-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3179
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:53:30.701582+00:00
-- url     : https://prove2.me/submissions/72af2d40-9ee7-4e0e-8749-38a6dd490b6b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 571582733 ≤ n < 571762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 571583983 1250 571582733 571582747
    0x1308070b070b0613090311101104031b08030301080705090c0a1403151801080d0206130303020d02090d050106030203240c1b0d030b2d0108061306030b0a0b03060106021002 75
    0x80c04d4110400821601034100f001d058189600400f018040580d80015961200f4848500d04c04803180f00d0010101424203101c00d00210f01c025403041c5040300000641d0141507140c484151864100741e01022440c0c3c040f517803d1007242805c0030300c5900085402245030a00840800c0a0220740d0742c6030120722005408000500b032203103404889000c1e01800313496908508103051000d90740000c240540d64042c440c0b05440000d00d44001b4645200b420840b9281701c00903800c0e035007280079501a6031403000482d02400101c0c5290303a8040c032561070911071340000a201d4a075105240c1002c3d214024983c90740c00400420004007240c8401650100140b00384540d10386000e409009540d0301501d083e00306114600c1000d038220380540c441d42030204d084070307642020324525401400e0150600c2480014409103c0c80f6506075020301c1c21726401050040c44214165151004038084400d1030b4016240401450f0510400d02e5172031252010030039081e00030f40b2a56040c0140030b5940c0c080010340c5010145e001404c9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 571585233 1250 571583983 571583989
    0xe01090f090e0c030f0a151e090309140a0527010b25030f030513020316090e030903070b0a030e070e01080c03070806070c0507090c03021308070b070b06 67
    0x90260030203414042003140c4901c02280104481c8440c0301071880f448038800814a800200c0340d07008413041004081d000055685c0445201ca104810341c40030303480f0000303100340c6009204c1c81c0d1070000706028002041181d074180200a01075540c44035059a035803200000706138541507149420798005075500d403103001c1118400c041c1142842c0601103a03070324080c00420070044640061114092801c3e40c164100e51409001d00d94414a101c01004620600c0c100009280aa0000d607800000604c45826001c1c4030b0f00401d06291804e00e08400d40395940400780410400351140074122028030000354140315010f40071a03a18a051b015075040440b004c18100c16291003500710382c0c24060342400b034503003150380c0700d0340032072000310078040c0207014080c0010000d0103082c00200f0b903023141d14140040215488561080d50128150201903403036010702000801c4a10042c080d900354006203a80c0103940c0c042207034440038815a240c0046070f00380c001d04020800010b4183c165054690000340300c3e03115486402c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 571586483 1250 571585233 571585247
    0xa080307030f1a150405130248100c110f0619020c160b0304020418170d0f0603050a0308010e010e0a05070905040f05060913080f0912060f0714030c0a0e01 68
    0x1c081e40c81000d80c00d001c1f25500d901c2d009400d001e070304040d83c0b22003548081c0c1106c1805d4140e0400281c8818203682e01065200c0c0e207440140d8080000095404180d143d000344c2e01911101c00b81000410304441560744444002c0044082c0420914050045400c0080e40e060305071076100546a2169000b00e0086544181880031822400a02c1600b012140d900e4030038014a801c22582613100b5403608005c442c250b564020a054141d43c0032025500d14040e105108030141c0001080441c1c0980d075000805524603a4415000954050001014103408a01d0003d08902050f00301200091048004101c0c581000382c031507030003006400300402c140d82ca100080b541141300c3c0d444280c1c01800d0275218281c10403d98407e50044006503000301c039940c0c0300c6c40c1c82071800c441c00500401c2510100486a41a41048050001c0c100300502c00b03400b074801d045c01c503403900b001600c40903905000726050104081d040758900d80c0104900075013600b103151001122004e0301844160074180708041443c020641e110b196 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 571587733 1250 571586483 571586489
    0x1305090705030d0f0f0e100f020c040e2b02060a09050307020607030809070501050c0d030203040c0e0717160f08191d070f0302300a080307030f1a1504 66
    0x70403258100c3e400000105150380959900001c2940341200c00a0a44a0705948580f810054049800c00018500840d0a1100c60703130f82d1b90031800344240f149800e581d2809400b80c0001401d0040203000400e0320841403034401c41c0140031102150200c2c00c01c066401142440d07001030b0305a400035404080303040c61400c510656500139404400022000205500a0000c5029a4071070f821582c4261701c440054510f0710420550b40e2060f4002c002a0000034820380082d5409440351511040c016550503c0c80041102595081d000c03d248510000344c0355040142140d0120018004210f04080e50074050b0400d00e105050701c00300030840000030b00d02e6600455852100f01c11a01c1000012071050035584004004010201c5902400000180d0801100700d442e041c0c980007007020842150000904500428001204180c0e4801003200c4102d9007040c0300e1401070900030b10f1402e60b2031030880e038028125420301c1200d000c007516100002580b01102c4280041200003644c24103a89401008810b015009a41c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 571588983 1250 571587733 571587739
    0x91c0501021e0d1b052a0102121b070b010317220f05040e060c07140f0c040e0109050c011206030204051009050115050a0c0204020c24070306051305090705 68
    0x85802c2c000d15520b90b00070b1046007800c8404029030459102c40c001103507540000300700003078414080c2e426800032071b0300c48090444802410340d144100308200705003a40c2245004661510740e010030000c8006545416401d1011402599440c0c24083da86109020506000c00790039880001680081c0c00c035204110ba10001404400b15800c071000403076009511858001c141c40034010600009086c01d1601808020b070f50100701500e4941e07a071403640700080e0040306007074609280340c081d844001301090120035504c076a6113010380108a07502c4284010785500040d9282c0f142e1514070240c012074804902c3e581b40c40001d02c1c01880d900c1802c410171001c1c0c11290001303503010f40b902084c408a074890f007000c2c1048420802080c07045a9a81171501502146000f50801040c4100f0190100c507201d6a00240010b100500050815000d13540705480c050810203846072294004019203070260801f8449603200d041460107000703490900c00070440d82e054540c981d940391601d070408070310b810206020001c043e246c09 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 571590233 1250 571588983 571589017
    0x4050118120311090607350403020d020622050f0111030304020f010e0a06020a02100e010c110a0b0301090903030f020910080c0c240708060a03020910080d020c0f06091c050102 77
    0x1d04041c0301c0d02d0300310f030041440c6e00302c07a01900c40308600748403018007d040f040e1400d034181460b5400340304499000040881e4415810450789100d8403d0001c49a031040c8042e4030348007814100750501182c00b402010f91414001e00706030004000900000300c0368001d40c16030707a0b02d201c1d03810b01005a8400f00383d8514140e10078080300b8003045c216400100e080c1460300071507031008018045003080d944140c3c142c1140b400103400081c00b03404616505151134031502c0c0942026142e590710b409402c3c085c1c000703030070000c1e9103600e84040e8814142e0501604c5c0030307002c600300218904058400010320020f181d02006040c05194000503203140f038a40305540c01d06000800f642c1c01142002554209405440b444090386409840801d0446100d00c016911480d0007400c0411800e096400b0400e00c00402841038543e0462800302040d01e441c144444540754145400074050080160304201042e5896491103024440500014009940b12020107400d00002c55111503540c0d464240140a841031007210413000c031f42 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 571591483 1250 571590233 571590247
    0x2601060b0a020105150913030210021b10060f050f13051323060708091903020d0201060602060606041a191e02030910030f060e010b03040501181203110906 68
    0xc85006000008540d40200000e0b07071182c540040f0020b00601d1150004007250001e1822000410018040760290045030800741c0402d904505a0748180c4401b80c03403091141c041c0090120030044207503400d600c1e1030309215241c10b2003000c00d01c00312030784070303030743c072961801c0207910040d00c81452220740404452000d100c603103402e0000d10082d00f03c81408480002050719030a4902070003250305d880307180c003140107805036444105048402c0381005e0600c1c3c40900540f00c01802d00100c24a4007032a441c445e07000390070450505507000c0d00311040c0d644918155041b201c00c00649695030000c480a440b003c1204005c44803405850b00391700e01a401c1c0300618100d5120301a15119081070700b1746400503201d59092001c40000d00c00301c1c0c0b01d00413401195003150b403115010300708030300035048a130f0f03400c280310000200280e4410340c1d102c4114080c2c1c4800450f07200003003031100f0f000080c00792040342212010134144038005540c42140741514518684101907070740201601d00f0030b54204540c15008014882c80d11050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 571592733 1250 571591483 571591499
    0xd12051314061f1a0a0512040311010f1a0d06060b04080a020f10081302131404021228050709050c0d050601030501120b0a020409020c100e0610260106 66
    0xc0c0070f0319048200b60303603601078001c0c041c000700c021803d0300e00d03001c42c0341e190340d50380c110340c202e6504000740400501c1000d101d1188a20f924182c0284614000d51b560682198000282421070300c0c7d15041100b44e50800303040141007a01d902050050030410786004004c07000909282e001414184c10154039503a0001d00014516400200301c081540212000c0c0050003d0404212503081c4448008000c0341030100040c2c1c500e1a210510300c00980090000d03070052040c000d001e01240e240c0150180042ca4040c180419418130780d000101091600700145105070000b400009040c1d404c80212220090030302001e07080110078458400142803080c1d0034003450800c01701c0046581c028082c441038032454500094035543c401e004041c100e6204803032907400442203840b0303160806001000c1c000d0f425020000011280414401003544003a005c010b040c002c2d4040380c0c10810780319920940001a8041d1060004888200c4104003c94080c100c10320010300504084130342c00600000c00b008e00394640403000036a40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 571593983 1250 571592733 571592743
    0x110f0d0801032108131b080307060e010b1c060204031a0105040f0c050307112a090703060e130203190302030301080d090b0703081e09011a030d12051314 67
    0x38030456443c5410601e541d881c403a40c01e007000c054000036481802241a4114515030201c20b2405075410f205d07081e14041c4103100b813100950003000036910008090b42804428802c4e142a00c141c4002031005481f203400040005040010109002c16540600010032000d641160000c40e40081c403030701030524400c404091390f2401d1085e503000324144410012060410b100da140d42d40001d1312100d045844803030084134010201030000c00700303214032000170307806041c001031050301a0110074201c801f00c80c201d0140036804c240601400d081c1418040d0501421040c040090f40c0300420813402c1034003114074000a40342044101818040d40c00030207601061543c080015030580d20720008685600f8454001201d0f80001031181d00050f0800f44940d00000e07210b410003681100145031050044400c1455030060560282d4814900d43c1d074540000d120b92125105140709402c3c00c03006042d50411080015007280500312030410416504c2c0700003001894480c0e008400c20360416805c913081080206040c0e035039 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 571595233 1250 571593983 571593989
    0x1617040b06040c031506051605030c0604030e0d110409171606150b0409020a02030c07080705010f0f080f0a021909091d03040e09071d060405010515040303110f0d0801 73
    0x160706000d10b20001901900032170307508075420500040f81c60b107008400c4400303800421202d900640b06019000111310300304094100d01c14490064003c50500345030240c0500100ea00c2c55004180000244c40404c01c1061500001c0318161004981da40c45840d02044e00380042d81c0b1000c60301d60114840c0d81c08a00a04403a000324410241000140c0170b0400003c0354103000c0c807900e0030401e01000280701c114074580241c409402d460045a041c229003030401c60a1000c1da400c0089150f012050810143d030740f048090300100e4050421401401c641000280900d00050010300443c0508010507501c20b29a4116260781c0d0342900340703100d0340070501c0c001089140c8510a4540f1a4140a191807060b0b04e020002000145040d00441c98240342203220909a00000d28000701402030680c0080c044142d14030f00d5945c01803003d90030480e440c0801c1000b0440d501a0455406443e080003840100a0520203d80c156501403c2ca100442040616189070442400701540f03207014803030070ba0348607540144040307040e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 571596483 1250 571595233 571595239
    0x3040b010e060303040902090d1a0f0a0513020d03020a0b1018050c03060907030b09010303081e040c050f04060b121b030f01090c12050709090614091617040b06 70
    0x1603666140300c07446a01c041659020b9150300100020848100039500401550700081c01d4440343e003a007512807011020503e4580d440340d4408104200d4141029459143d001054000402c524185400c03200b04a80f40510024010f100d20202c075014180200420004a54408a40101ca2074216004038a05641d44116900d41007040584140210b032801503078400d00004c0c40c910700b59a5603001f082035500e0003602c1a410f1550300c109404058840b0460306002c0d50103030b1100074850410b038000b501103a000703014500c070100144092000003000400d141081702d0044542c00144003851002400800c442e50000224000001d90080e492115064a5105840c041e221100456184c82e454034184411070704184c04080c1c0100510003083c1c1c41d44040c100c81020301c1e0208a59106462a00071581c0690703030000170a140c2403080100325034601814001e01b0350200d580e440d02c074101c2c022804642002e0040c070f8440c4003150001c9891441000e100c8178252481c400601c2ca8201410602d1f090b02c001d40321140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 571597733 1250 571596483 571596503
    0x1f06030b1008150904020a080106030f12020a0b0c2101090b030606030a1e032c0a06020d0c0b180d05070302010c0305060f0d02030309040f0605091015052d0304 70
    0x80490003499083d10810058002c000c0d80780707041082150f04500100100d13400a00303d00040703020300007403041d40090340c400c0410710542200e40c18580c164440c203403001340c110f40c00403005000103442412903035044001032901c1034480c01c42c8480800748401c3c0b4018450750110340800000e005c2541e411142c2c41d03d4060301a21040e40300c2c003041c15100e44040001521114508083d1300e4500310041514002c10f0007450141e01d100004c40e0240c20002c13200c2c50301a041c100c07007400e5080502e0000110b00042c8154002021a901c805030040c0030b02c2c1085070040c041c0a060301c0000c02401010060241c4400c49509034b89001c0000340b00a00640c0004400350019840d20780d0003440c00303001e481000e00880c1c000f801c402e40202031f03c4c00c00c1016628007500f01d806001c103200074141a1030358080da00f104034500d10f0101c1ca040c1840180a08500c000f409015842ca24410070405a00b80030076101c901d03103c80c41c240340d4071400c440c0d07881403100d600240c29882c0d020529075031070000124406103028030700c1200c440d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 571598983 1250 571597733 571597759
    0x7020f01090f2306070e01260f060301020309100b030c060406170105030105060d0f060902060d091e021f14040306021b1218040b1002010501080d0314010e1f06030b 72
    0xd024501090f111141540b0030408680898001e0702000042c4205150842d43c0001e030070030340c1d13040282400d004a81d651881050041e001e10303850790346070722210580003141185030281c5c00e265600c0f080f0821103042c1e907441c41c15007501c0c2c505010b90345c1c5015000d04203d9940343e541e040240100902c0301da07020a01244070001c03c140c40d041c09424040c550003015000a410700341c0f900c1d558501004400c95038907640e80f09030300058444d0405000943c2010500240344105030400140c55810444045a0000000d2200006035101000e00d0650f40140444155101e4910815540c2c80f09038048400380020109002080200940040c18940114480303d401c45540300d03201590b501c081c440034551040b0902040071551400d0448124580740100b0204003030380220042544d164a20812200503511080140814042004407050b0581c49203030401008104e445411690702d0180200e29209051401050050382002c0c01d466040815154201c106030740ca41e0040d000300507a1441c1130058081d10491 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 571600233 1250 571598983 571599023
    0xc090112090f02040c02340e1e04080d020c060103061b1d03030d020403110405070c05030a050d0b091303090f08062a070507030312050106050d0507020f01090f 70
    0x10010982c0d100892070b540003850360800c0040d00c0d43c0c42c034880842c415001a415082c01003000e034803000d002c1c00e854000425242ea40c0c0105044181c0020195244204c00d100c6204550000342d1110310042002020b162250700d48190144500078801001d41d0000c1108000c4000c0402c030181201e200f04000c01c40c0d1441c0220800c00144c90038074080c082014071404480a052082da1400c983c0d00003001e5910b040ca1051001c0700f01e8200d50403d5503003d10b400080400da091510819801c4011070a28029064559640f9992840380c0341e900c2c02001000300300175910b90826080182e41100061111980d03241a00c02c1d6240e500280c0340950008010180000e8880010b84164068480c003201402c4195a540b440c4103012010050088000c0340042c0040103003000100904002c0d0304c548042c104080c9541802020b040002c02e40004c001d1400d80100100c40e0080115007150406020200d41a03903034110586c20100e10300400702c200d500749103041c3d00700b01030848134040300c6200342034200041c221000c3c9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 571601483 1250 571600233 571600241
    0x9050a0614010f0c030e0a03060e0c01030213090c02010605060301140307051e0f0d0501020a180801020f040e2e06031d070302190f0e071b110409050106030602030c090112 75
    0x700c2804100000541100c8912400031000403d0103400c20070070500d04500410b20b404055401030f20f41559402080898000910031f040c0880c109103402e508025040691400582d01d520071203d481c1d43d500c50f20b68245000703401c120f00421006020310346039079485164000500803038051600c20f0041202c00704891030700c80d00c42d4011082c10b00344013101840b40000c0c812021230f103450165102e00c14130045000910f00740001d0256081c41e940c0c0c01c0311381c50b833012607003601d142c035401c00c91942e4010300c082c04022034140103071012100701c030b1660181a11000c1640307480032000e100384100c46503c2007804d81020030501c103010031240326076406c01200c210340c0210704100b01c0d440340d1440d407500284010005407500740d1b00010b545d641d0301c0000301d0349a51120415101e0442d644162107a511030301c100900a9081110440144509807090000170629a900c00408000c42e50051080c4c0d1344c5c0c0b41c4103003401025402400503603030240f41156030303050980b0b1845290304a9482c3c1360000301d0180d200e50710b030059030207 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 571602733 1250 571601483 571601519
    0x807050f120405040216062f2b0e0a061a04140106030c02030d020c07182d0b060c070509010b0f0412030c20010306080f0601150309080409050a06 64
    0x91502c0c01c0500384030800c40a0b5020491070300b01d0004803e050b0700814503600c80d400b80d0101e241c40c800c1803e03207591102200c52155400d0310706401028001000004400203030305d40c3c008050529401d000a4400c00040200884440c0360850310031a4091000c000517940708000b01100e90a48800c22219802048199224038000c4000034145c14010041540030750012031861425005903820190008580301c12600034040d4502c440e8840e080030803020403150500d17507107021050814020301c4e043c40c0c03015401105400d940703031804810041031b00d0060016805502c03c4100188201d07038401646040035554082401290700c107001d400000035040d00038000321284040001c1a0700d0174149418180f04008241100a4041c01420801c0e070b03002440480451100c10300c206c900c41285816240010100d500e02d4124080c590b100c1011260041030009902d17044800c00d40e84200e1071000c2102c00c0307000d82800f80c0e0041840310301217004102d84820303403c198803407285550b080044070b84c0d07000380b401c2e408902d807 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 571603983 1250 571602733 571602763
    0xc05010b0d03050913090f060b1003020f07120908241302030a0b070504030c0e1501110712080c010608071e0b07020d051227040606020c22090807050f 66
    0x1c41131003800c04802040181c3d4402c10009469078868866407445458000220b6200e83d0b142d201d03220500d088034805800f259185421418409601c903207001902c54a031000d041c05801500c1000310034070424000001d0310040b403d07500e9164103035032141601e03a5100c190010400601d000a003100030000c90314200c8d00c0e0000e005102060840e150007250348000b40c0680100b1004100101c0403d027042ea0000040010f407042015038504048200c032501c055070301746030400200c25001469100b001500009a814880c4402d11f1050140307441440f920444401e482c032542090000100c441c004034034102100c414020100e010403940c0d418910906441c062180f03131040c02d0181502508000c010f112070075121714121200c91050b13100580850300660048000a038803200c54400384801201c1080300c80b07005039418084642000c5000e03481d0800c010085000d408405c4081d1203440303000202212001c1c007010100060700c4c00d418000d1841e4803030082074807144500841c00380380043c0001c0c8400d50f102c0c10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 571605233 1250 571603983 571603987
    0x100203131d010303050d0b100f020d110606040e0c09040318060503011d0702030c07080102030a0b0307081e0a0c0608061e090118020418090b090d050f03060a150c05010b0d0305 77
    0x3d40e50682d1240c01016000c541142e44283c55101a15003c1110300703915600c1c0c403040c00c80802c2c60030081c94043c40e001c2c0c0108100c030605080d144107000098081e00250110b501203103040099411500e84000e03c4842940004813506000506170406000f10000c0d04240340845d07803e444d80400e540d248000e00c100005481f41c201c0180d440d0000d6211a07070484d47d1407065a140c85003501109180140302c0e040603036565400014030100c269a440780020006058020304103243c075000700c1c1521100b104940f4548502c890002c103044140a0000c2420203500030220000301e0349410005012202c121034032405115035020300c1030f5544150030b0181c10901c0080c409550380c1e003044440c0d6a450089001449401e4081c000410b0007140380015440e0380340540340008858046081c2440d0340c20300684483d050750403040100da10154004126014030a1112a21fa940d40700e49022441c000040c0c0c1c45411711812450b4000c040d00d03440745007407a019001d10006d000c0c94064108010050001c484024041001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 571606483 1250 571605233 571605239
    0x30f060910090c050d050a050a1b08010e04030c0b07020304030308060a030f030c061d03271005070809101e0f0207050d060605040e100f0b1507020a05100203131d01 72
    0x2d107400010f0090424a03240e030508211038140001d96000366490402d150b00c46042100c20701851185407011004a01c1d561140c1070003102c00303400400107000b007400400c04000000c0601d802800e09480e41c5034441e07150280b40ca82203800a441ea04140801ca002658035000f14506107044158003081c2d9410000c02e2811110b50358043c3e83c8100d00f481c089508a4454880070081c00d202d10180395101d0b0120042c1d503a07103c44444462442d80700803000008242c0200c4041c3e207940714a40100c8840f031960910503950085414005128000c4102c190390001242640e03480059104841013451580c14080101190144400381c4502e1070784540180185c0c0038041c104a5442c00c0348070544a680106c8001400d0354941001c10103644c1c1e80c00e8030703008a070301c0310000c0b04280c50300d4842e05890080c1c0003020051070b2017001c00282c3c10700c401c60750000054804075010003555203000c9100c00902d8001c081216001d6441800394590b0801d00300e540c03440d4410b074400602178014148008100ca8180340c8a4001e0382 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 571607733 1250 571606483 571606499
    0x228060504150f0c020a080c03060a0606080105010c0602040513020a0e0a0806220b0106090f151d0126160c0b040b04030207030804030318090c0903120e06040902030f060910 76
    0x408010703e40c0402404420440c00341c0c84207280c902c00341c51107502402d1034100038828580781178805000390862524281040050560051201e41952401d1a10703c950b4401400c0c000302034041c81c4c212980c869645284170868017080d9004058400f10741d1101554251008100b0824220b40d10a1003500d0b000b0340c0000340040a092190200d103107040b011000054015121440c01040903008035020422480041c0011645d03c2c508100600c0240705002c4192111080101040c1d07038040000b020100f00c5004450582c002c928100402c96400790a030b103c82d00d10640780c0398140050f2810025070b4070078071080305103a210b8001000501e40180c00c00c61a6103d5599140c050300c0010000e40440c0140500880010140380c0188002d500aa8485008a285040c0b50815660310792107054050300d4034521081035604082441c04880d0004030701e00040d6101d042c10f4031141e5071b004d00c469126070009004200300340d2580c041d601400b001e0035405100d584203000e03c940a041030724008a00c0c1e40340e500c1000244 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 571608983 1250 571607733 571607747
    0x10219210504060c080f10030f030c120309030e0303070305030c0309070b040e0f07030b0d0b0c09060d02071419060f0b0603040605060117011203050c0703022806050415 74
    0x12400500e550400803049418208840054404031400381d103403049014015400100f9507040b81100026480c1c900708241c000190001c2d80c0701c024100d8821901d68404d01d401404852001900311409505810600c030005008240700d480840101e400c0220018a500b070001c1522102c9074541c03910340c55038960307923071075803841e0401403910020380715210001c909452810040d100900840c0a10410740c241503c850440840007070140e010145001080e07241d55889030a61500183c1110f542c023900c0d01c807080380c01c605100700c4601c260004030006001c0b01c094484da0081100d68000c800d07507011131240154503a1101c04541001c29150503080c2644046183c66010700585400802c0010b41c044e64030010840740e81003103509803600ca40c1c400820456580006c0f40000540b840b100380081d0b903041c410b841130003500d0b5900c041d003008404220380c0d0b0641820007855014680040c4116000b054007206495100c1450030b4074416005008000180d10b405501910300351680400031404806605008a03010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 571610233 1250 571608983 571609007
    0x411181b0912010c020313050402090904020f01030609110901114306090312020c03031602010c1b260705060a020307140303071103030c040e040807050f0c010f02010219 74
    0x44030b412001e1424181c01d11400000b030055401868451062400900c40031920b035125078059030041240c030100b5950082001e91180d4112880074241056a0048000300110340107080c1d01e0f840e1640e0041c03044035000141000a07000d0b60354141d1a40c6e4000119201d4a1003486000c080302003110003010f40c0f800110903178030368040034107580f50000070340003141c0014a103521003404200917200510500c08d01c09290017404016000400c101a0601c020035524400e00050b90b0308082500e40400c21a03219a56500344944c024025103d00500e00008024801051003040c5101d110400683c0c40c0c0494504071207000750403040580a030510300001d01501e5801141e110301140402c0000c107000a42c0740320103400c85140ca0b001991030b40b51000c1d01800d00180800b149015900070b10422201881400440707045c3c1e05942401c0740c2e039803200c0c40d1101850140a00040150045460403440c840d0002881c102c00f1b0026680d01001110704102603080f4448c2d80c40c180d44607900b00380c02e840402c0c0076054202c80 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 571611483 1250 571610233 571610239
    0x1050117160320130c1e05030403080103140309031f0c090e01090f0605060a1d061e09040603050316020f0904020607060c110d020102040f050105121506070602030411181b09 76
    0xd02980c441340d008841000d042200402c04c40418141400310040c00315422840c282000e03407850500b0f45001c1c01c8039005210080150b4560b07920691511700a2043e24458440602121241000e001d1074015949852180402040c0362000100310580715210030800c40d181c14118001e182d081441c01c0d03018060618030700000c6902d1760000900d80d2124401482203205640da02980e00c2d100d484a649000c12138150103102d4402440a0440140c2580b03000e6080c0c0c0c420164180e56100c1da102203409001c00e0341c0007500a0001203240300424551503218251144200c070507444040b11b0400300012248141e502035000b00c1d09004000000e000c030340c401241c40d0600d00b044e1641c4d031410b18000f4075003640c0c03008410044c2d4001c2b03810020b814651241801819003401c205003098940b0703030407640d0b0440092100403200c0c0b09210903150354036080100c2d00240c0e0812400d543ea850107040405503d201c1e030340201c0c0100034105d00d0007649040c0f031419138040e0012034101010040300e1800e46105400018846034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 571612733 1250 571611483 571611499
    0x60902010507380c0f07060905070303050c0d2d02070f0909030801170c01050706020702130e060f0c090f0102102301081b100e0301050117160320 64
    0x101042c91007046890a64a002d0301002a01200140382c40c145040e600c44101464010f09000e8040283e030b00369514000d0544100d500d841c03007420008080d00307103107002600c01d00500c01d0100601d0360140c018007581803400111010401c040388100c802c0c2c0f4240702c0c0100d240c00180d0000e2028600c94508120b0b0b01d40c40c1c030403502031580340c2c19129919003940d404100407540d10001442016002034000b401401003285d0705c6c0d0400c04810074103032210b008118180c100000003070807100700045941920710641d00076241004100320100180000d0034100505a030520071080000d041c52880c403a003500c14504081020301f810060024080d8206e555101c103815805030b655080c0c0d041e000f905c1152a214400740110b4500050401140c9100d0b106800c80200b41d08802c100914512444650154000302558480940d90410504581c00f420108039140d040d42068000a01c0c0c0c1c00404681c0310000c290810384d58000088082c00380d07a1002848020403540c41c0040b2466514046403500041d124040c090300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 571613983 1250 571612733 571612747
    0x70f05010e0d1b09051006030b030d0f210b120d1e0c02030109080a0e010908070e07050c010e2109091602150f070e0108010605031b0d020d1d06060d0609020105 70
    0x400c0c0e09080350080c0ca1300d1380d42c5404001a800351a40e080f4010700302e9080c00c0041d46032010200c3d8481c07034000140828056102d04015a40340306a5020080b40c003a03482408810389040006c0c009820006070480c810509401c10001c4110042501a440061511071a141c1c03400161808629480c80007110b0034401c003285000096102805001c1015114800b603d070b9856150320003411018902d14014100311303034030400384241840001c886003956500d040403526980c40c0d0004880d544161180080c255080c0b0300d0a00040c1d000095050f81301304c8410030f01349003c0d00141154854010301c00c2d250f9100f000c1c01e0118664031940d8100c03040b100080e10665081039070ba2003014031195419101400c1c5614034901708200341d86c3c000800e00300d0b00c4091800c80001d5140080007810340c000581013a14000411403070341f004041050440320a90031b68681036450b036102c2182d480c010510340956032215900940007601d01d100c0840d0940c49000000e05501c02c40e040f40e00d52000400b03032810103e0600004011107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 571615233 1250 571613983 571614023
    0x40b0418030c1703010b0304030c050118140106060f0207091509110706050a0b0a350d03050a090b07081e04060e0f07050a060c0309091a03070f05010e0d 67
    0x300d00424029200c0c0c1852003000d2611500c2400c002c980c1d009404000d00c0188603071a403103003c030781c0c0140c1c02d0b1400e80d00705001400c1842c0101182d04180d580098104445000c02004005072031840050200030001a40e542c5e60076503401c0840c44640c0b00603004030314207210a00c070715409161723040d10200ca0303584d28039160001041126000400c41100b4000800c006081100714016039038880111a024020f400c0d100c2c011588074901c1d4020684e0812290040c00d1905d500e98001c50041d1700d049481c00c0d0b120310040b04075a15182e41500000009051800045806032030b400390503d01a0b21403420103050303480003000c65400c0710203001806650884403410005003200103c00303001d02d002e0b0400040201d96038010f149000065030f1040480e400140b020070140d82c43c00585800c4607024142170980711410324048405c011944c102e034003d28640305500c8020030451407407001080060703080341c5001d51107082e0b9405500071032240600269110100300707090700700140502c00c410b10800102c3c04d41d07807092142c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 571616483 1250 571615233 571615271
    0x1507120626060714030a050403050d0f021b0705030a17072a090509150604090203030c010b101112090a0b030a050a0b04062102360705040501080402040b04 68
    0x420801d85040101121042003800301035008885802c2c0484055241c102c5208513000080100310000d81d1440002c043c14014800c5035001380360740c072080190350300d14881e410094014885824550700f862002d8048a03800103584030035101c0060040c12960030319a40d508000c1402030803500c90303610034000c00d000a0540c81c50146030030210980080192442c810601440f05141d00c400f845508004c184500558041808401509020407420880d601c1902140c040d04180d10029003500c0f00050381081d88006611000100704110740005a00c034400400301e50040402584200f50342081900d07103082d10034600208580ca4010701081e04690b070301c0e515140203400c112035010a40e5100c00410545a070140710306e9180010442d020402c1c1401d2404d111085031020000d020440b011012200c29541c1786442c41c2684031400021014190002c5100d00414602040500400120101194540e4010000d503070035954182d5965550740d460340c0170030018040c0c0c882082d030840d540d03040190b00000e41b480703 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 571617733 1250 571616483 571616519
    0x5250b041e03120c23030a15031e0804050a0b030603060c07020603220605040302100507050a09090b0402091914011707050d0617070f0b0307170912072315071206 71
    0x44007901e03807500501e40350544613010004031440310145828800a4040002b940000c5841c042d0380c981d01d00c1c2807806c20314030f20440e00200c0d40025812400640741107041c000314030403681541034500903202d246010304e4900410100960040b41400010081c04141c2d0901c40030000301d07030104c1c1400c0060b031102c90440d1001d840507801a0013004c52124000120301032035030014040c0c5841d601d400d01c41e1100600c0c40d003090040c034407003d40350625501c1c00e85d11601926000880140f0f00300140074031b007211000a290302d103c1c1144000b060500704d1010342c02745400040401b04c01510385015501d040c0e04854030ba0110100340075050303882d20003003021030541c2c840e0850580050010101c46003042d080d02184000d03640043c104050803c1040601a400754031a84c0d50007400302c0c0b034500d03601d840314454100a1801224400800b000c6034150901981c401611048091b110700c6014131000c84980548901000c080b070041c0300000000f080c02c00d840303003c109110121902000031980c2e200c410b001c0c0180c03403501c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 571618983 1250 571617733 571617797
    0x2010f090606051f02100b01050f121906050d0f030507140607090f031106371b02100e0f09041a1006080705250b041e03120c 55
    0x24070144c2041242c060321601a00c3c0744083d80c0002c2c030002565070842030400342590f501c4088800c1c071a40030301d042d0f564800c0750a5045440300c40840380070200079004c545100080e00e01c4070000c110303219548511829504042d2085109100a03200c007140111840002c40800c074041244d038004c50988892a8524000100504018206408014100c1c442604102c5c41944c160b0360410021300300c0d40d502c100c0740b14151202034072010603025050001c0b1100a50241c0d4410b14200d81c45944241070101d000500c2e2900d4803d0820013054200308143c40c003000094200c0100810698200d0161100c450005d10042a00011800131004186c6010041e6401c8a480740c250060b080c140700c00e8034156500003030a401c0c4a01a0f4a0108010b11403c2c016008100b4030200040c504100b114400e142e018413500414010703244446442d041c1e10801084905a60100100b5140085900190081410250540d490100107100216100c0081511b41c82c04010711a80c2d4005843c592620441307021114540 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 571620233 1250 571618983 571618991
    0x305160b1f06020c01020c1002150a0c0f0302071a0a0b040905100e0a0507030813270c0513090218031e19020a0b0c0f010510030507050405101502010f0906 68
    0x100007060407158000105542140a511409917800904e91341407010480b400318901040100c00d07800c1c44c05100d403210307148400c4410807000703504c550020541c030009540c4944196240c0c4008404901070090014203410840001030a0803032841b001c281c00024000c0005044400700d0000b074200e5099038000c8403660001178509825103d28400c07800d8403c5070b4006807030324064070782e1641e80381c14160000074101040401c4c810200e25001d80350601901c0446100c0c0c6500c80c1c180c81c0b50364400f80e0300800501503130804222810091154003500e5404038803480c00a9840e050a09910103034006640015514004075190236256804100702d5511441700d000c04000643e400444074148502460047c440e10100080e01005890300c404040c205d40d1942c100365201c6100685013410526040d0304040745600b410284000700e4010b507003460489100d18200c6040d140d03100140b0081c1d030002c43d40d04d0342a017002c110801c40c0d0101c90000c0c100c41020303480001420070f0340d42440400c5036003014041c7c8000b50380d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 571621483 1250 571620233 571620271
    0xc0610060c06390e0a0515070302030c06041406070c0b130303021309061a070f020f18010816081f0b010c050102040b0d0e0604020f040c0e0603040b04050c06030408070305160b 77
    0x200191356a09402e42e458035074a401c0c10b0100751901503510341907860036400140340c82811f10900640d00c8980b1103500303072411420a030521241c00c01c0c800f104401c0b14002d51000ca84003d0049808003003803503100d155083c05548a0301c4240038412951020f8042c15003c0008146030800d0032815009000b030b40c171000421070b04000c4140c5140e00302600405400341c04105200105082d0180c00501e50f0b812075a840c0c0b00394050020640d4042c0881003c40400d480c8d00000c01c60580100e0150764a12611514034041a500d1080c01c4c0d03541c41c60091844c00782e4242e00780402200003508050701d0b00c001818847d401ca00c1c50303964070342264070070b921520034014081441039504115005010702c030b250078001003040d820581c00107005401c078440d501c3d00c07503983c40b1a00c03100c45003d41c605000401004110588903d81802c00c1202040100d804440b180140a1604540e182c0304c02074038007a607005101c17a801c04065030303419526603120686440600c1030002c0001d002036001c1c0d4a851241c0380740e212800300082c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 571622733 1250 571621483 571621487
    0xf16060905060a0905040b1203070b0130020f12030d0902030709060308030a0b030c03070305031b070305070b07050705101d101218060903050c0610060c0639 69
    0x80d150304114441c100401c101500e07954042c0030383c0e0581c0d00846001400d2910100047e03281102c0f841102410301002c510f034814003011500090407a420076a155010740d0245a4900c0a0070007680200012041920a9005820150f510315140d81d80078052010303d00c0f000510628580203036046542c0c55440c0c1c1e00410840c20280030003030080943c09402d000c5a030279595505154000284031444003640c0d610004034665081006085005024080e50941612401e01c035071254090300c424410824079200d00c6820400003d0180c0c00c81b13070071070301501c1c000382820240020783d4052071080d1450321807050045115903070011200e01c0703000c0c80c0d203c0c2040041d512000f81d85a20310303501c6482c0f1908030407408180c40c80d04443c0d40200d10161523000100d010b0030b0404c1000005c258000641018074286003481010b801030000c2804104580844101d0780d5401103400300c1140d5400384000050100b120b010002d01c007501300c1c0182c1c0c0703081e0208080350b48d00102e00159010704a0a4060700503081000520426 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 571623983 1250 571622733 571622747
    0x5091005010e01081908030c0702010e060409060f0b0a0f1409030601150f1701120f0803040c031a0c07022b051b09010803070803060d080c07060813230f1606 69
    0x191603211804e90845c00d43c88400b11800006d00106008800068440031a1300c1254201443c1000501c1c0700e48a6485030b2411b8010001401841441e150700f000100d030b10080101520506078481d41c0d03031070540d401240102da114658900c0c0002a20007402000c240e6034041c846140a044d010040440c00c2103107a0004210003403012401d820701c0b2620307600c0c04603803000c0316001c0d064640402014240000d18500040d104082100c05460900048113020411014500201c12240100040300c502400c08068240e42c4e1f030155500c030038812081001130018200303020000c034000400c64160882800f82c0001034612200030304100c9213a04030903020034442941c0a0b00107131480702035503000d001d50b04086d4607030b56910400714094400d04001c0002080d5540d841ca8130aa000d51204220303880d40c1c45d4205042d03039841c2c0c60041b031002c17900100000d03400f031070781c140b21000707094015a2854603c0030b802c20201094500c00d0944c01e482c01807003c8404000d8082040d10f100e9104002e50108d03041c0b03802d00c01840c00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 571625233 1250 571623983 571624003
    0x5030703050a020a0c02091315060303172208090618090a06050f120f1f0609050c161e05101401030c09050a060510020a03020c2205091005010e0108 65
    0x5881800300600c5150312080c8545d030f2542c180c2d01d101203a241c600c0030190012000ea001003c49968a81800c0d956034681c00c148122032291301d80d98420328140c1039169105900715100003070324200d00c83c0c00700c98501c2c54444500c4140215400340c47d041520002c5025130b4050f002d40c200b14000880540c815081040d900c7d80c3c000b54122042207441c0c24000000c404d200f05200349885010020b40c911b44100742448904145a03140c0c0880710718561000208252080304030841107402d191100000700758000307000762445055a031108601e001300003403181e441c40744400c50989504000001d50f180011040001241e40c1d4082d20041002802c00c01a0000b40d40301080300180c9170340b0080c01000045c003204165001e807100d60101040665a400019000b00991313030203640e021580d89401c82c01300d40c022540300402030281c0d09039040809400c09008030103c01c558403222804030b600c20a0444441c903440180c00c08464001e65142c46140c1d0f201c01d042d55401c0e001443c20002e244e004020b0598108442c1000b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 571626483 1250 571625233 571625251
    0x309120f091e14120a0b090615010912170301090204030204061d04031d10051b0d05091504050402120f01170d0c05030c060a020a030c170a020f070c060503070305 71
    0x816401050025010050748180c200002e00c00802d883c0680d94080745940d54140785040b2034030403003503040c0f4842e141000d403883c8659018000100d88842141c5042200031041a110314025a151031407002040031040016140c401103030000c0b682c407152940040d8024021034001584560560040000326002c950040c039001d00215000d4585149a401c3d01d54041d4040c00c100d0043d61580b04500703091128508910b500541c1000c01c000129000b01c0a4040c01c0d40f41024001c20030160700c1316035650f03030f0703d180310310701240050000000501d00041e1201060114181e50340c00c04d9134910114003a0b8003c03004551907002038504000101d05822207039801082510328400417001c1010980707480d184070303400300f808001890b86003000340801001283d80c0c100da94002c4919516201d00683c0094100a0920002038104912510f456216044a0307a11018100b811700658407002c030f04500a47c042c4400e52803181c01801000085001010101c009000307a80f034466603454101802401c4580c000d00140e6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 571627733 1250 571626483 571626509
    0x1317070501050726120118050f06010210020a050f0f0409051b03130201170a06170c130b0f030a0f03020105010911070f02060f0a09080c010503010e13030309120f09 72
    0x1000c01c08610b0b00c1c040f480a05001340b214010701d8600120340b40314850002c08002800c1c000013500c1c501580603113281d414841001c01c141c0d100e03105002c558801c00e4980b5130041c1c2c082c0608109142d5568002d0003001c806003046460004540d10400741c94001d000020b10ad1140841c040140c011240500d55000c440010f01c004480d605256180c841d0001030080001400765060020071a40120582e92221007051521074003441e092800c0c4002d00b0301d0b401900203502c0c081c0c03034200c103040340000c0105c4410801000044141480705083d4014410703104990fa210003540b0590703605440030311401021601400c1c0d17440d4103c845040c041c1c292041a405003521510b8140c801450703251510556104a074406c01c2981e001d19540005100c1c0c0c0500c10300c0d401643d4002034040c1d031981d00110340c001114000002d451444004100555440c0824414006a5021140054030002c010440031107202d100b030074006401e222903160742115070110350192000c941001000c66006802c511110020a20204409 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 571628983 1250 571627733 571627747
    0x31905071a010f17103801050904051b04122d06091a01090b041409070e04031202041403011a0f010c0c0e090d0f0507050a080a05131707050105 63
    0xe41c03800154850820f421480e20243c140c0c100040c40450729017121180c0901c40b83c5031800c1620240074280140440c060701d9450348072a8003060030311001800340f0503100c3c81c0c2400d0809090002071701d00200641044541e2105046019000c100907001030001d03040060707179441c041e1806200003c0c00100b803000c0d80090b030604110032203000ca030600c040365100300c011441441c1481e001c40004001c0034041d0000301c600002092140300343c5d01c500542d100840301804820010725070300280c1d4105481d041c10a03041103005010720100c60307090b81d0304140700e490030100c0519000d01541c12070300140c11824100a491428140c07500e001d0084da904800c0008240015800ca0380c001420307076044e56041e50500c180080010140314072155084000c1c0f141052006682c901529032503151040e40000802081d10000d44032541407107402a200c000c2d9000f0001d111140c83c1d5120008141c104840c5031080000c1040031000c0c00300c2c16070340c0d10014105c030b0f1348909040381f050600a0402d5010f0300b005040000500a072 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 571630233 1250 571628983 571628999
    0x6030905071707060c03020f0d020c03010f0504020d12020708011103180c0d0b1b0c0a0203010507091211040f02120f24090a0902100203030a050f01060f080603031905071a01 76
    0x50320440c0d0045c10150310300074140c034081e41070180b0072010300182d02410301440851600800d079600407042c110000c00c0381c4600081d06800302c60381900c019402c40c401e00d455800083c2c802c2c401c2c8000030001d004540c812a9504400c07400d4644c80c21412002c3c0c000481440b40c1614100c1075800301041c010094400c440300c00000c1000c034514004044c00c0f1920041c041207207818000c405070000d40400d00215651180c1080303546d41d4443d6100f04074080d61800000031100c038403c2e2960400e64a802281d031610342c90603100c0e4454002100c01465009644500006c202030151009008a0f60320b141e2401c624540f03810350070580311000308940ca003c0c5c2107420002c5074890015840c40c1d00403048410400c0368907515840c100400f001d00c0001c4d0000711007041131030b4458000010b03500c6044164004e20442d0384d83c0c08000c5a155081c4902d0001c13480841450003010f0081d0200ca034801030203000c4a050105030b29a950180f080c4540520108500043c00d80502540410007525810800c07221101949031000b5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 571631483 1250 571630233 571630243
    0x12c0703051b040b0603060117100506040306020403140307020a1e0b1c0e010b01020309042c030d0b01090f060e130606051b0a11090a02041a030106170603121b010501060309050717 79
    0x41e0656081800d0000b03003041c0e580303180c800050400334080588494482ca0b20030000d43c8076000546614008401007104480c00004803160550b0103001082c54916001c3c21594007031001024082518807641e0120f12440e9035400347c40d600d0400d0b40c0c000c4080b8116819101203907a0549482030b42e9042000340b030681d903000000c5960050040c0c400065166204100903070180c080c0b44e00140103075a5912640b034180340000035244805000008120001c1c000c0019203144a82d4880d001c600d100f020400c02c821802030240807001000640480100050740b00c2d4030003200c0721500301c0310204902003030064900401c0541501c8a13006140284000400c1e47c0f40d100b03201000313001140c851018240014190210b03034064400400c03004a051880701c00c1d40901d00e4140c5c0013405600000703410038004503c10b1034040e103104e02890703014018007010f005040500540c0d078000d06d01440c1c1300c61804000160b20800f4482c182c000c0000d5503000501000c645041d03800c10200c1d9200b107103240e000245901c801075012038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 571632733 1250 571631483 571631507
    0x30e0610050d11030f28030f030f02190216050a0b030c0a20010519050415050907030b0109150f0b0f1303061a030609012c0703051b040b06030601 64
    0x541c1c10008012450000901243d800180d9050b006891002250f00e0740040c00030b14044802c80c55040f680b01451036020744d41010f02c400b41c00a2600008040e887d4000e81c05403440304040c6a001d4502103000007020000101001c0d01001a07005818829400882d06400030180074115469403455181007040c0d4101c0c000a001426050301c0000c00301e0040d8000c1c030120b114081d080c3c004158800018035054000e1000700d0385034050640c4d040303204c0219440c0c0e1184030701c181d610407078401c04103040303442d400014840100034043d144584440880403c040b405118000c06c200c660124034505102d84041c1740c50050707843f00300c0342401e205050200701a2001a40c40181c0441916511200c031244e0610410107240d0010344050b16204c80b110106044031040844910181d08540b05a01c8102070705088072110b1003d210050010401e102440707841c4034103458110104002c448d2440d03102d0311410b0078415403040300011402e072081d2031131960a141c000c44540f500c04603480c034207615101c4000303020108495 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 571633983 1250 571632733 571632739
    0x708011107200402160c05040615020303131103100608010c0f091401030b0402041205010b0109051804210503040507050604050904020d140607030209120604020105071709031c030e061005 82
    0x120291192030f1681550603151001500408001441c1880340200500e402500d0103181042008500c19010741040c68803040301d47d00540c07465892040315800100c84044c2140d184003510742c0740b60700303039010010180c085005481c002585490b09641c01d00315001a010407083c010082e00a0460301c0e04004110100ea211b0060220050351604c0100e0080c0340c021034081c0c4c850b2002c240440d101d02070182041c92203110368001c1005001c41c00054136001e000b4800c2942c498420023034645400e0607a41a1074000d1302c501407007000800c0000c0702d03046200d20034a442c00014004803c000030b02c4010050703403004100660780d171443e040c02d080210300500d50040000e8020120402c94104201d01015150000c0801c40e0a4031401d060040d4018080e43c0400f2030244070b50200c01101c41c3c80030703000ca1024050b56050316450728003c41c1d85e8a41024984035002e041e005142444201081d4a0903c14a011100d0f182c075080c10155001402408a030302e070008540c0c8992003e410080280c211200d05405c1e81c1040f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 571635233 1250 571633983 571634033
    0xf03030512130c03200108150d0f050a032105011503021b01110409140f0a0507090f08070603060801020c060a0e030f0d0f060e130b0414030c0708011107 67
    0x2920001505594001c0c0c028054001440d000040c484e51510300c00680145c496101d00a0f0308000c0112401c1e94281c0e0116084507079080070300301d40d2402d08034001000d4401d80d4072000d03405098440c542400302c0c0b00c4040d408036800e00c9030044500010250040e200ca20900100050350400c961024800a14995007041c540d0018007505401c0d013418807404c002d2290f5009211181b201600b200c1c1c66007051107071510182c100001e055100814200d614401c000e142010320103565082100005010046d124800303000007072a002c00c120f03d41170b041c18080d04a40700101181e61410b0001401c0700d00b180d10443c580d034818041c40320f1f070180104a090304900c0740e00c408200080d284401d5400c5104800700203243c0200050a4500344540340c2000300208402c0301d0030081c143e550452600181d41c12200421007107801c8445100080d0840c200300c0d00700340108804054052001c8a5600e154003020141c110303644054000c01040400b4058900503e009040f0581003100c50f5403161000032084003440500c81d41 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 571636483 1250 571635233 571635241
    0x10812091504030f11010801080102071a07050418050f06100c02013b0a08071d0c1303030503040b0106110d140903011e140c030f060301060b0f0a090f03030512 70
    0x1c081d0a84024541082d035404254109203800740c00908214241404204440000a4030f00c5041c4296401c242c0c001c0d407051120090f004a16203842001068102805010710000c0703003015600034803500e004118500012a8100755040c00c41e4420f000741114803c0d400952021006036112110084566080c20103002d41e52480000410300d1071490000c002d0b01c16803461060394481c138a80d05150444080c0c46514102c4e4031800c02c60345a0305240a80443b0300b007440c0200310942884d244541e40a682105454100f100d6004141251b82c590350003903002034404002e200621078071000050041240b418141d000c560300681c1c0c1034840002c0d02c60001031052101d450121020740c4012950704010050080140035444400003005e80c0b48490030078010380c03500760189400100180c000f40a40084100581513603903200c40c8008103440200070076010354079490005880f12944016000408085946940740e0302c00c144014624281540410303c060b004607010408070b50082c1c100d42054110000b110308650b2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 571637733 1250 571636483 571636519
    0x604030b19020a03091a010e010618030b04080405041a0a0b070201051603021c0201020a0e0618090103030815040516050c0f070b18030d0e040b1801080a020901081209 73
    0x980207110308600d00008125549540c0356100a0a0f54401c0c03000b66560400c0c4581c07940d5003403007401211201e103104401806402c0c000c402c0ea0f00b442003000c1040a0060320703680e42e0318401c3d8043c0e40455040d0700c089404e00040c83c1500512200c901034840c0c000703440d988000020310a61080c8907100c841280001e802040d64416411200540c9481541c0281d4240e41d24000390390300c08088026402c43e02030300030480c2070381c418000c40b80210035903900c04001c0d03c281010044154000031040d03036030b000b614010b203400c0d46480c1d441c28020360103601c0d10402482c0c42c0351103905c0700da505400188258a44420004180401c0b10340c7c80c13080005160158841c1d0303010100a00d0411103111600280c4600c0d08000f481620704401404c1c181000d9113240c0c0310760b951005040d9038000d000450000f0a2200307070f070025607090550104054140007004030071105207a62181ca03c800d000e030440050b07604500042010350070900881401030040074018801309040503c602202d00403401540e01ca5400000ca01c0b521036 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 571638983 1250 571637733 571637761
    0xb03100b01090902031005100807090b090a26010c02190b10030206070b0709060314071d0a12020a06080c07080a0203041802030a1d07090e01020d060b07051b0604030b 73
    0x4083c1200031940d07403c1c44c030212000d100192054034030501060008032203041c41210704600891140d1100b5a480341410f10064207034001e008040c0e0000719400c00080d1181014030f040e84080620300b490380f0400d078450022425650103d641100b590322a1009803800c00010900101c2641c101c02015110344803c0501d0882d8056640003a51203480071404005100f0356800c12401048581c40c0d03402542e80d01c1c03205405842140c84a40b58095154000070744141c068040382d05c91000403054600660804c0d00001c900e44c2c03090700000445009907d4210840c200010004003601d40d500b061042c038607005228603610301c500c61004080941c04031300f9400150003001501e019001007559025003050481c041302c02900300700d51400b0500e00f48800301242c9034501d05104a0214800050301d0030a043c0201440601409084650329660800c29808058518442c260162001e401082e03038071046402c200c1e20b0001081c0c5c1301e042c045841600d00c4016507406045404a036403005903079946580d0450410b000b5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 571640233 1250 571638983 571638989
    0x90602031812010902150a0305010e0408180102010b040c11071d0c0c0304150c0b06090c0a03024602070f060305060d0c090507110c0f091312050d0f0b03100b0109 71
    0x81c40c1b041e41a601c2c2880090410f40429650410503681d0792940c01921480c2581d000d007103018200010300c204404031803011901903044c00045154021500842c0444119941c0100091800e052010950340144000e8005140194014401506d21040b0a12401d0050144010b1580004981c03c200300c1c00c4c4103440c02400c0b4108240f46103a910703080900304204880084881c40000800200301d4640700700800d002d00c1e070719403c650900200d03000071341c02035010010507000d0501c88492034803041660700c606250303048403c840c15240c000d510403e02c1e0301d0700900d030024155000800144408001c0c607040390704035030040c500450280c81d908081512012103c00151a52140220200f6030600c9500480d009000503680c0303070001081c200b1407030b40324451010810380c054400d840c5910103240031046a40c200c440043c80f040740d81895a03c200160341c0522040c00070501c0403502300b40e01c401501c1009401e11209405000950380440001c0d1540920303262410115980c41d52203019900ca06600005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 571641483 1250 571640233 571640239
    0xc090320180a0903090602030c0d110a15020a03050f0f0f071407030e0306010911030103060e07081009030206010b090d1403220906090b0a121e0f0201090602031812010902 75
    0x20341401c0100e040030f0905910705030080b404008001404510020489510802090103449036454070f00c0e0403174180d0880e00690003d1301c00e2642080200b02c0c0030303400c0c0600c1144c1080041c1c2d200c0c4000340103419100000c0040b00b500c0d4100003000f40000c081441c00c0c0d07104c01000d10480b80355882110039104912160340e52811000049111410150041086100748008604840181ea40c400c4036106039020181c0c041c0b2924410300040000a515800022519019070152a080d41e100c46143e4034240c0c20511400005440b09400d5040c0740e01401668058151484140c1c5000149004684203129041d00100f103a0041e000e00c40d41c11006105680c8400403149003110620305507000048858030901903004401d02d014000100755441c3c4c415034065000150040013280d203050400d07006000d9428083d5812050070308040600300319002c080e1012449070801c018000400e0000600c0001d00d03402000955000f00b12629413860240408007041904035180d4403056a520358441c098601504001c0d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 571642733 1250 571641483 571641529
    0x1e070e010305161e050609040209060a051902010204050f0f0307080d050a0e090402150a0c08070b0106020c03010504020a17070b040312080c0f0304060f020c07080706030c090320 78
    0x7003040100707450f03031032001c8100c86440403a143c440c4816140e4242128441d03000d2001e00c02c00c058104180502142d000007040141015070010100310355901040c000400900e00041d4108124418030450072081c0c202d10085040c10b0505000c101c00c0242c2c3c072441e80c440e80d803500030300f084ea541c01c01000c0003030010783d415214614071448000e011508401d100320089612104011400d003401401c142c42141c0003410050300a0852500780d0039039101d036001500700203c83c9038603404140080002c00d101d41c481d149500840d07241c4040241004075001d444c2e44281d04090501000d0307500c01c80040156440f220301c403684400e416004625147da281d1211008102c04200041800305c0701990031842041d0351611141541c492100410600c2068005c1d68810b07020700c040350206509078054a0711911904005282c000700362911450042103510051060340000c1c024030240394940141c0c91403014030309003c1c0000782075039128406c4100701480c20310101c440300c1e508440d0750340300d010010a160000401031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 571643983 1250 571642733 571642739
    0x10080103050a033e0c1f050a021c0c0b0105040c0c0b06030321040215030c22170601091a06072010030c0e100e0108090f1204050a090e1e070e01 63
    0x841c4000d1302c684902c882c040c3c103004203030b00d0078580000c001c1d0501c0d0380300c207032001160300100784c0b000e40080c0c415800311b20402001d002412000140580c0d00c150f80d80b5198500001d40c42c00800046050300b0580c081d5042001540d07580750485806503a1039400503c402059450740c0c040303443c40c0928040b400384580c244080012003801c1c50356160040d03000391100c0004209001103419144010740300030840324820455603201c003441000c81150b201409200c886401da50707040042c2400700351100b9001b1504240c004021402507840b41011180c01070324081d44c0c401e105030018405004a9002800344041a50081c0600c0030340c148900380b1440007050b489a201400000900400058202030041190b038003400c1311074500724949502c10140f942d905c00410507030b0030044030311300d8010380036800910540103041c44c03c21041c02900d03540c07048170440e140c84514013400c20445d40155484500c00915206c81d51f620040085040009106c004944c49a03261902442da071030901560700222085203154004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 571645233 1250 571643983 571644077
    0x40c05131e0f0b03040305070f12020105090705010e0310050603030d09080406030b010302031909020f0406060f0e040c08070f0c0b070309110405310506011410080103050a03 76
    0x1c0710803100341244100c0025140c0b0346040c00441d46000d6007100290a00020700001c0c421001404007501c9944a803006e280030360780d90004101d03184c0b8100090303511401008184c8004000c01d600528091030081c000f0000d80003c01d80314000201001c0d840754403000002c0b92a10104112004c09962440070400c60303090f41000c0005403c507000340c100090615002c85070700c1d0f201c1c1c02640d006040586003414401c4080e03134440018214010100d802c24018003419a05039550312412000341110307101e0502c450440700c8010300a04002c0045842145003c500406060340080b81e281d0211213418003a0321060342000c1501e12042e4070354002d0009042c101008540ca030315401810303e013881408801da00d84170020800055a0041350342c001d143c403030501055111450703a85042c0e2021081d1400840c0c1440e5130f140c05003803034800d802041c0403090f9140000321a05164404035021a000d1821116650450340d8442d01d6407240400641084100c00c808000754902c0000300c01d000605951f0000046441050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 571646483 1250 571645233 571645259
    0x40305030c07120b060d0f120806040b01050c0a230a05010f38040b09090a0b01120b0a0207080c030a020106210b0f0703060f030503070606090204050906040c0513 71
    0xc912080c0101100007810040061044100540c0403590129581d9010244003810880040685200c7e8a110200c1c010605c5a00c2c05400040a9686ca40310752910005000035102031050302030400c142082514808000800c3c40c060b025403080e402c240e460b051021920b03101c51505107810f00360080c0070800007003000540c40101c65110702c110500c6440103024482d101c2c0f0700180b0000500b901442581c1c204040b200380008003205004100246d104404000b0810b86641203c0920039903000c0143c580610188000c0c550040c04466680d4050b0010b43d40c035142814006090080415004111320341040040401c8d11444066541265125140003000a01034443d61040080206159484402120404092044442d0002d81c040540e484041002e020110014142e20405a0b6035001241100b0703480c0107400214003c900445d00d50720113007065021144117a20152000748100010031080d182c0c09a0554041000c07100040c80914484003904e0912401f003000241c061201070107d00070140a079 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 571647733 1250 571646483 571646497
    0x30a1a0108061803090f0102010f090b0108120702030a03030e12030f071409060a2019051023070c0501052a0403050303010b030a020d020406170709180e010204080304030503 76
    0x4442c100e89903c000000c04581e0320680400300c0c4c004005003685030410480888803076038180b00014440980303840d05011a41054011111100260010000f0880c01c00002c408201e603551a40d1800e0615800030395508a0182c004040c1511072100c5d21150806000c101030001003c0c02c00c60344c038904081da4101242c01241c0130350215060304030301304800d058034040d070b600d101c00580600e140050300401580c00609040003c0101443c0e960040303008074080c450480f0700c000e16540b8007000e150030301d00315050007803c80d11030305003516010f0307252017240c202c1103910a0500c080300004901e071101c0301e080b11728644690029001d9800c000600400e0101c160544c40c034180d090321100410b407618810180148210b04c400b03015907100744014090b5212910040d40c2041442c4401031070305002018401c107a8000794841800f0603086410100f2588007107090503407008161514038019410301400c0c1c00d0b0381010202d21485599541003244107482c0960499029200c0f15041740c2d115507503460b1039a40e03680280307 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 571648983 1250 571647733 571647749
    0xf020411030601020d08010305101d100606090b09030712020303070506090601060e0d1208090f060f0402090901090f06020a170c090406060809060c0d091a060a050607050c0f030a1a01 80
    0xd6038510505d845a0b0b102e906980c0c0c420301401c1c1e064191050ba40151800e11500da80107400c2030700079400d40c030040041c0c0d101d441c11060045845494403074060054103660b4003040410b8010090900304e42d030046a103a00b52601440072091903521800881d145009400d40205144500402e1111030100001c00d241214035a5803821100009842806800d104280004018a05410840c008140143ca00e0782e4082c03000411500c418250a04c25490311030b040d9190152034180205100c290308140b840c041d03000c00c0040003230160845c2950b400d1185080b16134007400083c1d02062034880a0f220b844185064540c0b51000040c40c241400d980c096a070000031490300c0b40e40361010001d0840c3c01641184d00c906610000f4240c0c80d91041c40280382544110981000360f42d4030110030700000c0815201d500d0100d100c07034210b90140307440014040481203540250303100302c03403c0c8040b00000f000010503c05001081d13802c0b6271884066808203203040d1900c0340040c100daa00040080d1481c24040c0f045040319050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 571650233 1250 571648983 571648993
    0x41d010606020f1005130c1707120206181c0302031908070c11190b0d241205010e07150801090b01082e09090614070e0d0f02041103060102 61
    0x58079081e40d464424070750006150704000b003031003c407080651040da800251103540b00c6034001203070b48030310b450b6086800044880743d400105840c40c1e00108000c4015004181d0400d29140712600082c8080c050200091031540c401c0740d4506c19500da21a141d604002d100e83ca550901203603240180d00c903000810100038902800003404241881000c40078042e03c12615590884007480c1c0f1601121044402c10316003005009049807107400ea04000744006141e40d080f095100d280103585402912041c40c1c3d0041e05150904d140640100d041d00c0103811116091000d03088241303d40f509070301601200b09580c03000d0240300c50000b04940d0111000d0b00c20f83c65991641b64582e00c81030300d0000c0369116040140010030340e6001940040f41c070f00d2409000e2050400b50301c16004030002c003070380014090308450f004980300c40f1075000300440390080518100070001c002c0340b40d01c2e0a9100914168169040620444071055003a06000b00440504607545e005001400780f85001c00503800c1c5e039403003603412074018890 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 571651483 1250 571650233 571650239
    0x118090905240601080c120f010e090f030409021b0d021615080402040b01170711070b120621010204030f0227060f0f1201060e0601110d0c060b041d0106 67
    0x114040381000400e07100ba29a11140300440d600b1700020301203a40e9010030041c3c0903000d45606807052280260400d00412981807641c2500d0303400010b449000e140d4020f505083e004030b4048103a80c181c46040d00c0058544805025026066a0721241c0342014001d0f07404402ea42640450841c02405003004041429641c810403104003600304101900011a0765012030010714203600000ba000405250180000f05008102c0c0143c00341514924082118070540017441d04051203228010900342141d20b08155200a00119038140106164441c29245941c2149446090340030721500c029480215112a22132400303907031103034072241c05034801c1080e00c05015100301e0041d02c1805500c405122072109440341407d000c0c0d010000382585d648050380502c00000394944d41501c40c00e0743d03030b64000454458900704801a2081c070107840340e81000076030701c3c1c0c28200300c0380020a400361021a01c0c228030030200900b0104000c20b40c903030329036900c181042c0c02e042101540709009000001400020080d1603a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 571652733 1250 571651483 571651513
    0x20307030c030f2a2c0406020d15063c08070e10020a0b0a140f1b040b0d0e0f0d020114010f062304050405090c01030c030216081b01020715060608060105180118090905 73
    0x4061050800082d443c40c1300c14a12074070300181250333407a80003e0342c4a151180307440455500541084210000d0900000c011240390711034104181c21b10155030040c054440e40000945652040c036000d44210400b10125410203000d40c00f1140d8041640c00e9541da44c103000b50007510070141139800007450744200540720111154032046400311102040d0306490646484152000b038114039500030041c3c002d1040550440c001844002040b034201c0d4000a6407075002200c402010f141038019003418a000e03103060203502d80000f40b1000c0710701004852080001660102c08580c89141c1202e600b245c200020b0080341240000c850300071f01d809032810300140381300f0b6404804a0055284c1d8440400c90300080784042040c007402400088a81101c420408140c003c84030b082e41e00079101151401c4802c41d601c40306240b680301310005052070340b8107480e56080800009000e406904c40202055142444045951f0b0003451100f84114403810882007040d40c0754812001401d0481c07060343d42d40a0940c115400345 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 571653983 1250 571652733 571652771
    0x11090103030224150d11090115030f020f120c0705160305150f150a05090f061003060303053c03070f050405060f07020307030c030f2a2c0406020d 64
    0xa880d903040e210400e2130300c0d001c00110350703083c80040c0e0f5840d40c2402001c46a4407038818042c080c0c000d144003081c00b110211001011034109080c400e80c11481405030303413081e03280002180c1040c12102480b1ba0b02d515501c802c030500344070300e1000030241c0c0306180e6511207a2480d660840122409013090760119082180c000140300d40032520125a1403251000509500d09000c83e12450b5030f0103054800d825443d0400300c0c0c84030b101582d108114043c030504100c01850b02900a81030891285401e20504e4510b94016087d0b020b80241c034100b04142d06511038001d04050503e120411845400300307c46803001d110301030f480d441960354100084c4240045800e150092040303a0840b00007400d1280b62001c1102500a903070000c080499050103406000004507003a185040051401101000e5000c201c40c580030300c8164900c0c1c80c0071035a040100e183c0320880103807640c910071074002451006072140720304400320542641140400d0003002010521062107902d502400803200304d50b00030044d6001c080b0a900e00c0e1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 571655233 1250 571653983 571653991
    0xb090c1f260402100f05030a0f18060507031b050702060c03040f03080a0e0a0e0a110d140a06080606090703020903010b0604121104020418050411090103030224 70
    0x480304045050403542000514010440450718040854648401044128020200c641d100c590080d50a200951400011a41d00c1e07000905040401c840420b4000d441c60000424212a9942da0040a9201d072880c0e0440743c4506508120030780c1224040c9080380050800b9106040040e00c4c0880350001d08120100080051000b81c03202070a000b4103a003008035a6010310400e030058082404001442205500410055441110101d84950803801c00511010305001d9503031050140220401000921303018840e04580e4480380803482a0b544992191141324510a61040c0da00e8071030f143c04950824880345014080b60743c01031000c0c1d81d032240301603607862081d0340542d40034402c6004500c10764001e6008224440004d000440d030451500001501e0350025888810401c003418240401c009401d0a001030b0103604540460905040c01d580c0c950a4a00500591000756144045824080e140200508841005000507029078492800a4407041d801c0a0ba10525203103201c00000e1421031302a551103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 571656483 1250 571655233 571655239
    0x1090204080705090c1204080318060105210705061c0501301704030b0f0609040c1e0b0d0207050d03050402062a0f07081002090307050d0201170709030b090c 69
    0x641443c0401c144031a0180c00781050b148108034817444484502c01d4584a0f902810700d05480380b904440306280d402c50401145036070341121006005556581260325494045d400014040b245510340c56480c0c070713025401c010f88c00b00020584408034062030300d0303160342d40035440000d1001d41d0783c86041c4031038400c44c01c40d400c92400100760b007080c01c5040c5400210269004807980410040800031a42030350b0321580040e605d42e0a220b040001d968030741207880b5000714007540c00e60085d103040e8072240141c540714018904500b48051605170550100c44280c40600000701504da580d41c00d48001000070f6100720704c00c882602a1b034080a0450380244940741c49190050320940c5441003011026010102d42e14000034110660104808480800c0103400812640c1c02d00406260341000140c1c0d141903222010084468010850202d541d01c0202c0c540701114001d94290f10031200510040c1c444483c0384643c820004105002c0241a0781c0c01004c41c41102c0c01880c1003000b94884202d0507450f4507200c02407c0d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 571657733 1250 571656483 571656493
    0x2402030c060105010c08040e010303020a1406040c0b2209060501020c0a030804140a0e0403020622080403060b0a081009021005070f020904050c031006080607020f0d0c11041b080109020408 82
    0x254042e030141030005d071145d06001d2038940c49004a103420034003030b0810760050303100b960484200411441442c410707120345070052020780741c1540d440360328160394003801017940d10100d4400c80d500c098644881282c40c2105000c200c10391038810315402403001c0d2041c1801031080c0c204059403070402c040c3c94001c0ea90040f07202c2e481c050502d00007402c0010300c02d004507045180d011000030390503038840185000e41c0c8650301510103400d1104040346002c00286200c0002c525550001c00059589812a13048070340c00100412242d84505c0010345001c11036120041501a150955000031050360107845440d1080700d40d0407105006200c221046c0c0113840c0010708006c0e116040001516041007601e501520540c11501c9005a8802203401c0503907003158044010f441e03650500c0034003010300445600550a1000345500e03221014800e82d1261004034800606c1100d0714010f01740032102103480f0502001902c02d0061207800014406440e0080c0300143c0054841c000104031418180221012151104000c017 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 571658983 1250 571657733 571657739
    0x302030105130903020c10050706110301081b210d0f1b0b09120f040e01150e010c030207080303010f08011812140c07060c0311030712050901050d062402030c0601 71
    0x10081c203d00505809500c100c060b0a102943e43c5040c2151b102d07010341e50140c41e82d00c0da01c2d0030026280c026184680c4440709000500903140e0009400b240c500c1c2070f40d0300000c9106841c001c528021043d449145149503c4001000d00d5480000c0680700c1c40c00030341e02c41174031110340ca004848801580709121004450140014003054074100295041002e00701650401c2c28902c0c07015010b6489007403264001c010129040100142c038a000340e00400004d060300034402c0d10030700010300a80c50024841e040c0501c0d503d00360140b5101b046554050700351201100c1c4d40c2d5854081d158a458068401c01060b0360802c0741c1c1c400402080c2030401c801c1c80d44210840340036076141720141c03032002e4030030b0b00481103007c1403000502d2038004206d007400803c4540c0f83c407001000c20b030400034082447e1020070100340d40108826800222007900d0800003511928003582c480320110012179180c0304d042c4558803690704040c0d0100711042c20f00c407503d5030f900e02d0545070402d10100410603a180d0058040c10010740e00320070010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 571660233 1250 571658983 571659019
    0x80a1b050703020f0715020c22110d020d0912020a0b070503070522030b010b0315012109060c1214060409020d080a0305011415221716060302030105 65
    0x75000c0c1900c00d006950b202d5a04080140c80c0901652001e8801d040b0301604e1a0141e40600142c2000e5006440640d40859500d1201d0b02d90161000d040d480541d54202a01d0901090f0050f95103c600782d4000f5995080b0301111040901500c0c0000c1c1c1d000c1c02803040c0c2415243c00021032080c120381c0810024000d03a100f074004c0c1e580e608000c01c40b6080c42020081c0010361003006600c0c00c06010510f43c0451308904505041d038000308141c2002d803290008000f40008800d061002c07401d189024a440004440ca2000b00e51031010442494a41103082c00300e40010403c44d07820503000458180e41d00b41700b01c00e0b040841e030244c0303e1072000316519521038400715481e42465000314207810300140a00c84054510754134040b656003e4650080001d50b50390050014804942020303011306002c44003881041044800030400b8852848405030300a2902d06503120b09000c2d10309680113040d2142414605000c4880c4180c4641d6280d1504a00c00301c1050003103121400b910a4030b041e544041c1c500800d40503100c042d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 571661483 1250 571660233 571660237
    0x50c160321201e010e0607030c1407030909140a050619060305060a0b1306090504020f030a0525030605090f0717040501090606181802010e0103151a030601080a1b05 72
    0x1c082c0742402642c188281d0003d81a000c08402040140005144007802c1651810450080c0940e01090f081c00041c1c901c01d64400021400311404829188d52500c0600d0159001c0c460707940300c01c90f030501300280c8250003c403980308039115881c00101440113607125010000403007108255500116029241480043c0c0302e580032350b900030b0003c0c12021150b034440003810000e41041c02041c0140b00200c4040c032000b680300340076000601c8252029070411003d441032405c0e9002c018007140c40b060303650001403292040d056104520748865280c0603003c8030103500040161640d400381c030b400790f102100480c24001564000d03d2081c400c607900c040c101d0001c480380072207440b005001903481d50b403034000b9140401c00c0c0b13108400c001d095240100010700807106040c2d0a0724403100c1503100682120000001503608218104040f94091a002a000102d00442d1081c0c00068000c0e036040d02c4101c1d13100340c41c2d403001c01c02940610401d0f07e6428a03661031000030000d8400002c0403403c030615080c0e88010072401000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 571662733 1250 571661483 571661537
    0xa151203120230100e07022506031a090106050c150f040b09160605160c030804050103050907060e0d022704030807050a140703050c160321 61
    0x6001e00d9890001c51041d4280e80004440d002c950079040d619030070071840560301d0034000c842508003a0700352034441110a80906a446840c0e00c0c00805000070342d40d0f5200b4814103020040021010810719034801c140481c42d00035002d8440881e2800b1083c14058281034059240ca1a0013040c4044980c2080d400710380369040364880d61121b108400c1240039816158450354442c02e4012404444e45c9020300706200c000101a1072800944c02040460540813b000c0d940001e550840c10000d40e40e0341e41404011038203181e4440078001e000310101c00b10800151710300030012140c0076a000d000310780ba10310500c2d0300d64081c0c0c07240002044080c4212451820310f6000c0d4200140020021001a80c5004030000d034090505200c9512004250401c410103030805c2070241c01c00d00702e1915034141640200c2c0900912041e1040e90b4101201107160b100f05841340f0104c0e80f012400e8010350350411030140d0400000d0070750780001c941d584402030110140c7c200078040039504c0c290994414440d02d502000300040e02c1402c803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 571663983 1250 571662733 571662737
    0x6080309040207061d030909180a02010c05070f030b090c0102010b010903061509020726040503071e0f060801060207050303030f060d02030109020603090d090f0501050301032004150305060a151203 86
    0xc16905c4020b688140c250b51506045c006540d881007140f0802010b64002010344211003000400061207e40c000340c903031000c03136083c00c0000080015040580c07800c400303a800305981c10400c04000c010440c034884214024140d5208450041000200582c01d070350b80104098005003a281c0100f01092582d04020040070501140200003034440155405070b03400700304141c542c00e01d40503442d101d41007000314001c14501d24140700c07420b15013002c0000780c8540892051031440c507942c0600340c0149949070300d050010154107134800041c0d86d4030724024103081000d114003809800b07420000101824044102da02c41c1100380100082d550383c0c1400c0003246016508160b82640d40c8400f2000142c43d0718005501030869030000304003a040b4020000d0041b069900f040003121200ca03410041641c000096034103481c3e00100c0b9017108202e00200381c621040d84c0b00d10a80c804d00300b40000109100d22a81802603c0c05907090f1000c1d40c1d50080743c18242c0b035040064014080c2e9041c4100100c000000c152400c0c20f10034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 571665233 1250 571663983 571663991
    0x91c1a150a0b030603101116080c0709090c08120d020f160c1e030b01060809160e0117031c020a11150603150c03070e120f070807090608030904020706 66
    0x38401040c0305035080c1d0088000700000005100403071804104050383c19903c0c60041c080001c444010002d28014143c4003d2031004e1441711714100304003481900c01211451080704d60082d070752400e203c040c207401c4009440c16001c00e1408a01c288020400551200691000500d8130034100800d0000750f011820b02031844009200081035071685802910000b40103102c40413900342410141a40c002c900755142c25401240001040014810803403a41102d27850700382a1070750380d142003c0c1420502c010b60403001708080380c0c0c00450456411820607041e1540e88035000e0100045840d0940d40f88035852200b420b58603c90f216a000e900aa00180902400e51a10483d404005450702e841c100b00082c80c0c000394120310040020034101005024618507011030211101c2c107260510080d1444003402000c00c010b00780000a60355110f408071000300e0341450040b0f0740d9201040e010161900058002c448990040100015250341c03540100c4043d640085c01a40c601008502008002e42c0024411a002616 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 571666483 1250 571665233 571665271
    0x705150d0e011506090f031b030803181e15090f01020408031803010b060334030e0606150f0d0b09072303010303120e01110f091c1a 58
    0x32400384400d10201d030000401c0590240c100303454414000d402c4007082001c1701104102c4150803c1c0440100e94000d1039030341034490604030b4990144840c2d040903152403000001d00040d0a10210401c02101802c03094030303002030fa0088d00650130034800780824059440340c2c0d18194541e8284042942108486048446940d04808064266040340e4450700d01d5800114500040c000c8144104c41141d034210001c00c800100c80c800203a140c00081c01144034402c14504820500e40ea0104581000030603410240d03070040940401005000308803007282d15401604041074407030528403003103c0303018040140784e42440002c4c103e2140e0768200400461445883e141030306a2516601c2140b40a00d1003a540e0031150f4280c180750742c0d1070f140000400103000c0c80410041010075400084240d081200540114224054940c8240503001070b501c02001c1032800a480002800c600380104110b03c82078414070f040784840c82070706c05c07120307640c00016101520351070454600350300100e0240c1e40321031070150003008018 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 571667733 1250 571666483 571666507
    0x120a0b0702010b0f0a0b1c0212011401030f060f0506090f040e03072901050f0f0a230301270c12050703061404031e050424030501050102030c070515 65
    0x4040d588440503035542c20001c0c045040074511040305540039900003803454640040a801c83c410642524002c02e0b1500030900407103e2501104d2043c0414032040140c0c4d41c48200e4680e01c0c0526000542c00700340780002c0c03490004214010003007124403001132243d2039480c000620515600000d0444c0d4080600c100a508941c0c4510031820010101802551514054503206d100c1c1d020214014602c1e003088094900c0d080d0785110000d06461090382e01651318560000071420484600b543c0c00d07403000b6003100110351400c00c540d0001101c0b00301d20303111100300c21550925080f903050717448804500d407400584034800100c84054407825441181013100c2d1503035800e0005d106100d61301049130250003407202001403003054060346509103005264003032035041c01e54019080341c94030000415607807400c0c0c848104843c0200309950013040e14001c90003031000b200309250040984801d0000100785460001304055100105441c4005030030700042c00d12504040410408141b40c40052003d600104452003030301d8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 571668983 1250 571667733 571667753
    0x180b06040b060c1b0108090705150d0e010b040f0204050a051c0f0f29060405090f0d030b040e0309150304020d1202030a0206062403060d060c05070506071409120a 71
    0x20243d100944111032594182140355000e900307030350341080b5070482400100341c0302050328000c40700d04840c1075600d415944c4a40041d030240440c020346e80c2d40780c13607091b43c1d02c0f05042d00b1203c400d540c115410840c0c0c1220000e150124040d9004850300f0070161042803005080c4110081554810205a00703880b420319620a00d4000c2c600200311010059003650b04200141d085500e40c4011810400c0351030708500b05002014100c0017486030340b04076107840200d400c0c040240040034464280d0815507074219070041000c2c0c05001600c41c1a03014924286030380ba11500040141c515600000344450a41c1c00c01c0c030003e83d100c2e000580140e07406400c4110327a00c0001c00c101040410424079401442c2c0f107040400c8007030300301180282180d000fa00007000458104489200b0ba101c4030191a04044d165258000414400c551040004240314940040c5000b0240c108024280d1a07102d03104560a03940c981c501100c0d82d0001d88500c0c0c028000034031551215107800c00485c219604c4400440c0e45802894403102d07400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 571670233 1250 571668983 571668997
    0x915010c021225080303040b071d19030308090303010e1605092205090615041a030f160f1d040303090b010e0702010c140d09050f0a060c0f0201180b06040b06 69
    0x4010f0001d1103000c800807003e9000042400342d01550961510340c8030945101170091404007041006a00c00c01200030720017407840000340c060b101c856088a5545440385146035030005602103007003180001d000420010890703050b2202c041814100303481d01074040800c039140912003000c1c00300502010665444410b5803503801c1120098a20480e03e01c1c81490703040710b1001d010001545c00c800100702d0340c148900948a003c01c01510700007a014680407809419088904901e07605006170207400303552000008502c598011080e0300b08484555401c0c8445400c04a80b0501d94142d0144e24904004803843d505280d000340a418049030007a802d80c0d03581d0011200b60411030001228809201070140d0902c90421022004e081c203200c49840d4400070680e0f80036150706900069202ea6012003040803d1101c0c030703203403c82c0008842400c0c0705450b100010b0001200c101380001c01064044031640c1c8140550b44002e900b002d801703c0305203035a0b241e11000c2da8008280e07980060f02c5082c1d001080c1c6880b0020014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 571671483 1250 571670233 571670263
    0x3030e0a0305030d0b0f03011505150c010501120501062c071b060608010606020d08060f030118050307020910120624030507031e05070b03150a031109060915010c0212 73
    0x4104840c410481c101011b60380c600d019a240086629103003003201c0611003950003c85d85e000040c203003002c2c03070072262061101d40c0100c0d5081400000300c0e13281444c1e0a400092042009002c00354480c844540241c810405258840052601505490400d802c1044c4c000901d80340840d100451034046034599005600c084a10303d0303032200c0400000e0000c0c400c4001920343c074809420240d10880c8020f0074280e01a02c66407258400e00401140e65030b0950101102c009a501710341d51340e5400781041130f00c0e84c0120f001a400381e1080720000d00100320f50403d400540d00c0e0080f1461601c1941e40320000140740802010a096002c011f440c001e41c9400900000194462001000d86d28210320f070140c1c01d070580c4e00c4c4a50400910164000c001640400c2d81020b60303a05d01296a1680d480c868662101201480e449401902595000c024008103030000156110180d4207009241c82340d1042c01001802154400760003205800107100540c494042004800c0c002403005d401c1e0b11100d0b00540c10a035545240d500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 571672733 1250 571671483 571671491
    0x9050102131410050f0d0f0b040c08010e0603152a1b070506071a0c09150703030b2211070c0602010e06101505071a090606030c040204080703030e0a0305030d 69
    0x18614025544250410040c5051341c04c1a00005205e40303180581c03010030b2109078848101c0240c132070003079103c2c0540c0e5000500a20242070218030180056000b0302a80c829003078281c0014041d414002409004102c21b015001000c3c0c0e19083c02002031655200c6c455825a0500c50f00500007a0b460003406c800107480c40c021101035480c8039043d1030450b00358407042c002e440500c000b90220f0300080201c402540c140040042c0b50756075400001c09807007010300044c4e1159004060381c00e80015180600700301c5110340c1b401c01500f1038403410007103840010f40100c2035121089800d17011a102d15004641d0044500084c1b41c01e10b0207d0340c0d099507001c8107410100050b903544115501036107081140c203801401c2500c10185503400d01035409140d00c01408400c0078420002900c008000c054024407900314200c81030300c100c80c20300d101c144c2d0301d4035000d0301c0c664800c8c4100102e25240d494280300321422130744a000200314441c0b07140e038151440300300d012a80c0c2d4080c03002130000002c507000784002d0038403851100c070000f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 571673983 1250 571672733 571672769
    0x705060f0603210d2408010218010219080f070204230f0403022a0402120403080a1a0f010c0506070e0a0f1511070f090605270a0905010213 61
    0x1881e04000d04a842a480c4180100304401c0c4076400865840144c003607030200b030941c107208405200101c0c00e8888120a00c1c84000000c5146066016003504401c02c8416411004a1001243e403a440407500c4040b50b92100d50020002d84410300404a1a100d000000d0811061360005811113032000c1c1c003040c100e80540101c030b900c031519420302031380721036038020300c6010f41450784009584288140010b1003041441c000ea0f086569010ba9240320400c0090041d0364880315104440140300091380e01b203020512044c01318818908501a0b04008000d600340c03c10305c1c140700010001d80b900d0003400c031030502106402036400300f1014451548200c0d90390325402e079900b800d03c0078060a4079207a48071010704150202c040c80718072441041c854402086213814041e00700300c0000070341488030036800350007d02030b1340f10005081000ca07044102248d40403074030a0a10072080641103041141100805d00c0300c41600e000035800c020690042100c54007d000050820f5800c0b0201001d00038207802c034030034202c1d21100c15 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 571675233 1250 571673983 571673989
    0x914040c06050c0a0b0a18121101050c07020d020409141f091e050f03030712050a060b070b0a0603150f051003020307140103020d02040e070f0203040501020d0302030c0705060f06 78
    0x400041c0098988070b881d1042c1d81c2000ca032200062070000703185a440501042544180e90030028020030410340400d1083d04d00e2604020752403000b1048e001080e0900488804040f042c030800e4800c40d00300c0300d2546840303400e80c06c1000d0310b842d420081385d21981d1201640081200801003840d2480b031000180b14403500c422249650803100f540c0901c080c1c2c20007038000c0004400810340000c083c9042004440b20760300f854228108403104480302003a220100c10402e101d68041d400003000c50782d107641004640c6504070300c02c00b61070150013010500030003000844d0000e00c002200b6035201442c5900050101e84a44d41c0018625800d4a8640740c141c80d034540c182100024031802da0052003070006030500302d10350340c0441d0700c864041c07240c400c0c1500b038596401c42a0340650121a45101001e108550301d40e19805100c0c4541c00a031400c8001441c0d108081146038000001c64042e608140c00601460a0200045019500c0140ba00049032002c1c0144400200c2c2000f64070b00804110703241c00c2c07040c9416418 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 571676483 1250 571675233 571675253
    0xc03021206040f171e09040b0307350f01140711150603010f06090606020c10050f03040c03020d05150c0a09150504080d081f05011d0a091404 62
    0xc0244250403541c28440080d4100e09071910306a4840c40c82e1070603080c1464030084600031880d20101d00e220061760600054066801881c0b1184111803c02c80c3c040c582003410358418a60003004103022340d42c030943d5001e0b0406090180d03900e07600011035000c40001500d0b2804d000d101c001c1540140e4544a4032405032054000c4140d010040c0c0c0351824010300c0040b542c556480f62200b10300c0382150080c01003410ba4a0a4109404204980038148420f60382c0700e020700b000300281d01c07850f00140200c0012070914500b540d00702d00700400c243e503224201084100441d40650020b042207e624036041c3c80000107845903100166814007070005030140c61107244c401b008444004098003800d03030040100c41515a0406c1400040d240000000100e0850a141c140c449108a80007040d00d84540c0f00307038074101640f00540f0b41c81001d0091101c1141c00151850060000e2030340a054007284081c59142c003068803141d01c4044403440104403407610b5035103201340030860f000641c44072641d40500007007009202c85011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 571677733 1250 571676483 571676509
    0xe010c03050c220906030c050310110a030b0105071703070f0201020f0a0302070c0503061311030d0801051002011b020c0102070f05030303040b04050f01050a0209011106010b0301090f020c0a0c0302 86
    0x1000c0c051440c003108541c40a01c12145202d80343c40030302c1d0403500c0f040d10541416020745100507081003c551a41409240b0a1161003010311a2041c440c0c1e01070300e252140180c2010507080071400341840d41c150000d0703026020720b00c1d04a04122042c00403002141c1f540305014400007410304503550301d080c4490018003e81c42c00c004407083da8010080c2c01a01030400342110030401051a00584900041c0340a00808449034403555244c403c00b03051015100714a400b04600c14441c80d10790070101280011301d0346607400c0500400c08290000010452030600501017220b0400a08c0002282881c003001d0140c0c8000c5100428010b030700c00c0360b4140955804029844c040d00030f03400034450092034200000d40c0c1f0700c00140700500040da00b4012074200b140c1044128016103207040240903903d88065410000c3d0480400c050010b0985440d0011500300401c5440c140d5941440035440c5a0074400240301404000909150380e40e820424601d0f421000d00c042111540324641b040d4180b0f14500402142c04080340b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 571678983 1250 571677733 571677737
    0x605190e1e0a020703030e0f031c0603061b0801060e090106050901020f0601080c010210050108210706230f090705010e01020708071d010b04081c140a0c0501060b0403020d061d030705010e010c 84
    0x249078408c1540b400030030303075482120144100e440e07001403102c03d41c0900601d50000b00114180860321b43d585040821038440c40500e5503a104041ea40c0b07070400c07102801010703c1660170840080040c000944554000c100304003040c01190450030303585024910341070003684001401d07005441900019a418000b4040c5210f48500034400e0754103140c0c5481d1221442510760b184102c045819411032000c035001c1e5444540c10100c200000c510081c841c4a0117101450501c3c3c00c0e040420000b201ea44000101500445d0070300c0091002c54105401500d0706020400e207503066110394100006da0260400c00c03030010340842d10100320000f0943c840210100410b03000211a1041400113000a179030014206002500b240e0341140102090041035075842c06034a845003036160002500c00c0819000407640b520700784a81d000308040c6558428004090103540402517000840d050410081061134021880a50200320210300c415000d0009514681c4040d100b1151651a103c250074103207002c1c0b0032031409184038 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 571680233 1250 571678983 571678993
    0x7150f0e01111902070806160e0d110409080f0706090212032704021b06090d020706090605030a1b0815030106030201080406020a02010e030c07090605190e1e0a020703030e 75
    0xb820341e204560041c1039108114441c0c05500c0c00382a84200150401400d140741690244e0030201280c0d1030815044c100d040101c2c1c040d20790b03802281815607450b0031713054010500307050701c00d100d40c02c0001411120100343e801e2907081c00341d0048101124014400c1a00c04c1100250f103420794814803e840e0001426401990070501804140300b91406588800e51410000e00d00031084100001f070003400b8103044600010048440091074000005a136030150030100304072111580441003c99540c2c500f0300807200000c2c1700c00b008022443c0141d018542000418601241d103550401900050484c2d001030600021110b109011080081d440000782105044d002070141d5401c0d0303000038120140c00340c00100704590018011070030030f1003940658044140b04d0701392543c03030303a1188185030398000710b0150030303810741c500400010149004013041542d10041800c07084101e16011180740f0540004000c2c020084440c005181c3c002c0d070024000307106605810006885100c1e60038020102c0700c80884e003550030340c41 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 571681483 1250 571680233 571680251
    0xe0a0c0b0a1418090112020d1e05010f09050c040c120903020309040e0d110d140f070f0507051203030f01031b0306021c05240405091524061c050a0207150f0e01 70
    0x101c8d85002500e43e080304c01d0791106004c0440107030003580107290141c0705500e0034000030310f00141d50704a45070407802a000c90303070507903a00d00070001240d01c2c0b040c480000c200c0c00381c1c03038180116641e0400d1107443d0181c01a642001c0244000c103083c0d6210314140140c0d074202c5080700504a8000070146100500000140210040000d024185a495403810001c100020400120cc058107404940d0440c0c1d110f0342c0940c40ca5440e161050380e61031140605841b5010902900d1402d24000041d24803880301e2107071524451746580c0b10100d200a00c2c0710841c290761240a000310210355140014207250780b9940c27001581c05203182c010b10455070f001e080320001ca44c026200f100ca0142569a5801d420310489000a080d01c880103442c2ca0050b6111010041089240170004030002808201040b24840d1459940615584040041a109102ca003c0c07110b084282803244d501c11642c442c0c0d6122140309001803425000b074032142c0c01c50f4802d01d42092900d8031144170204910301c900801c0ca05402410003031008101f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 571682733 1250 571681483 571681489
    0x1002091908030304020904080c0a0c05100c03020703080f041a040503010f06081e01181a0a0c020d0305040c1703130506040b04050409020604090504080301090e0a0c0b0a141809011202 80
    0xf2004e48080d00c40c621602c00300d810b01c91400100c4142103801c8040b01d9610b0040d1404081440302d81c803400307105078003200002c0c10050103130014249199140d406010114115921611316402c007610503e4000028040400c0c50303182e1800c0030354020358030706030191114035110805080d0360400303c2d14005d685c10040100003001e0700140300c69501c0c07110b1444030400c04611105c0c600401003c100600075204007800103007030081d103000b0103414440b2409010b0b120740d01c015001007039070b02440f0800c0047c2e01002070300c030b0b500f07200790300c10b03604031380301d91441c04c4810382c1c1c5c40d03042481744880340420ba803507000040d140404044440d0709400038101520300c5401c00f8a45001610709002c6c80c45154051615908054110741d101000c5070301030801201c0401c0b1509090a020b403a0350402d000d03c0c5561894020301e040c50710b40c0001c41000c441c1d8072180030007007e8101000c04a02e9000b000c001c00a11010a411000d4940f92001501502c51b2240c1030041103030580080000c001410307480024144a440300403000350b1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 571683983 1250 571682733 571682737
    0x21212130f1d220b0c0a1808151302030601030b061e010906050c0a060504060501150e1f03140903182b0203030d021305010311131412100209190803 65
    0x401143c0c203540808014040c510b0030082294802080414200c0401a241403001c000e003950324071550f144080e01d090305404440c844824000c5120950050b290461030352001040c0c076034030030020780206484140547c04030386403903030a80003190380a445008105c041d00700b000b21000005440c0c1c4602d030700034284200107800d140380c90080340100000011146011141002007060b1241c2c061420040c0b8a041d041c4040107180a001d44484118003c0d111450b0500c81d0502081e0814000c1110002c0010300c2c680c10401c81c6400d4a010600d929000e070075600103001c0c0a8107100d41440c0d005541d44a4400703a0542005004020407842249485501c080070080340390940450075508010001d0180e042c00040d141d80034114801800c2800042d40101a811800d072b880c4c2103601c01e0301d05114405500c0041105801910281c94041e00d180008208ea000800700c5c0c01c00300540544001d42c0040034807192814901e801e10000c5000b03130006503080c0e113805c1080340c0542910031800380011107401c26041640368 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 571685233 1250 571683983 571683991
    0x150c0c110108280515060f0306040b040b0909010c2c0409060204051002070305010c0c0317060114071109060a03020901090e0304150c051501080307021212130f1d 71
    0x410040080e640404600d80c02c1200050340f10b600c0900d254881e024806801c0880d5201c0030880301c2d814030080c0303050183c1079806c00c0c2c00e209410340c01c540d5404140402058650340131a8030a84030024440161610a8030350b000d00d2141e800422000e9040c0c1c1c0103401640c5c0415a0f0141d45801100324814445040030b0b5004448200c07404201c0b8002424001c019025640140d54420f2542c450916680d80014502c1c00f1240700d000203201d4404100020b940c0000d0107017000d000f04081e003400280e10007003200a264000414140043c0c84648196000815008050300315806101c000018a00c0e18140d840740768401002c5503481050350655000c946640418400c800032107403914406e220507981841580c0142c00d052010b02c441031012003000303007122181401501c8034010f12444900d60300355020000d0680704440000d51610100d5824012582100c07800e500d01401444a07649a4400e0301c0020000c00906c0d040100450b4101503405c56400740c180c0c1b0030f0b01104d98050031401d0305074040d1245580 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 571686483 1250 571685233 571685237
    0xd0908070b090d0f02210f03030f01031e0c09020417010905300f0409051501050a050c120c0606031009050c0405130c030303050109240312090b07150c0c1101 69
    0x300c03d0301403406891407040d40000a42c00240010150740900707080401e81e01d040c0014040300d034030110320350301e1549a1005455201d52302e91900e0048c000310b4140300940b0b00100e00024840b041000a0b1036400900416405c014506600011f04011219806005030041e08000000308200799840c0d491b5503464020801c082c407044405071000c4415000c00d03902e070001105945109036104841501c0e5001c5030f2043c054072424a16040c08a215601c5400c000104880f060315007a2400402400c2035507950801580c540380307882042d0307688917022100c90181c500800800000c02490803d0f000301410203180d82c0802030002e10b003200d0f150218100207010000c401c0295030018035070f00d808000c0b18500c130140501a2007400081c20010170168554005412590342071070400403642c100240c03e4010083d4503081c10b1102c0d80c0103082c0003140201c504603026403524103000d0136042d07484400701e015401c00d900581e1018000c0200c10407800b07032805a01e64541c4989003424503006160749064840c00c1191207a41 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 571687733 1250 571686483 571686499
    0x306081e0a0b0c190503160206130204050a02160c0302040e060c030c030c2206030501050f030604080903030403021f0207090b100309051002070b1605070c09021c0903020d0908070b09 80
    0xc41c1403c9411110685541010043d0030013801e41d01428651003030703c1b00c101c0c50340500c0d0842203440c404911140180b010b0380340c140707030703188984c0030800505006014412040d03420130840e581a0210346240b02d0080c4145420700c900b51031801004100e442900d0100115000503041001d0b031548041200e500c1541d82c0c034510707241d88602c40c1d410414000c6a04031024440c07000604a80e46000030311003022134000355800d0240380c0e20f0303074180030120488a9901d50994000707804600010064405007804010160450b420f01d03903260000b82c02003090100c215000001185140e000f00d5051154201820700380b00240201c2c2131110100c0e00e02100f9111b46c4007055521742c0c81004010b418000314100b04644842551502203a0800c2d0074003030020307610500942c50306254041001c1c0588180d60781a078210806030411850032100030081e602014964402d6880002103460000c03640c4105034041303000343c1c01091105001580500300c90546d800080c10340e44000410403800d402002115402c20094030184 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 571688983 1250 571687733 571687741
    0x16170408220306050f070e01021f0e030301120c05010305071b11120313090e0d08040f081821030f0d09140604020910211506060306081e0a0b 62
    0x1140c086440c260310320021000c0d00000240a40313504254001d5000560074019031700c074880292500c084480e54103015800c050040400b1800c440c130803070441c408485010a1140010700f8650a40c0d009030400c440003805d07100002c0034000402a00c0010306001e080403c00c0b400c00701c40c080c2514004541d0700c840c44000410880400003404603a0024001c0600f0f140f80b080e1b15240011b80b00d8000c6c1c07040a148071200d070340c009001885400343c2840743d00300002400300f21160002c11a024500200191b03640d072001c100b440e00050780300e002402d6461007110441032070342c0400d08001c2c191010100205404640403503a61841034003104032071102d00000f00707050b0380e0009614030001801c0040e40182045100040484110101080480c441c5100f202e08504980d240d0100884480941c0900c52036440902c2d40300c1810040400ba045925006124008154111400d0074081c1d8015401a1000030380300c0c0400c0008007410000c030307070348040c12200e4081c480248180381950b84252820190204809102103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 571690233 1250 571688983 571689007
    0x402030a0f15080f060402060304112715030303070816230c0606010507170915070c03150e030904050714130f17060601030911100816170408 62
    0x41050281d5540007440071500024510301d0060161081c201c035401500302d000200c1c0c00101e8007a01c5150f00802e014203607102c5840d040183c0e0801c169980d040b1825554080403681480011061284c038201c10f0019480c0510341628030040c190b40c41c1e406644244244042541c02c0501c940d80a031400b0440e1040d1600c485c1c0c100c600ca500e0340b081004000700c17100030403c2605040000c00110003850100c605584485004440c20f1146080150081c3c41c01c1001c5840458500300406038803c004140070000011580740d9445076028140c01c07200e00d01264010010480c2c200c403000c4c030341200184d0804c1024080300c03549449100342e0021a119550382c5001403103980c018540c061003100c010f130505841d51241c580d481d4a40e1458042d407501039014a00010b03100091004003401d01c4240c1c4060002501c1d22001503000c0c0c0145541103902c04003000c000784460701c503031b0304900c0080c0b2265100000307410100e40c00d41f9800084a007402c20000d5480b0401030221001d660580c0084d0b000d1a041d07611400e015038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 571691483 1250 571690233 571690241
    0xc01030c0915230306030703031821061d030a0e19060504062304060c0c05100f03050f060a03030c060603060c0f030f060503120f04090608150f060d020402030a 70
    0x11041c40c603040307200000380d01944552003c004408200f80e0041e0303909400d540c040c8a002c200c8110742c0c9030348049018000640305260461444240c40c0c961074040d130f203401c2c403c00707010101e0020042c0107142c14074843c140501f0f409500014510703581860090364054040d9034491040c2c0260409201126203000901e44442000c4048511440450703030200d904d45000801c150301c58490711001450030303124040c83c445100400307030b504132603450184d240c249400302c20b840a011240042d00c0c0e00ca240400002c25440c3e1840384050208240d40700400c8503e22040a401c03204050180f10307000c40180f003007080320313180e0b0384c0101d09590b010300381181b0a503110b20f040005485142c000030142130400e41403494054005070041d02511081d1018040d0a1084a1001c02c403921881840e515920541f250218039074110001e10303202c42c160082616042c0c84c1d04501082e181c6661004c01c6540c40a1104822429070441c0503411605404003c502400c051000814080d06400082e02c219400008206600d0590380 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 571692733 1250 571691483 571691489
    0xa020c07170c101106012601060b03060406060318140a05070306050402010e040e1b010c0803090a031106090c01050a050904050f04060c0207231804080301090605040507020c01030c09 80
    0x40c1c180e1800903080c0150300c4440712440107000e040c00701d20408400740900d41d00c40030b0795000c20080c0305517860840c0121901512610241241182284403d0801030070b0280c00050035a8a800d10303940c2c00d00100780030446810340d21070b100700b600c1c0070000c0074006440c15601c0440368100c82c40c101401d0710041c0c06404c010410720000c0c0382c0c0c4039481000040150a4019a215034002d03240c04540420390014001581e030040031002c110f82100d882e9991801c26064000784414041c507000e640740d2865942d0740c800c1ea000365004100369010012800070150301c800d00c2d070361800408000d01032a0a0455255603241d560042040c1803220104000c03c0c0141305a0603180d50301d200a0007031040d030404404101c90098247d45c103031112030510444441e0342e800011000c04071020a41503041e80c49100080e2462642c1c598410303644552101211601502da80010500a40c02551a0769695240c4025081100c5050b400f403400b07282040200040250003144401804100b82004660082c2062080323440300d003260 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 571693983 1250 571692733 571692749
    0x9050a0305010603330903050912100506100f0c020f060706090615080c01081914070e010207050f0d060906050a0f05090a260c070b070b0f0c030a020c07 67
    0x5400003061040540040b8210707400341000c8a94254a0b048038010002440340e0f9101c04200c120107909042002e50008007407600900c0d18905080720800015030722400480944502e5200e049102c5964980d4130400d600030b40101d802901e0008d8041028040c40429000d40c424090342d40780c0305040d911818030f50342d028000145050341c0d43d03082d480c01c0001032001103001c0e14040d10b0124065004055803c0903020b0f51121001054000c0340c400044072424801440c00e1107a644541c10071400281601400000610484101402e4034045c8001002c003050605554110b5001075410002515182e100008010042d1042c4100c0e4006040c00c2d8050503600b40001c00c11072810b0b00300416480c01350700c840d554569150302400281c90340f4601359501d203907130360000e4012030101d00321486103a1244103240000d000c40c0d40c0385040c50a910243c0d0f003400c841fa8481181c0301350010f260350800a041018a0303210300c01d071b00061400d00b00908178450f140801000c4044560340001c06415030074003041140c00070302d00720f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 571695233 1250 571693983 571693999
    0x20f06070c0b0916120b33010e030609060405120a0e040b0d050f0106050f040e030f16120504050a060201290d020303040906050306130302100c1e0c03020d0203040f090c0905 76
    0x300c040110142d0300e4103040e1030030311319500811b0300000c111b444504048000103a410400e034000f6004040706d2207c0a08906120030103c241034140c41c140b0070140300b81c0b041c0c00075010919240c200700d03003454007000306086240741c201705002c20340350846c0b60141040000c0d10f0004229031113901040c2003481c0710602804511980009201c12201500a00d0698070165514801e0b540b00e017090000340d40040886035150341050100c204d000c1454405005000e260380b41c604070000c01610341d01007100c40003441100007000000e060bc454280301030b5000c01002c1900c000c01526a502c41c0141601c00801c0711200444800395441005070354510311810559002000d4960300c1c0d82d2608490010310462007a103000303000d0350780080c800c02500842803420f1a05a005080e2140080c10404000d04a54210105000c4400c0ac1c1c654840007802606100d1076682c0c44000d140b880c03609002c0d10b0205c90151080465004000a01141c1c02d990001c00889410300004680401d80c4402a0f60041036a00026004006c0e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 571696483 1250 571695233 571695239
    0x140c06070f050d050f070e0103060b040b032d0f0c18010c060e0f2505060a0e040f050403050c0624060708040503120d0f0501030c150e060a02070303020f06070c0b0916 73
    0x114003117180c003501e05522005a65100000103401382e4009100c0c01242c5002440304210755040c520080d948100f441011182e51001d031000f406041d1600c0c130f810001e03003451208020b2011420a40a41c0080b180350f03c032403d00810810702c5009032000c82c1140d042004c0e403401e81041102039009a45640f800f070f016100341c801002c1c5c18554903030b58601c0c101020f0364042031031000300d50400c16000980300081d29079850301c018030b102910002030398001560048c0d0b8035140241ca00d41c203441528015482a0348083d50f845032100044e18141000d0901715151844518411250858414a0f080c024040c0c6a04d61114100d09140886005590219401d8040c10108240c86244c041c0103002e1111048800c12078050040c016008442c004d00004118011301c042c180901c0452101e07140c1180490700d002001040036002044845e003000307000a0159000030001d100300750b0180004810f0035110801080949800c9800600c003d560741400303400d1400c807a01060700400103000810640d8000e0b1409000156 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 571697733 1250 571696483 571696501
    0x16121a060d2009160206010e0c2d07060c031406010807031d0a0b040302061b0306010e03101e0605061c09050a0c03051c05031501080c1315140c06070f050d05 69
    0x201340300b4005004035800441c5800184044a02642114102c0c81c02c080807c002c2e04403a02c1c000034101001480152907140f42030085000f0480207205a5010454807888080601911102190202e502100e1000c0010f00d0340d10040300c0b07a102e1160300d40070030102001503c82c641a245965806040e00841c00701c50244082c4100303950089200f5421282a5661036184050042e00030003401e814810401c04546a5880360803404440d61000301907960304e601b40c200c0e25007118001d0101d084400000808080100102d1184400926054450720b1034001a0000d03a42010104200a40391a40c0c80315110141301d01003001c081c025500c0600418016107074100140d40c0e22070b400c40c2420500c2e035002c00381c1e03019208200340d030700a00001d0345030b0701010400e40054502910081c41d080c0c20750002d00c00c100c0c4907007038000b1007c0100b40c2e40040500c501042c1e10010b04404908440386003a072410000540800c80010b9280d41c41095407070700c0201d0343d8204800b20f400d441503036402440e403420302003400f075060 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 571698983 1250 571697733 571697761
    0x7030c090308040e070f0f1d0a091a040617120d020f0406081f0b090904141209030106080a150b031908090a050a120602090316121a060d2009 62
    0x19100e0003540200d2440449034444410074034400111464490b40e10f0307010485912034080c500805003040a900d9003404402c66a144c02f0440388804000c1e10080e0900306407041d50040d080481e0784040d02c0680518003941c41d001940c0c1f0110366240000c1c400c0300c5051a50503101c9000c44400c0c49a540d0341e079020000c2c0201d030190791581c00340380c1c0c200750036201030140100b0b501255030b0901c0060820a801040040191004205031001852129100c044100c00d1142c04251181761000c107884000740002c2c1400c50362030341c1000009500001d042c1c0085015646800281a020100400d0600302800424140504007407600190707461404009c08000d9010b0241520160507520605025a03482c1006040000c40c881d00d0480142c01c3c0b8601701013000703a0010b150958002d0300701d40c1000c5e4400b19805a60000743d001c0c484100341e803020003040084035040103001064840b4030700f003a400c2c244001340c1982c2141d80000c103403200c1c2410074035640041710003680380180000c045042515015030a94150 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 571700233 1250 571698983 571698991
    0x2040e09030a030f18080d1d16080607140a030f020f03011e0303140901090e0a020325140a0c1a070e03011a15070c060203040f081507030c090308040e 66
    0xc42e007054103201c40c40c100e03171241740b04000032104100a00100c580b20f01d4115849840404005511041c1a0360703004003049255105c0112400200301c1d880700000c854080c02c0c038540101071150456024081640c0d8402c003c90080c103c840803d56807254141c0c4160000c14900d070446c00c01600100e0840608481040918100d070791445450716038001e19140050800524080100864281210306c05100c00c41806130001850605020841270341726510510204412504412020340000800c00d0303d01c4d201203032814544003083c044000441d01b0801800c0703038803d080e24080c021000309103802c0c50780c07144054280d82500b1000f92400d4680d14840c40741c40d10011100800801c030842d4245a650034140708a505640e2007200c10030f0500c10344030070032040d0580032016481800e014804030010540f00b1244000519040c0c000310b07036075442c026400b01c00741126801400e558120b54070812842c00c1d41c002e4650710403d91306d000504090600800e80b040e80060f00058034040010070003090300810425a1401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 571701483 1250 571700233 571700237
    0xf080d0306080102120a0f09050102070f060605100509090411090412030b01090e0406050714030f040b0606041511120a030b0405060904050312061c2301020a05090d050102040e09030a 80
    0x2219140c40e07810742070b40f0901c2e41c02d9101a00c0100044c10b06c111a1307015400300c14031444041070b045219200d09099070401d00e1300b070b950040031041442c2005528401d401c0140400c0d07500814001c040b0b0f0000d40036000f6000e07003601960403400040c04000c22200013060b80900108000d43c00c2c00c0508102040b8801c02c195140400c1c42c00c2900d81603980542040800c441e449001c2000b9590340d41e0300d1a0281c100941074034103102540b07034802c00742140c140146211b0510700182c94428500f40c01e05200c1c840b030107011035028900c204000d00400304500524a201c41460405894214030b5640e02c42c0349c00d890f070221810f50600407400c2e00c40c45516030810000369108403014081900d0307103010451240400d660080040d0300400500910403a41c88441f90300000c010854001c01c1004e03051480c40c11100c0c00304494800200b5000c004a40b01d120042a030410900003c40c02c0c598407042c00340485c403846146a101329520159801080002d40407a400791141c100b2101143c1429000d0961300c2d04404610301c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 571702733 1250 571701483 571701491
    0x3091e051204050312160503070b09010c1b26040f0e090d0c020112061e061d0109060c020a050402070605010512010207020f060a030b04090c05030d020102030f1501090f080d03 77
    0x4000e07448041502c0546200030064207440e030309101405155800506642c0100d4842004030020500034009402c0b0b02c7d000e11002606450700c0c02c81942100c83d01000d01c0300f80000d010000e00001d030032401c0c000f00240c4c05101a0445041041a113541c00602c1c11440752112000602280b00900340140c05c2c21241d00581039103542d25441505034440c0d034001c241000158107103910304090341c480d940c00c58001462060001d103440d1900c003940c8140006400512501c0d901603010010568405020f1309030340d604e03502c130311032440740e4600003480303810326104000412114244000540d5100b884002c014200100f08541e14229481e1080c05040244540d920403034244040a4403a4010300840b002964000d102c11040c00500d41009180e410004040c1d0405a42d020705905030384944c8900f18085004d0b0a024000c21300c1c0100700b41c0380400224050f000c590061041c84824041c00d5a51341c5c00c0f242c2c10410070844c0d041c0c24012600000f0315405401425880c40c00041d0b134900120b07200050086941d0140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 571703983 1250 571702733 571702753
    0x80702192705160c1505070203040f0501170615040b030f06100f0c03031d0312160923030f03070b0702120703020309130b0a03050102130522020a03091e05 68
    0x800c88904465203040d1840b000500f10300f1520a0b51011440703032240007010b4450503030a00201c01c8403c1100c444015910000c0d00b4070041c0034a0309101e000701001d2130060800a00302d103440e0080c0c2c0002c3e02003401548800007a01400c0012004c2d103019000045000d916403800d41c0080341c800c031043d01d103203004518101000590b00c2c85000203120b42c000e45e842d4039400c900c451380c0031802005c964110000c141c0100100f41c448100c00c1c0000c0180f2a01070044d1621418100000325800c0c036030401090502003029402c0013008a0034101042504028440c030010f03803c02c5001c2030400d01842d24a943c1d501002451104104d85000c246001d08203542c2125221800c1c1c407082e81c01d40c0300e25038010340942e1003071020408a103441d0448002035001d4000200e150311001c00854203845158104440d2a500481c2c2c078081c1601024029008050407240c000120803103040707010007464a50300f503000a640003d400307107041c1d0107500040403043d44080c642c0b120000f600d000200c2010191821180c0e405000051 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 571705233 1250 571703983 571704059
    0x4050a140603070c03090e1801050c03100b0f07020603160f14180a081006090e030405090402100c02030a060902090a0c0e12011d1f1808070219 63
    0x4241180005448a49140c0303500030251011800700c0e001700d04003d00d0705004078400c0204039010b400f42d14584c200341c8110001c0c80c11542075600007402d01602802c01d00800c0a282c00e000d68550859450302013255590707080c3d13100881288075000e401307500802c00105000f000e42c80101d402c1320f03c0d01c1d5607075074103200051010100d40420242c100c4040b0100188021494000a03404249e0bc49400400141440d41e5070803082d420f02c2c084541c130001e82c0303941d18000c000c0d2070294000c0724940001c1c0c502440c50182000c1c000740c9100005031000c0d0164207039420401340180510802c2000d02e4004080350b0032107400f894210007402c0304080132402010504007040d03055103079005456000c200d0341c48501c0c03582e8003d01400801442d0414005180d07480e004840340b110b03141080c0c20061340d22000900004012100300505000b008210340c520185404064030045400315595903850707030310600c1710340d07aa8403d000061070a01d005030750032400c4089050001d42c03e6080f0415100e00a9076000300300d89105400b4030307 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 571706483 1250 571705233 571705259
    0x60f040201080103061805120405040b030c090a02030c04030c181109030a0b130c08011505030604050d0c03170709170307020102070e06120a1103100e03090f040f09060204050a 77
    0x80c0401c2002c2c0c01400020f103907800c0011041d801500e80e4a0704041612400d01d0300d00c403540001401c5400080c240719504150050006c0c09000341e000304440c114440118546580040c20301091075404404910300c004940100d07401550000d0514101d107480b41c04195035103552145000140341303040c0c00c00240900c0c0100f55031408000a01600c0700560350384403c0000031004010030700e0301207808407810000d4003035103241c0050309000c400041c0051420368000000081600002d01ca580f00078100400a0000507031200c03c1e546e030341740c4080301030241c1ca0705403950482641e0149611802c042049980c9501028010894690003801d0002d8040403d00c41c0c2c6074031030200c001c4e005070032a950031302154501e01c08150b00000f002d41100071100c88081d41608280e24000200c40d00305009410480601c0c0c03c000d080410600a0000c01c5107165825240759a4880c680250307029030000010302145035034640c0310300d15194032a8010b0048042e2850494001c2d0321038081d45100b0f240d03010300481d03100c04e0604 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 571707733 1250 571706483 571706491
    0x80d0501091d0c0f1306080303220507092403060b0907050412032003031305250501120603080408030c070902130e0406060b0a1e03111c2903060f 64
    0x101a103484810b8038140003200401c02139580c2c00401e0308010704410f4555101d00f8005101c130b20051138480c00c0460101e030345c05000004924140f21041d1540700825004107048c022500300b004005004100b0303169504101011008040d07510751840000000d01400b80c008401902c07044900d007201d41d952600564013400b032802105e2010120001e600c0009025a080ba4180306100074200341c81c07020414440e182d03034070486401000c5943d591000040100400c4010480041c44081001490910b0b1641c90011102e104050411543c07048000c0100d0050b0301c820055500420150703074450711040800ea6030b900c03158a0701001d01c588100012525482e100359540305400343c40d0800c000d880c00380c2c030703180c5180050815a81266202800500c04071600b00820600c2c0340c81e10b03104120000e81281d03000d05200224107806041c01c04001100c1400c011041301c1404001080b01034102d2908911480144031000005074038580d54034014581c188a4407501c40521740880480d082503403604c0c505031003050280c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 571708983 1250 571707733 571707791
    0x150907020604120f0504080703030e010f1b0303020702061204031817030a200307030305010e0a0b030a03050a11120903070819020d030c06050f040b150603040f050703080d050109 78
    0x10741c0303007150340304122202c0484c8080c909207003400c0c1c0b5222560305010300340d0f001700c000c5040554100da00d0b581115072000081d040342012069029003a00c0c042441320040b500908156002400364110342d1184142c62403404082005003803031034149005000c404011124150491000c0400220b480340d40250f0b00c10303004003402850a11171142c2094410004480d000e0b91241321245965000749020070140c543c05001c8ea801041c1941340002c42c2c0750900c0064035110b00182450711001407610005080d480c0f865142c0b8007155100711400089413201d0700b008016034540500c002c40344168561102801243d54202e0641d215256200740544e0b590001c4205001e050102d40032140141c940680c944004c5802410034440040030347d8ac8002c00c50f0b1044070750400c1c3d01e10341402e0206015943c010300350b000d6951600f0001c0d2010303e01c00200380f4000203000425010000403090108801400003100a40d40542c3c90b5072660b4401c0c07822000340c2401d000b41d4035858a4650701da092004030f9010000950519 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 571710233 1250 571708983 571709003
    0x120e0723030a0b0405120d1a0103020c03071b05030109060501050f0f0a0b0d02040b03010e19181e060207051c0207050105030123120102042d050d030207050306150907020604 76
    0x39920300d041c0d00b40003130084c0c48502860003036204d045610002018003540e00003001960305004040d203c580c0742d902250504040c414403090345a881d00000b118001504034030030040e10310b02550815401c000e150000e6415508215804040003199080b450688000300d80c104d00e420b040e1418061210244c01c07200741d11104e00d21041100e403900d1001413140035221030000d85820f40b1101d201c10541d0083c1e0007413581d0b1032007100f00000240f00c64617200c044006900f0612100003501c0826801c0050194068400c01d0302c01c0c140320180100080c0c824043ea8400010340d111095410315507103641f0300c65007003000b0800192082c49260b1000c10bc03001540c005844160859003086194030a841d8940d2050341d078500b5240c112410341d035880e075400000c205100009603540b81004030b04087d040b460b403070098003c9210b010794150300159040607401e039441901c501040402d00d080403450084c4c11f500183d014000e80080c8254040d848440718036650056600000070740706d0b440201e0340c80900301d601820102c41 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 571711483 1250 571710233 571710253
    0x30f060b070f15020702061602120a050607030c0e0a0306020703110d080a050402030337050408030405010f02070e100e0115080708072304150504030c090b01120e072303 74
    0x3010010110301852442d00506000c0300746e0106a03d42d000c1100981c1c00b9508082c0d017021807510508044a480691000e098561810ba80b056644d03480075104e101451b4848502007070052143d140003440000007020b00203550b07901c4c2010b000a5020103800e80000364020301d0300c200c400c030004800c09120301984c4d03440c0c503039524401410001c00f0040e04c22030b45404204010440c8000c520f11400101c07034040854280104141c41c05400d00c102c080104040c00b40c14803040040b81008016903084070b40a080c1180b1032292a0342c22420301d41250444640c3e00030323440034007060030000c0d40200150744446000c0d034126600c030401ca0400452481c102c4001801410004140364852a299504050242060307215101400c000b00b0003542c0d1a1a0001d000f0f902140800140d00c40c440600e0803100d950038528038080c2583c0710380075a498a4010400c590351100801c0d06940d21448404042a188400c01c00008000c94290358442d4842c1c0306000300b0501e50281200e20b0601d158102c0d034201c0d0002c0c010260104 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 571712733 1250 571711483 571711493
    0x5070b04080706020325090e1803070b1006090f05061c0b0618040f231f1d06010914090402131d0106060504061403060d0203010c030f060b070f 63
    0x80040040360002028840700c000107901d400514005ca81c0417040758608010321807420344542c03030305086100300f295800c01000300b00c04170822160003100070710380c1160780c4100705240d0380b551046400003016030340c4540c100940c1001040030101607603050799400c0b01444d55980f0702c8221151034012203504c00300030400c1060040718034104454680d0b41500c017003088004100002c6003900034031200d890f2550b0381d100b0800700d4680741c0b19131100c2220490040092038545142d901e800364040d40303110301030b00d0b10402080407800344845002501038100c40752100181c0b1080011411144c950321800300701c440a000c2286503000d444d444044e2101024000070a402c0d800400042c02c0000d8010707604030040c0403000e8510420360050150307a00e0503003440d0301c284011251b100c0c03c40700107901000030404107020a2000c079070700c140711400d10003007000055202d0b00c58900280143c1c6030b00034025415072a103600c6a0840b42c00d60843c0394800d461950401c0b4450b603c60240300e8502c12058002d1004e2005500100021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 571713983 1250 571712733 571712753
    0xf140103060f1214060108012307140c1504030c050d022b090b220602010204030302031605010e06041b140609040c0c0f05010f0507021515061c0e120a0507 68
    0x42e006900c41000e0304c100b044041c1c1460406c0e00306817142d945a14000d40c00d210600c2c281210600d96070843c0903132b481c1031328004019942000c4d80c0c0c0582140001d11320b0a0542c20003144001031901140550309081924010b00710001700a0121100c3c0100e101c0940c00300e002207802412030610a8000343c202c0c02805113003440083c600c445005110181c4004070715031201c130029210201c00d046c0a1210381c48444822050103c07245d00003401c584c0104414400668007005440300070391800f00341c0c1d030180118a842ca01500d1603611000d41c43c031502041000380155050340720180c40300107881407011503c03402c02803c0c841d031400c0c42c1074202108012203141410203501ca0b128640d51882e000a0b40740360b5a4420400320b02da00010b480713a0703454016803c2c4501c0148279070754000c941d600080900c0d80458070050803c89004103003c42d42076a14a41103119200c0300201d0380707925103202c40d481d07400080342540c030000c00603001c3e540502d02c114404802001c0c10030044490b1200540c48690800c12199101d00d01d00e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 571715233 1250 571713983 571714019
    0xc120b03031206010e0312040e01030303180c0524181f0e120c191802090d0b0604020d140a060609050102100e011104091b032d0b03070f140103060f 65
    0x1403087c4034900034000541006880681800b101c250303015455030034000c0c161022007440907004040340d82d1990003d500b00f4101022610143c032100f14102d00f0b0014800070f000301c0406455180000142d0142550f080b00703c0a100c0792080300d07980340b280903000300c8000480840303084501140c260f40101c20a031a1071150901e1030303440300084500840081011848400e2606002c0d001c1400c41d417024050a0004213020004c00000982142002340703030000107582001500c4042c0080700085d001c5480790b15a0380444450f0381908900740580b0002c082841409042211000d000c0c0f0b150540104103140308203d0341e012608168018a41440c42c419400300800c010181900c0310341d40c80c005003c280c3c00030302c040c0c00103000c10328001446007a98130254408100c82802e402c00c044c41c0400c244000d201d1481c90101c00342c5aa0404088445601901e40007040c00c0c10f4166814860990006800304040300b40d001542c40600b07224140990420043d03003611040d002d42200d502c00080180010f05d84000c02081d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 571716483 1250 571715233 571715239
    0xf060605090409050f0706080106090905060619020a05061005090603011b080907030b01060c14061b0d09020d0c030c0803030903030105011d1302090307050d020315190c120b03031206010e 82
    0x4642e2503540f1b16040c0ba41d445400841c021100412040342c101c4a40c1c0e004010381c49052166207028000140c4038032500310400e889a0000c0c400500a131320070044101d40035405001c0341c180341418031070020402811300c100340c07007207020000182c4182410b024105014800440d94820848458000d07290110002c0c0000b146115281000000c40c0e2140d10780c0f40200360380d4a44000d03440450914591186240d1104400d80d40030100b400000c5c2184100b00b40d001d01c142020f1500c4554201c0312002509a0343c9000c2c0d4000d00402129090209401528040382d00c11b03044140e42682d40c441c2d40c0d84a0108803001c40850304244010031195005003800d03100280c4044a40003203803041030000d00491504030052080a034040740c0164242410080107001c1c110803500150303490302c01e40c0000c1c0d680003058040740c610300099011a0b0503c00204c4005146c03140070000b07101c041180c1200401c150003011003610b01e80e042c64a42d402720300f000b004452603004816540042640d8100056615600441200703070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 571717733 1250 571716483 571716493
    0x30306220f0b0a1203080408210a1409060103110607110405090d0e0a0509011a0712030c0905040908030a050c091008010f05010807021902031612060f06060509040905 73
    0x804000c0ea44259001c1c40316101e00003500007000b800f400140800c070340003804042c1030414040d0129030848440c644c01a030000f001c035503450840d410440440c25101c150311415410ba0180641041182c212800c2c50f1070081581015540d01040d6603903440f402c0c0b00c0a0a01c2e0070401b80c1c5484e9041000060007140c4c0190720280040740c800011500302e500454880500b908020b90b04e070340440d4800400844500c0480d2480c01071400c12002031004001845134040c0751860b40d4a1360b050f9002041924282600441c09080d60703049008058007421508258800044000b138000c82c03186024410b014070240c00170203181c00d503500d852001e0300a14000e0020928a01c050181c80200d944d41d4040a000c000303156250b6410354540004421402c550b80c10033414800d6000030031440e10782c00105000e0b0f0b00395500d6403205003030242c00801c1c20254203424084000d5030100004c01c03404d00d90f0910101c03c0c0e00c14101000501030141c40b0008440c203c0c0503840006000b00030044c0719241c250040c5040c94040c0e0300f911 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 571718983 1250 571717733 571717789
    0x30d09030818030328061d06040b030f0d11150c070302011410030303090204150b0a092c040f0f030503060108060a030308010605090604050a03240b0a2714060f0a0503030306 76
    0x40e0b900401c404005240386010104861070804d8022030b41c0c0610245e00038642d4cd5900d00405450301b50b0051040c041042d606020601c4c0d400400520f8086800e07120b507204c89003040000f0421540c0141415405903007413001100f241020301c01228807589880d0030b09041c2c1801c69400318041c282041c416079100d500c80066840702c3d0514a1480c0041c84140d00044e6100003089000d03000f0381c000d901043c542c034014101100000c84081185418000059040b900ba958500c3d02d00d291510b010000750400c2088410b40b8201030308400114001d080c240c9a402d840d17a1050200502c1c24406d02000380014820801000f100b400340c0094001c400c0010005410241c90b00b01040c20010180d0042e507045a0912880b40400212841c8003a058400402409182c40036400309000002d9480b4032010040b0b05c04c04050f0b0100400030320728145840440900114101c0c952980e608401910720511406102c00e5140c3c01d442d181d15400100c82d4058065415907a4010410264400c002c030700340700c038030300000c1b82c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 571720233 1250 571718983 571718999
    0x91e0a08012306060304081308030d0603031737020c060708010f0f03021309060903030603023d0224010e0c0f1b030d0903081803032806 60
    0x1500a880c0c403400020302800007402c182c1c0390104214201c54081c521006000d81d0303440300c3c0b085a0788180c100450f00d0b87c4405162101043d40e02039440070005000c0410b0141600c0c80c0c40d0000011a8082c1c1e647c428210002d0710a03101c44482074460005517104079012554100840d017580305468160005d840f0f42403002c295a500b603a0142c1d940c1e8442d41c020358100007001d900402854090708848a1001085040c0700524100881a000282c031500c45508080d2010300b10740c1000000561200050042c10881d00d8050064101400300f02c0c0310313120703005841102c4d9008080c040300c2c1c00f0050b0704461038424555010001d10f0f42d445a01403c500440c9080811070403500761214030711400b202c1c601503540c0b502700b94503c6406c0c05040b003003202030200010302d85a0840010744910744402080304020b0900b4001c02851449490b811400c10340c10300145a0900d40c102c0c0c0c1042c402c1c20b03208508907510841c00e940c1074903481708403501c050141c42c0c180303103540c00203030b100c4610602c455052001804548038411 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 571721483 1250 571720233 571720249
    0x9060a0806120a0f120824040906020c030702031c0e040b0a0e040302150c070209040305280c0b18060c0318010203010b0a110f0606040f0209100507031b0206091e 71
    0x81544c5040c202c88214003007081c00707030307004000c01a84d00d8100e00605080360685115409403040d4107010341703145c80081203030380c55521284500382d00a1003199240e59400500340c503034000200580c0309001d208000003490040d00b00c42038520596649140014032040308200c014543e011410b90000d2811801240c0e0300d00c4456030500640c000c1e001012b02d54041c0c9a071140c2280b00400301012080b0070b000110058658102075a002603043c00c3c80c6450b5010002c1300d403070002d50203220100700540c0010310342043da000094500030a01404800400d555000c111810a1003810003807851a480000000c1640d07500d04055504205014180c0303c0b0307180c0c03200da00d070309907002a0071010402000182c40ca02241e080079002d10b0f840500c40103841003002007c109030311004003c040360301868076211b41c803c41c50321940c100c030000b4074002d204035030032190810000c281d90081c050072070200d0016140200288504069482c21650003400d45e460075041d4403e00030b0040559100398003200903001c030010240c1d641d00b9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 571722733 1250 571721483 571721503
    0x933040203101a070f060b040f090803270a11130e0615032a0103061a0706050603070b0703030c092403110406020c150909040f0b01090209060a080612 66
    0x50080c0e80c1801c055450781d00600204007810303014820080d50b030001e800c669800d00221b8029a0015801c2d207803901141c050b2074100026408d40e0700e0030360a5001c02628402850280c4103d941c002c480c1c0000d00450701c0000382e0014410096030102501074001986020388403851800034003919043c5840700641c0f02650b80245403600d003070b0003610412150224a40c074800c04184c04400401000c00741c5030a0080d042c0c0d101249900401a411070010564000c4d00498000c251151000d0310001100701d289945421081045508909200101c0c0350780c40c0020303010080e1864002e070140350150703a1b0340079002003020210181c2440280750000130014540307407450041d52002202d5240d0f40d00c04200c001d00711140d40c0640340822406000501c055640050f001c0000c400c295991060040400e20020305401140d0f441c660016440040204129000c001c82d40b505200e89203940c040d0362a031444c04d05134040c50404603000402070024a01881c400d80d44160402e5024101541028441d8056818014208 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 571723983 1250 571722733 571722751
    0xe04080909090604060b010f0512070216081605060403080301120312020c0321010f170703120c150603082a030d0e1c0c030c240608010b0933040203 65
    0x1c02042c041a4061b2001c403c40900c2c20fa1900c4036070600240280c0514255083d02c1d90795040060540d5000304000102440c07510040c1e030519070b035152010317030b44c20220b05e92142c081540c25000441d8105803051740c0c2545d9020007000c0c00d603070a01c0000c42c10307600180015410001003111110303280d01c041c40100080a4010080d5030340c1c20441d81c3d144540d0409143c0c00301040c0c90000100000e11007188101c040c0c803000f00c40c1c1010220702c0d003481d80c81e21841c1d0300007030111410701841c0a80250882110084548a0000d00e0000308910001c001110510312002c0e065071800c202020381580181c4c0464941c00d004200801c500c14940c00301441c540100c1119500595501c50a400303061f0100082c0d15807484c1e055a00001c07208002c00140010b10b021401000e00000001c00000c215200611840300040140c41114140c004040a170141c1034521422100d540b03486a0314555040401203e03110301000103d1800402c40e00d0400c05100c2c807a102400d01110040b04d0140b1541e0301da00085001721120 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 571725233 1250 571723983 571723993
    0x31615020f0f043204020c0307060c02060601121e09050f071e0e041101050c07120305040614030906160c05010204030b0a060f06140304030e03100501090605030c03070e0408090909 79
    0x1c84c80954460104424807007a1448880030195035100240e02880144190340150300e41010300c00c40ea26600482c070009084c3c0341840107801e901c581c001070051241001743c1e50f03440b5042207003600508074ac0c07a0420001b014a08035643d01d148030234541190760150b21030822502c1e00856002018201112078000b07000c0c1d14540035002c41c0400a48007080080e00c04006007003090b081551361420027a880c03600700c5060100106848000c02c1d41030000b00002c0c400d038507c03180769060750b14009117070b42c0c080d000f0f1380c1c0420008000c041c2c000131444142c0344607000c00002400651651500c0c102505c0c0381104140030030004c3c3c0590780000c0c20a0024100540c81000d04000360300304102c40ba003e640450b0451010044888403c2042c250b0040800c100107008480441d0b0b40d407582d007411140c0600d01400030380c051140444128000380150b1205049668030f00d0104042030710b031010580c4070818880880d030f05038480788090080b11200d00300242c10522070700c11036140c986403001040078103104640350400d607044 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 571726483 1250 571725233 571725239
    0x20906100f0332090d031116020a1e0501171e0402061c0b030708030304150b210c0427060f0f090c0e01120807061d060a0b030f031615020f0f04 63
    0x3000134200c40c1d025411b040c41480d808610002c9540144001401941c06007440b5038155260583d00d01d000d0494154541025410f00031410034014140c030035540003812181d076424180c05442000380c00303600c0b00c40ea4602d100c44010510404441c0c0a04240d03406407017002419030507000c0210394a00c09400150125512003100109400c0407810380c840103040c0c008004001c0069030310001d000002d0450700c1d0019a000b10301c1c001c2201903501c1c5440441c0c041a051010031060030014001c415100700319020b01210b803070f42c009400140c180c114004e1403600c13100ca0030000107292360005981c1c84089100055070000824810082d09c000e0038080d50401c042000c03c2c00203009481c0e9441c0500302482d00365480e51125510a4103074825094094110b1307541d05a4500045400008010515015001c443d0141000c82558000b0100d10005e980300b882171036501d01e0140404015118090362681d103011564078140c80b21007242040c182c2c4180207036070822201032502e442c0300140c459042150000303510746003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 571727733 1250 571726483 571726501
    0xd0b0411090115021212010510050d020f070b06040e03090114130e041203140601030902040e01140a0b1815030712030f090b0c070506090d020607050307020906100f0332 74
    0x242c0f481040c0360b140300030006d5241100d661200ca42c11101c3c2960f106c0c4514002405c11176007405900b500c105102d00001b42032001c011210041d02010b80102c01d1444e03192108000c01c400c40304013400504032a001404055620760203030003400b406ca8010400c10b86440351081c06409000710680010704801c402400f80b105000b04407810300d0910805050800001288250940c0303407507001081141010f0703c0340e515074115110340d00040606c1e101c0000074071689a00301c412100c5a41c00301c407000345c0d0624050201f0b44603d0324031300c000401e80e500301d1800c000d61105240c020b61030038076100881c0c051040780320008130101e2001650340c03481d001e5031703401c040803096590041001001d0f6100341d000c0c60050024000b00780c4046000300440b2402c5586d5a9980020804182d130320908600280d0f00560114041080c041c020008154003482207400c1c442d00e5844404002c50150707c444c0c440001135041e407282c0790380c034065481100d10199a43d06214044401005070840b030308600c2e07008825200c51700034018005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 571728983 1250 571727733 571727743
    0x2710020901050d060e04051c0801030b042a05120304030201080612120d020703022127060406030609050c070c0e090a0b09030a0f110d081003290f060d0b041109011502 73
    0x4255000c00a00812301110040c0100340c180400f80000c1c031110041000c00502c42503000500e403019031500e4141402103180545d00300d40b842210302400e003401c10300c1001000030080f90b0a0380da0503190702480d83c0303d038014040f03403108003030041040344144c1c400088840c0c24480980b104c884071000150380c85100e0b103402428200300c001d40c0b400f0b4140d032100c2c220504c044501580d000c0e000b00160a041e0740d8022009204d070780d201000c2a90040ba000030040340d420382c160131140a03140000000e0100780c070340384075034480c901c0f0b50700015240e4160140c06024110400c0d581ca604080329604a88403400c090302e0b000346c04002075552403442d60000940c3c901c51a0044d209505400817030178415400780000d480b568071071a624a8078000c000b925400905848950843c00c2c02a5422903440b00d80781c030f2402245040440743c200d250b1042c100307040004401d10340400c3c2a61040001a2440d8900a107954421841d1003025000b10344403000e400c4901955125110050300801486581d20000c000400001e810a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 571730233 1250 571728983 571729003
    0x5060c030d15060c11010306260f0c0d0f030203040302030607080f060a03080f0c120412170712050a051b010203060a1409060d020d0804030b2710020901050d060e0405 73
    0xb0680d0034a040210b0790b000700c05070348065000b0b0446064480003100407002407015800108070364080300d4803800300c10343e0130544528000d80324023100d1000d10846581d0f5600e103000c500450388103690b031110b80002401451390f058414400d004407400d02e6140d90002e810080300300c1343c40000070f030b4040c10020381041c00c201d02600000151a034695407402c40c1c0300e0b4800c0d8415480e086813105000504000028020400d5043c1100751b0811244c0713032519824412308055007514256050511030808194560b408000c84a00301e0340315031500b8107070785102401d41d40d54000b8800c050038004203100b091000b181c50f15030701141541c01c40005035646451030800c1480a0301da00410403884540c062044a511040c2109405c42802c98601854501c07038400204071a08100004048000c042000408c0161803071040b8007413500c49084440600c030180c0481a4500340161040322540302c2c02180841c03844940c01441c041806242c402e24201061190806840840c5c0c08080712402074000c001c00e1002c14007218000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 571731483 1250 571730233 571730261
    0x1c0804020f010e030a0b060a05060705010e0d080708070c140102031003031107050904060b0609030a0c0312082511011d0c01030b0612070c0605130209010b0408070902030a0605060c030d 81
    0x2080050042a900c20b205c100080c100c0044102251300c640e00c00c2d00007402008020000c580e19032a070701d403d60282482c0c0445100c24428803000203ea1402402d2480c0314000d203907104040c1d40d64180007201d2100071501d0a5521501301d501100c1ea10b0400e0008600c204401c00d80a0001c62440c42c004180c2c400c1c5040240705500041403d00443d40ea0384007041e0003d8008501050012060340010080c0c4038203158641c1c940304550240c4100801d007188441181c0c080d2400d00c031004445041980c03c40411214201001850660504401296203003000c86000d14a450050640560340c000d0071103020750200c4400101c04100803409000802c8a003000c11401e2a051081d020b9050108045001e010b0403803400b400340c000000c451034403415a036911590404000d00c0941801c0c9040200000040402d0b030040e94003000116418010104860840d68028004e00c0790900e0002c030030009400c003a2006055a440700c2d80007900741e4a10001d000c160380b490010b190b5990303108880e541150f00f02898410 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 571732733 1250 571731483 571731497
    0x21203041809020f0415031406070806090421091a07030905060a03110712020f1203060409030509041d06010906060c06020d0912020105190212070c051c0804020f01 72
    0x202988011864808000080c03001044040b500c0c80043c18149a0b6007000d6045071078802458594180c80c0d00a6049a001d102002e139807403245d420b05501c1e9078003141e160003c42c440c503020480905100440750350042c0030313048101d0060442030544411040c104d542e080041e00103c0140039000740c1060300c184860010540c9854845c06580240406680744950782c4105804a05c0540309070003034103c00742c5243c902c0c40700c40d130310401d1f0702e03142c030810a680321100014400d85907645044240002c00982c4400303010030700da040d59119020417025062109040382089400d000040081c2c58901807003048200001d0400308034054650b403985043c5050b17000e6501300c0d0030490100f0803643c12640001d6503d401980169444400e00301440241c54180c00040c0f40100346100d491402da4194440e41c080c1c074251032961002c03864010500d09034090804078508039010100403403019400790503126041441141550411422a070300d103440d40c4044201c490209a09204001c01c528010300000700700902420504 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 571733983 1250 571732733 571732739
    0x3050913090210030e0f060408120604050f012309090607080c031315060312080109060b09150d24050a051002100b010302090a09090c0f03020d0605070302090a080a02120304 76
    0x9159480501070180906a80708000d00c44010181b001c122031004c0c000446441e03040c6460300d61002d60010032082400100c41c0302240041c85d242c0139076402840c0032414940c03c0e900300303e16002c620706000503845641801202004182e110144a54454402c800142c459481c0240c00506550402404803011210400c00c0001c401c94081105494a811801740e1030700c9641820300310010072075508050710b280301a400d40884654030661441c1a42d1002900b403216a5640d400043d10307014021500b680845c040015042c0d0884000103441d40e00d45205002c01d40e0040c60030484da0081e100100301d0301c000303400b100a10003070902c03c0c4803400420341554141e141034201c2500940701c00c4e02c0000000950b49411049069a02c6901030352003802c0d000b4640c14265654803450001404050000c943c1103003412000680021201002c00442c0c1c0c0107000c441c000180340c1d4442000b008000e101000340f43c5d007480500002e40351500780d00041d00c0d004d002401c0c025018010070a101d54504400d952a50082100f4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 571735233 1250 571733983 571733989
    0x614030f070b030c16080313200a0306090206091c03030b01050f092101020a02160b0406080402130f090b04020f03010506031c02010204090c021608010507020d110c0d030509130902 79
    0x100e84c8075030081940e580b01e01e040131140d81413880300d50016020707030008403e10000c601d505180b0722101d8400e0541c40c85034882231004001c6d04041200e06588000e124204102207a80c5402c02c45800344018541490301030f07040c0000e500c0016150f844403a20b204600c0030810107030144548540f240d0300b400c00d141030440542c0c80326142d00c2040603441c001c0300d00040d240c00f10441c5031854030010000c60020b54440b580001c0007503070343c6405004c0c0100c9000c41c0c5000654500b080c8200c0b03044e81da995036000c2c150360f515001c0c41400441c00b0100e00d2502e503500442540d600b00792003000c01c02071142c920f000040c00c0c10f00400c0a0351320b403c0b03405440380e45410148016554005404406020b454041e90225100a0700580c0207020382d40c01000950b0030031080402e604c0d03020481a00e000508000780540300c1e00d45283d1400ca1700c0417503800c1c1c0075901c0b0919062a450003404d55040e13407000c1004848420120002042c1113001000041340450f03008503540301189842c080c804458085020708003c000c03265000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 571736483 1250 571735233 571735237
    0xa02120601230303070203010e030316080415020f1608030a0b01030203161b080412050706020f03180d1209260a1e020d081e0327100614030f070b 64
    0x6071060402c0c040c0e415261a4030148140c0d60b409400070001c201360b5801311107054580d48110f425035904a58a6195a485401000042d006940200c841d24031064401d0702d44e002984400500d0b21162014010300810b214480b04100d4200c3c450356a0340e481e410140350304010340d000090881e050600600c10802941560001048054020301d80300407804080281e0000e80d10028074058401080000c002c140510441098081d040c412011118070540d10300040382c0740d20803605101000c5c0c00410404103a131400040303200c03400e040181030b62180d01d101c2c0c1c1c1d02d4603101c20400f000c0000c00c840030400c0224142e0010030f00b0741c1511000100c0640409004240d40302c10b01c0c084001d04ca1824042000052840c4503101004564050b011049c20015800d10166503040072800422031080c00c00c04000c441c01c68403d1302e004000250a101c944848000403d540c078070a000a42620712548503106402d22030fa000d0540103005c410300c0c02020354404030505041035035860300b004880d403007040100a08071036141 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 571737733 1250 571736483 571736519
    0x120f02010b0a061d150d0603050d050910180e07110105070f0203041e030515040605070e0108070c140118110d030f080405030c060705090102060f040c1206020d0c020a02120601 77
    0x204a2002c007250100145c2490100300c002c070b0000d200418070441d00346c8280d0000c8207690088044804864124504861038030801044503000240070104a120a004903d426030541d2605c0421540d10b1311000302e5079910350111048000a294018030804a40080c8a4903410141924000c00ca80f40071040c0070750349120303030b02c00c808510b0f000042000300304e4105000389000c1c551103401e49038480c8040c1c10406148000752400d440852920f004500d4660141110003001c88040e1205101543c61040a4030415410502503507243e10724030080316124002c3c4034100864202c3c00c8007440d0341400b0308064800c0d030500c0500e1030007030700444560000700c0e030454131005403880c0c1031802411560f254601541107000b01c01400b000d502c104024405d610380c0001c00b60614005c03e81c03c40720190344003420380620801c2503070003420007036140500b8040c21410146089070140105005454454810314807003c841c421242c940050700800644403c614041003844140c0744514004c002c80d50501607084d25281d8154 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 571738983 1250 571737733 571737767
    0x6050307050a180803270306180f0d020d090504060f0e070c050106141206151201090f080d0501060504080c01051803100504060509150a0b0d120f02010b0a06 69
    0x4a104100e052080d01c0c807980e94070070140002d0b41c441d40c803051103650b5001b1398a1620822440b5a4070644604c2209021400200050051265848030390148421506021184040380a8400c01c0e0017031004c100f20032200c1a940780e004000e0085010401804402e060308020702c15400c2c0801001b00c40d030388080301010344610340b80d11407580c2ca400800313407000050039100030150b508040c400181c02145a9041c0807001064850501c1114042ca0140e1201e90464803001081259110700d4014107043d0051541c4014000001030b5001d0306403220000c4001603d4111144c0d80c002503001c0b220360407805414014009810702c0c2d8146418031100c59207900408140904204000c2505080c03a12491030111910704060291048032200d0458000504000c8600744e03581d43c2040c01107410f0403400140c1d400c194904c10500c4040752100e8003c80040c0041d003800d50303407200c5c10030491404549812000c1c180e4070160380718055104a180c00c00783c25985101c1502d480342d032080404101d07a0b0307005241c0800c541c1c104 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 571740233 1250 571738983 571738987
    0x41122170c1513030308062b0609150e010b0f010207210305130e161418030a08030c070c0807180213090614011e0c0b0c0909100306050f010605030705 66
    0x6186006000f4074074851030a2101420000906401101c0d0a0160b8020f0b20340c1c42560011403140002442d03054140350b03101c19420500008200d4640c40304407400e100360300343c1700a000c0280c500c1040d01c01c1038000c0d01c102e035512107142901c0c3c600581c24403650340d0280081e010591030702c803500518141c0c15065a08440e4824900700806103c0c104a444400001d150501480e46135040710f101c240d0110340040080c15880016080c00c6c2c00b5003165146100e003001c0441c508540d412050704030000c0e05085541610070382c2c0054000500f5840610b100b804940c9145480c0c1840c2d04190744914a903501c650155000070001b03000c0e000d40700d00e0202012160410160b9501c01c6008500c0b4915065030040100c2403414102013801407a51491624450b02640e4100305e0350702d540310300c159041c4841141c0d004aa0110411400651221462640410440310090a250301c4002280c0c072060100c42e0081e124600403024800c125543c030849402c030020389809200c0d9070408002500d6440090100d1040c0480 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 571741483 1250 571740233 571740259
    0x220e06060403022106010909030206130b0a0f060b220b040b03010b0901120504030509041410032d0303060f0e0601020a0201120902150c010c02030f040302010c02041122170c 76
    0xe00c041180d04c0010a4044481c0c035a5200c4007000108010007080f80140522004541c4e55148484141e9002d074206603a522161203400902004110485a40c079115454640014078100741c00003910704a0101118855900c18000b00b422403000303030350010f4120340c03001e200030301960009200f62410340709043d8003256515007600058030179690650b00101402d04144c10881010ba20030081e0134040d4082e60280903070042c041003041142801c4603d00030b5001c1c812401c001023010304d15071345280803460012194818198900740ca160008800c2903002c00d4981004100d0f64101815410080c6003006103000c0c0c9050150000703450300302c2c4610190400c195050950418520b0b680802c008039401080c01c280590b00001070398036074000d0028580075500e00340b00100354078004400c070f074031200030400d99a281c541540d005650b03501c01620180d030407039618801c940309015280010445291040b0070100580d021450450783c15480d03401a08032404243c0842d54030a0001402c604852000c407000341a25070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 571742733 1250 571741483 571741519
    0x1a030a020d0e0604140c060c0a11061908011805010b07020d060b040c03050a06050409020306130c0b0406180503030a20190b07021204151d0303220e0606040302 70
    0x11504060b007040f0300a91040c0300801051611030312804c42c01c0c40645000b1100d110804c00680252548168550400c4880e6000250098001c0400c59001016a41001c081c580d501d0740e0090300c580d00701c010600d50b01c01400403561101d16043c0760100054144101d604129602210340150000240110001c9801600b002100c0c0c0001801c00c401520402144078210401000382c0001c0c0e9014001a240c61400b081c24102070049000f41900a8000c1c00c1c01d449000010401072203412003600c13048500100800c15076080c000a00040000341e03100746c00503808241e00600501ca642c0240d109600c00c2044004064008001c0c481c00d1502010482003d0807500c44a4242040702101e2070b882d800d0f0b25000c0040089030000103001d401d05500300c0302c06956007003014030580b0942c0240400c601151218002c0341e03115004e2844040658000c40640191001c00700c0c0c40c6400c0030380f1a40d00b200d1008800205010419800d50007024044000b10480c201600410300c0c602c01d500029020700569480040740300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 571743983 1250 571742733 571742741
    0x122102011e0218030606010e010507030314010f05180f19060503030403140f0f0307020f010c0c0824011d04020d080313120c0218070c0b0c0307091a030a020d 69
    0x1840c2a0341101040c40c501900500a43c8050b40f8401102140c4141c070002d03040c0058030314070820040c0c4518410441031001036030542c000c280124201030301c40004800802c442a2024001c120342000c0585240c182020040d02c6104405100080c0401000704040c1008540b0126000500d00081c41ca50443e9082c80380c0182100e0341199070544400940002080343c851901c0c003c0c4840c071000e982e0f9807030460b80d07003d8030b8142520103821035502c00d01c005130140c0f5100980001411050506d610b04200d5540c07540d038084900d510a1502d60810000c0c40b265940a41c011504e045070002c2464a07981000c0070035060101c88020080011420000101151036040e03018100c0fa4004406540b207140001003048130100200701154010084003410581c0340c014060710100c00d41c000c0c0340a1590b01510704405403840000c14a104210500050300c020400000380316010b081d003600c3c940d66030b00c0c00e20405008441075901c89140c0580005130500155030034000c1c2ca0304020498009aa11129440044068 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 571745233 1250 571743983 571744001
    0xc0201081b0c071a0a02030405011b0b0f0702010501080a1e06061703041a0405090a0519090f050d022d0307150b10030e0712080c03030103031812210201 67
    0x600007410072906400003441821209201510136400c030b6210385821090041c030050b50096402808240020340c012101c50b40030881443c12940780c86110744a03240d203001e06171140340100ba5042c00303029040b0f5081c001c1901400c14140200740d142446d81e10100c0500b01c4040c40450092074820103030401403241c00100060502c03400c28845115901103068880d4424031030b00b00808420400d612001d22180d040c0e42c21220000d0003241590780c1d0035400700c05030400602007020100301c50400703401c00a5074418496050300554910445281c913140c100c3c0b4240d041c0030844155800441d001804000c20540c1030000d10f14440801d40351404148039a00d18001c1d4132008180c0189400c1a00400c3e001780d001000080007181c28500886c15840c0c1a8211940856000c11540100d40b0502c80440c408003d1105207100301c0c19149041404089141950401e07001100000e2100d0750015507803401d211851302030081c0b40201d0aa01d000b556034000340040c842c001d0952001607140c1e179800345000703610401003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 571746483 1250 571745233 571745281
    0x70e09160e09070603060506090409050f07090f1505090c160b0c0c011d0715140415090b0c030301030609020609040504031206060302070209061c080c06040204110a0c020108 76
    0x644038048035a00e00c81c210b901c298035128140e00050003d200f03005200032604040c00b250325004404040c000500300c10f0905860b00d00c10580060504441005071100402c0f66103000a07134401c803a56100c0588170f40c4200040700024142085c4a269920080103400180b1002d05070381d074513002c4044541d0a0801180604500e10180420100030031074401004454503010080181012041410135001c0c41740c5602d003c2a400013601380501e504048482000d9555030525200300144d0844510300c3c1d90050b0090541c01000903925103111340c00614450107041041901814801c40f10900765880c0030510000d4145512110000c0954a0700b0741114504c5902030400d102d80d240900300a031503681075080c0d031207103141f60150004004e840781c4250f03028103900400208442c3c40344000c00170300c00080d94440e0740100e404001c00380001c5500004180700c94040c00500400d290a004000071211140d6041c0000c6c4810002d000f203599102a4030185a40d0900740040b0b640c440a000611040c0030f00d00880c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 571747733 1250 571746483 571746523
    0x91707150603060504020103050115140307020c0307080307050606100c120314040c140f0d080a0513030c080d0504030b0406243308070806240d0f0e070e09 68
    0x24808140c01042c49170b8001e0701c0c03c4c843c1c1e076621144090005901920440041c024400f1184040041c0c4000c0d5045206841120740d10360100d40064144007059101480d594000038009042050520505034840b604958842c40e074000008054515002511b004154a46003000b51a07218040da015002985010841c07244c6450303c0d160481d5109041c3c06198407403000c0f50641310003460005a000382102001d0080030761a2407595445180f50841c1c0c20590500100307201d0188128550701030000214021440091094a465415030034884429201c100f045020881440814903400101d5000703a40807500140c00148400d00344e2402c5802500200c882d0500f4100048002c084c03000b85654510138a10028503d140c003515185500c5d06041100200d1004c000055a0034090f2041a50041c00502080740644a610129908109044100000d4640890390b03401049540c0304060703c000034003d00300b0590340c0e41804166100c1c0d40d44241903080c880302001440d0004180040b080744801e94820320 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 571748983 1250 571747733 571747739
    0xc030d111908060a05060f09010302180d08031b0702010c1506090e031305030c01080601081312030c0f0e0303031609031401060303080f221a10090b040917071506 71
    0x1d248140030f039545071155940000100e003501e040030417244c5100c0c60f201c48501e400413230001500a904103840e03500020820200c5400103441d8103d440044030700c5105070325560b18008002c208070040700b000d8840740603403e000500040c6d0b00940340826072600145c203455508000d801e02c8025046a1300104143c5081c2000c14010300400805403d8444580b8510703003607181ca070000d00d07640d02410441180091243c0c40030554079409040d881c0d40004060b016900381c4546d5032181680042150720840c00a0f43c1c864869611307990100350b551515072103141034100040e182000a81d0303400b000c0d01e030007288810003804001e1305025100c0303180250390203121403266145404030240241550300c403c0c1c2c0420000c40000d40008141d01c1c2d020f02c47c4043e00c5c0c4422030000810503141d05c810f10707010111007011800c03010000141c0400701c0c25124480e100ca06010042c140440402038400204405000b50305141c0d10400050710050303c0165482c01541e02c548075852410300541d10100050310400c1c030340c9000004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 571750233 1250 571748983 571748987
    0x4050d1112010219230c120a050315191e08070801020310050a120609060e102a090e042303092d0f040b150c010e01020c030d1119 57
    0x4e0309900100c41611246000b00c0702c419500700e215825080d1500c02a50250848000200c004c1c0c4496403100342264880f00040b07802e5009a0301c00c01445020031404020041100c41d03c40e2900c06084c0241d80480c411b8030000c5100618591500030f640ba030f50300000e00c0c1000b401c1007000400c0189401f070201c51080d9034803c2128003c1d40150707103084021000d00c5000c18281885082001102d6902c10140c0714048103031030f520002e111036482100c403aa03e4600d06410120208080052044151000a40c80c2900c00e510b400741070810a6079014036a00712640c509803504604140111840c02440c2d16042da52460aa03400900000c1d207900c3e00b00044007880d4502c2c0c00000603000000003aa130030070510394082c0f5040340642030012031035a55000852400da99041c80c00c5081d000740c102034400300360700041c0c9000854449140500441781d01001c1142003840c0d000b40a85480104214001c52410920900c0c0303a8482c850b0040b0b1100458075101c054084210120403546c0829880c011801041e5480b000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 571751483 1250 571750233 571750237
    0x170c160f05010b19080106050904080f0f040f030614090d0e19150f09080a150903030f0c0201020702180f06091305161401031104050121050115020616020304050d11120102 75
    0x10605c0c15881c0103400300e80e038200344c9038640c00389800584e1941800c1d10010f513140181d0011428031003c0c0414840010b25411307100781c5402445c411072010440510782c814020100784008c04041003544421004071890b030304406116000784d0161120490240c40c81410300710240e8030340c0002c0d5107210a071a11b8503000d522400c2038494074265611916082d69455440799125030200c0040c01400440c1056003408013550300c0301d8030031442420f002c9511400007404034111042003040c54090303500010300d40118900701d032615401812040705910241024000c1c0c44c01124028215402841c944020501021501c1010020b169100c0121440c2c8075028540358034101592248140382607009200c0c80b4250700078082e03400900c515845641c1010301d00001142c0d402801d02240f203040b809c901101c1000540740c0a11800380090b01103854a5204100000786402c1000b8144031104009010080b0103a5001c4101e4003181e07800c0780c00c90b10344071403810014501c0c0150b60448e0f078403817110700500e4070481341900 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 571752733 1250 571751483 571751489
    0x51e060c06041e020a060503090f0706260108030d0903020a050a050a0201080a1a0415050307090603030e09010305070e0c1b0a051b03060a020703090e07170c160f05010b19 75
    0x5030b180e42c241d030108200c440d0200f041c0d200a51020b003600e0144443c9110b14042c5078082505412030300904040b08025040550f01e800c5032000680c014074104040c041404440048840c003502c13004150b14201e262074490044031304165401d40c4404803003050600c02c22075400d405800a0546054425905e40300d5510600b01000300d0101d4440c4002032910038a5100e605c00346046010040000183d00c07003000010a202080d4008a11407141c003c50162001c001480140c0807680c00000c2d418110300300070300041c0c0c0b4045218801d200400051000a5001c9800c804490301210b1009082d20b9004400400d4007034001558400d1080e401035003c81c5030001107040c0d18601034010340b90404441580215080d1001d0000ca4045c1d210b000441c4209446e540200900341c0640380c403104054841c0449044220706542c0d80d0f0001d45020000160034012030380c0d0b1a088070001000038034205008030412007407450307014054600151441d103002486000e41102c0c801640003422180709281c4808062820003242c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 571753983 1250 571752733 571752743
    0x602060604021606052511011a010903080904061703070210030b0d0f0609080a0206040c0f0e04111224090123100e0c0a0f030501050a051e060c0604 65
    0x100100d215410a84201c0385100b40c20701e5000c000e20140c1e01c9030805000040c100c42950341001ca041c80820b400c01600b141c071302c00305a071b4400010011804250035114554171400440c6001e00c3c281c0d0f40d5070307042000d038003c482d406061291a014035200240c020320325a0301c42c10303540001142140800300044018403046200311a403031605000e0783c8d022801c40c0c06828403c0d0700020f0604010380810a02c0c40716154151040c600481c0c44030362917503060119081700c403c20000d64040310a01080003410220500500301c840040000f0b41e150280079640014040c101500e1019494244465a2648a00e00003080481c0045444200d94041c455103103001e00045c0c3e1a061500801207010342c201805404011246591815251404101200170701071015082c619403a4903000d0000b201240c01f40005e00c109482c041c415202c407810710b00502915044a42d07030302014580070041c025a03407640c8070710068400c213032a843c0ba441b25000035442013034481d03241d084c1e2148012440104004c80010018440c4d0311507 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 571755233 1250 571753983 571753993
    0x92d06070c29030109180c030303150e090606040504060e0d051806030c0d0209120f060a141014240306031c0c0b060f1009212303070b100602 62
    0x201e8031480301000d0b50000b0004000c00040011010316040580b5161701c120750445110710a68036810034143c1a4002c80c0070035155a03400c0c1d0310114080400008101d140719005046c601051604d48a02006000d10704c0b40c4d96850201d424445d01e540803804c1181c20000300c1d10400c070b4a54000d8242d8004a00000740340707030210404031075410300070152409400e03450442405c110401074908040c0d00190780c0700f6000311540740809186442005858401072801015050314200001da140c01d80f65081900415441c1c50f50a11002d1141091510111a400400c8d804800011030010700100d84213001d0b60740031070078142003041c429400d10086024034000c4048850107109488010101c0c800c0c00c0c40c1c0303808031f100001c1c00c8000c25071440d07055502c060000e05040d1901060800164010130880c5e1200001e14814004d1025100c6401050b0400650108852204240b40d0b151500c2e40d43d01802c00340c0c0f400b0024183c400744402081502d0f641079001d500e400c2540362417825000004101c0c41a00c0040c424 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 571756483 1250 571755233 571755269
    0x1803050604150f060806060d11150304110105030f0f071e02030c160308030a151d100522150504020c0f071508040b0601201005010b092d06070c 63
    0xc3e84a11400c882160000d8152a59090100542c200d600d850a80d881c0314a640380851030380c0d5404c0f160802c3c1c6103400c10a902c030f09042c1003402140b649240d22905124003081070110148144c0c6000e07600400c0000040e035036580e0458112602d10811200a10072010703100121411900800035125105200c412211801d240307008542d10115180300c0034000040810114003101c106400084011480d110801c0307641d99940150480031003081007230046c0c00d607450305200a41d548810150001c19044585207110010014280f9110180b510030140b0750743d407080b050710303200703000303a05003004103170003082192100e02d01c0e910561990003000d00c0c3d408502980c207001c0f8090900002e010f02d07246a0742e40d103c905585503582d510b80080c02800e02c80c14131014103003040b009040101c0940000c062076003d004024400790044080d1101038005600c603410502c1003541d103480b8400004901007801552410858903d845030b00c1064601014a400440c005000e00500c42c400e07021004840c070001d81c9003040d0103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 571757733 1250 571756483 571756511
    0x724140603030711060c0c030601060c0201120e0709020d18030c0309060207080601060311120406060f0501020c03122d07210f030c0516050606030607021b01180305060415 75
    0x20030804014501281004c0c001610b00b0b182002d00818596503044800030602807000901e4010264440b0340011007515818045503401901d140c4050200c80c0706000c250b03212000141c6800c0107001d01d60803d580490044c0c2c11001a8100c8044024144c402c0f049032000f03814000d08205049400360007003009040001242c80c0300042c0c040444d00080702520740d590034120704034040c0000c14208007601c4001d00c08180003800c000e414034010344c418400080d55504d0118007101c4081103500c0181036422540840d01203840116594504920f510181540d13407c0c01f003104442c09080481144102c0e0211840b0301e0f41c0f500ea0300081041d0340c050000761030ba025800c07541800440d0214600f03000140102c022440c0d00d802900100c003c040a070030850b05281200da030100312010014426991070748a81c044c482107003800c0c131906030000700c0d074405030003042c003e649541041030240342c6650421507075200391060740d9000b01445014541c001c3c20748001d401c1a00f4208840b0f4100e5840c00612b600d0101003a544003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 571758983 1250 571757733 571757737
    0x22203030f11060112021f02010f0c03060f090f090b1602010b120a02091b160209070302040620120a030510060203091008090c030a080d2301030602072414060303 71
    0x100c2e400000c2082d6800c0141600b2441d0f14a0002c0340c20904840402d64140d021148410480146500000e41384542170002400d4621040c2442c090600c0c1c90014400c1c80c61000b60b85080d02d400309000f24002e000d00d03036503030f000340725044010f055a03450006101c00c035408400342815580c5194000e0158101c55020040d0583c0794084032035181d401207001d4001824a4044283c0c0101c04840c140f0648020400c0c0c8142035020f0018401c124200020502c2107240070914a43c025402d854114205803d120001c0e290a4050496141700c01c0f914490350388407201000700d0880c0f12081d00c1155203843c00c0e0b6401502a21050318600b0b0301c0103899030041407461001040e14004100244510305040a441003a01e09036009030884226006da58021001074030100a4806403d01c20ba01c01c03907407403113145c81d501c044602203009008550405101616003c40442070181036a4005c2c3c8010707034a060350710344109003501c581090364048030500402c18849105900c404107020400204203142d50b44d080402d40c9074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 571760233 1250 571758983 571759007
    0x105043503181c020a03020114090703150e12030603190201120c03090f1a16171909060605120102281413090c0201090b01050f04022203030f 62
    0x2529091000800c00b1100d86441c6001c0e032110000e4840c503441443c1c0010440100354090303009030344440c5003c0d0030964240310f00340c82c640307034203118011908158441588960186c40068001c4503480100101040c0607800342c420000d41c6800c440010030703051100d8141d60000c50380c107842801525100301503007459190702d0f005070303030705940340ca0390010300111450040c50100d01d400300300341d911248080020041003202c500d032400390401074001c400c0b40294450810000703100c8942c040c2d00c00e80210b0541d0300140c43e0321b400083c01c060307a0034030b54880c0740d04100c08031a8000031560700d003840c000009000c8030342e01010035200141e81e5085041c000384a003900741c0c071a003001e200d07410403040c2003180c00703940031510320013940701c01c0c030380840c80c0e0300500e50309001500f024034440304002c2c02c000104940100c078459040d038451540001c0c80f6030003031626030504012051017a80d00a040c110101c401c01c0d50b45504581e408a0024440300c0e5103c0e80d6803494480300c84c2808114086015090a0305490380207400140c1c0c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 571761483 1250 571760233 571760333
    0x903110f1012090204021c0e0a031b080c060a0b030606100923120c091b120942010302151812160f060905120c03010504 53
    0x414859100072514000301140c40042d46640d0314100c801603455000801404261142c420f0190350001810400c07246071448040d44d660212a000c00003d030002c1c40c810000301401b086402d40341e0a400c12403d00d210b904080700f92030240c44100000c01c2c1455000c20012001901141c44541d50542402003550842044001040703070103c04001c0a8550700b10042c400d04100d02c03190a01c6080e00c045242c45032041244440c0d40c20040781041a41860100685d1021071115a0019000001d580d51810700ca18080142541d0000c0005011000308100c4a200d00046180404a060024131500051a6504003e00c5130144010681c0c88220105c01c469050300d0300180801e41203100104d00400942c420012081c0054444040400f551b440300c410b0741c03072401000054002044141d2103107201003200d401c000d0125490301014045143c0c00a100820b0380c5080d55094241784441c8841483c00c04500c01c105d91560034002040304000828801d81e40ba501d0324400b50408481d500c803490000380c03101c0b525101c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 571762589 1106 571761483 571761499
    0x41730220e0c0705150c09090402150f0a020f0c0612070e061c0b040c021b0a0b130602160602030a0807050c0601030b181b0f060d0204060903110f 64
    0x80700842940175105910345003101004502844032903a00131285540003600315251054042105481000a1902c9003503ca040c20025070080c94000d0060090000c1e18012000004401d4005400240300506258440038807040940004181e50200807003201c000000e80c0f81d900060619240e422405c81200514000100584586443c1c06010740d02d4880b030f544402c0e0b40421038004401c411200d2144415078980001c40c8207500e60082004407400007450100d4081341600c00381120b0f9140c0a0385c4182032001c11490400c000c521409003d44c02c20013280341c680f40315102155100c000703403c0c818144440041c2040c0703405801d8004a42850310f000038883c10088602c180c0c400110039030000c0c01d5420f10606c0f0f5244c414a10127506014011903048540c40d50784a5007541c01c4104003400454446548080040038241240310030355001070010030104541c1890b104522141c10054030342e407 = true := by decide +kernel

theorem cover : BRFrame.Cov 571582733 571762589 := by
  have h0 := BRFrame.cov_init 571582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 571582733 ≤ n) (h2 : n < 571762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
