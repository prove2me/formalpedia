-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2098
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:38:41.019157+00:00
-- url     : https://prove2.me/submissions/4bf7cfd9-4faf-4b08-872f-c125484ffa59

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 377158273 ≤ n < 377338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 377159523 1250 377158273 377158283
    0xc12070311070b090705040204061106070c081c02070807060506031b0f09130b0106110c01020601050d0b10030b01090903030b090103030206130812191a010801052709060f0c07 77
    0x2400440d441d01d1000034005071500307413035002d19000802d05403a40c0c0000c0001d4800d40c0c4461708071207a1803903690319014004003498108108003160100194001040390890030310910040814542c60542c07d000b4801c03180002c102120024002c410003021750482c13449200d04a06a482d110040c0200c0000002d59140440d0300c41a200d140701c810b460941001c40e0480b0603010401e40340059a5501101d00728281c019001254407041c7c8402d1018007042200002c0c8000e00c0501020f52400000c11402010001c0003801c00c20448001440c16040340f2a000056410003d00031031941d64440700002000d8512054000900b00010b40e0703824104900b81d05c1c100c9a240e80240090750701ca80d000a070b61080d0900c1151b010f40100400a00e8000609145001d00348000364000120b4206c10050700b26201c00024500310350b068240c0c400280c3e084409541140d50560380785a09001c01d0034500003c548400c0c1c01d0424010744000d00008040c00149240318007e80001c07020a0b45540300d0405250241d8040280 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 377160773 1250 377159523 377159527
    0x302061b0c0723041401150318140f0a17070201020a0501060e2a0f070510060b0d0515030c041107050102040f1e14010c060e0a060504050d0c020312090f090c12070311 73
    0x2042c10701f40d4031f0b03403081141103160000b1580140c56800740417108521040d92174400000445030012024400ca002d0342d03e040004045101050b91140d0540d42c0c4501002031051000c11542c040d64024010200c000f58010000c008054407441400e2444100b0748415588032032825008507002011030845880143d805d180310705009800c0110806c50380101030803609400f41c900c00105620150190344050701100c05029281e189042800b022140d005125450300703045401c1c84080d6882c082140c0001c42c00584000c58518108200300d81c10f80302d2180014025807002500094038000b0074411800d8540c0c441d1507005c2c1f00c0c070000c0041040440e40c06104030305902198004040d41c0244451001c061054a01152f0441c0086055003841e4503007000f640e07001c0d02c070400c000801606100c071807807000e401d0400e02100680da4002ca55540c2e40030b171303807100d0564002600c40107942e1125035141e61004000c049401c00e2410103510242d42c0c200350243c102c1c0714000300125178143d020740180b80340e010403000058 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 377162023 1250 377160773 377160779
    0x5010b0412020d0611070821160f03061e03110103020406020d1b020604060e0102010b1021020c06010b0a090504020724060e0c040305070e040302061b0c0723041401 72
    0xd503665110900f120322a9680502d21905c9034258040c21003a80a0030080340c41d04465402e007580702041c0c001200a1040460800221681106034011141c6903841d03c01c3d0b5104442d81c040d0000c00c02c4c0d0304882d0b40d0900d00407084010042650b802c0c03007520711402407064408040c00055080c0e010782c0c024440540c00034082c1c2000325104c0c00700101c0742c607e50b451010898a05401040240d401508288001451850b074105c1958090094040c1e0140a0f104c0c07040c10307400b14600a10398803280c0110541d0300301c921100c0c001c8140c1c035010746940701d25980c1035600350350352403041001303550001042401082039020300140c030f45454400d59120b180c000350b000c83c0300c9080c6c0b103060600c020380d4841444400d0742c882c004a071304070802d503019220f204031300d249660b80ca0550074814038010a917403001c14003a42c05410400020350203e512508014103c42070441c000ca034500044080c0204039a072507444c41000000501c04c85000169241012000d191809000c4e4034024802560080100100d04e00070b084010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 377163273 1250 377162023 377162029
    0x1b0d0c0315080f370602041508060414070509010e0109030618050d05120112031106190e120909070908031309060e150f04110d06030309050d0c0303210e060a05010b041202 75
    0x240c1c84d07542c8551401882d10380c035554003001c507101e20010280014040810400d5508051007201c0c90810100390201b1a440e0688004203107101d011030250420000d40600e200e140d0240780704074099680581c040c404001d141000040700d070040360f0142c0c0e080c8540191250882c1c002c0003280c11180c8203080d8000c0d540c0c203000d2001c0c030b40d1022034011020031015404124030350506001560191089100401c0c281d140c0040c0081656061201d145407904202c105c0c441a4140c4c2e01256007004091ba007042440d946d4041c00e41d0160030b5070b44806094080022882100c482c0c0503200750a40303450315000c00880d82c5131100c840d01707040c00b1180711414502c00e103044091441e02c0404d40100c0440240003140740016180a5181e542081582660035a01c42c0c0050040507005030052010344000c6e240350b029000e05803912510b0035683e100c050705014003904841d001030020141c0350703c1000001014070148118904240d0b03940d004607407010f0360629050000c00d0f903110060846044441800070b80f04044056020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 377164523 1250 377163273 377163373
    0xe0105030f061c080a0c0201090906050603060d05010b10110d03050403020a1709150405040528091e03050d061e03110a08010608060106081b0d0c0315080f 68
    0x45916943c0141004400585110024501c280403540c80c001d04220707520000d031450f091a0011243c0e242030120a00c11601e610007640d038001c2d000c40b44161040b002d03007042030040201800491300700c0e07010b00c52400c0b00c9070080c240c0c04841034840200ca0400c000340c0740403800c465041c1c80060058000300c02503004a03110410449050754550145450410180c0004a2101081e0751a61400c4c0c000b01d4104050300c5d042c41180d42c4014031481360324140d80000b02d007413a000a07000c86559100d91b0381050740144030074880c03140c0c109014814040d1903c0090b0070060065008203681746401400c040300480c0014095802d43d13030002403480b000384c026040d52b485c10601d030346010000e500034a1042c0c0024401c4024002e10000b41140c00c080d0802e9410701c017006001110081001401e0840084856900800f41c0210303590030001070400500180c0420048019011104207030915200c00e800100b541603000c2034114400060720220385042d980c144a9000d146015800c41e4444402024031010440316594 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 377165773 1250 377164523 377164549
    0xa0e07031a090709061205060904030f0509100503090105090a051e190c0f0b03091b01170103060608100b06090904080c0307060506040501270b180f070e0105030f06 72
    0xc0d4084107056000081800325004480c00c60003e4110b010400070030b900b21500912103541200c0c2400b2524000c1c000c900c1d2028042c000800700024410b074604514030400030383d0300f128070040003912101000500100980c1081d0340a20142d4604000b140c1110700010b6410012036200000e0040758003640c0358146c18025440100605c0c1c014801100082141c1c080c0d503004070b6200e04181da0380f0358100701403002c0040e041c3d00444600c400402c07d000040e1800206042130004100242011002d034078012a00c1004c03064038855010b489000101c1048080d801072000d07103c00d00b00b140c4590b078001d614542510b44a45400b9085081001522028280114860340c858020101e02d413512840342c02c45841c540c80030f0402c1c1e40781c60303955050062516141c0140b80c010b100a03020300492910024000f00900711000c0d445888590798031881440d030b00c0303290000d0441040b1580c0c200d01458462851015050708480403000110325042c003848540c010b1095034003480c10001d0314030495940c10280050108650 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 377167023 1250 377165773 377165801
    0xc031104060e01080124080c04020703030204080307230c2101090b1503010b090702061609090c09050307050d38010303020a0203060601030e250503030c0d0e0a0e0703 73
    0x604085422015444154020181140001110074070303042c0b40c480b46410141c1c1c031b20822002110130011020005104803021000700c40c01640d820051030309070000d1256a100d0070b4a40001f0446809016681c0c003d249503003444460403075400c9aa0260540300d0800f485c110780e0101ca000000d0aa40d102c402c04c20030b0b0710b02584000142c441c500d80359200d810070700b203995200d421003d0041145504080c004c41020100c00d685121450070f003000041e46486005005a084994041b101c0882c6880b030264440204500ca20070000b00030402c400a000641a029250082c4a100000682d50410000800c880c6030400d00800308034000d41000140110403090140d072080c076040c0401c004401c40104180218400d4006040e9181c840c4107150500720000c104905140c500026036001c0000402c3d110a0303035041c0c0301820300c54290755075414040d101d03940002e505844003103066003800c00e0016480d4000e0b6590303103445248000880c1040b00940b002d0040000340c6e580f07400402d81185c0603070008025200c1e50 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 377168273 1250 377167023 377167031
    0x21503060d0f0614040c030501060602060105090a0b04150b04140307060f0f020102211501140910120f0209091302030c040218100201020405040e030705060402010f1106010902250c031104 82
    0x1100c100f2440000a0745c05030b902007640c800400801200748035070002040c682c000380103290300d800c00141003a6002058070320050307103e0350350310203580d1142e0020341d100030101000c9244540301c0c50b400c3e900c0e2f0054000c0c0550a28103a20b88007241c500002c402045500d65980e00e01305a42511040303c807503035a00010403c3d59024090301c1181c40131108010141000c411800301c440c5083c5e4040d0300e80440741c0c1d070340a05004008010803540741c10401240d0b5460415502701901d07101840d0304460403d42483e0b01d5841a01e089000c00d440c1d5403940080c6905901110301140c50b407030f003107403050050604140007517155000d80d200400504040c2c02815007034600c900c4494201144002081030703141c00e009200d0041c0d50008007400a45002e214400768050484003c40c2400000c0d0380b015642c0310082e00c080c3c10b000b8540e46010701e2a00c1003600c4900d05803080181c500c1940e480c01d000029410141c1c440c02032440001d80341240400601d08d900c5a1900f000e4101d25451558543c058950100e19102ea002031312 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 377169523 1250 377168273 377168291
    0x4060608270d2f011a040b090c1c0219030c020f03040608070e040e0601050a1a0d0203270c03061e0708060402040f03030804060f0b0105040e06030102130e04021503060d0f06 76
    0x1c0c56200c443c840402c900214a0080c2001e01c41c65104a41e0000c43c4182d2030045e600c41d0340e440750803003103500044162a403941c40c40b2000e800c02c00f0140300c1039922201c42c0001070707035001c02c2c4046140b500d0003000c43d1810301c0901000c80f8280c0e00d44c0031803e0144560b81c8188810004c0702d00c41c50056800c690035062410030300d1500701c049003e032111442101d00c0c0341c0c0030b8401081a41401c010300e0300181a50041c7e0b54500740c0050b072540080c49200541ca1000d90044041048040d8010f03d11991084040700c80459856424180d0340b2034031442c804034440e015100006002c07040c51408028030000104901c030700d40e52268402e44103c1800340040f03801070740c00c0c4400b14800c0020640940914003941f900b800c0d0b4502840c00030240d4855030301c100d80d0035007090854451641c1100660301035800301200c00140e5a20341c070110780207018012012801d000325240000712030f110007280e140201d00079200004108815050b0250510040c0c074415000042503181b1b001250035901811700b4607100b1080440c102c80 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 377170773 1250 377169523 377169587
    0xb0304060510050306100b0d0204090915060933051201060504051b040312030f02161e050601050d02120d020d020d08070e06160204060608270d 63
    0x112821295559500c0034000401c2075024224024142100200050714003901440d2021740e06108608601c440410781a0383d111003501a00d0140845000c01c0044d41c04c0e078103005440d540c0c2d4030fa040009138508080450509814010703d0304504440050f4641100903026089001c4410300802c101030802020110303c076540c00c0c2c0d40582c10000c1100104510f4104820082110000381070100c0034031044d00402001ca00c1c82c41500e04881d00030352040c6200da81b200c0c1c20340250107042084000c1c00d00c0040c808200342c1c15020104003c1c0c1c0031340928400c00c0c215210310844c0740014070000c0d120368800300041102c1d00c0c05282c808005480606100313000200b14070558942080d1034200340140e00020100034071142d040081d00152111480c113002e0f01c0c02d0001c07000c0c1600c443c99400c0e034000e0341c00140d4100701400c840c1c1c038000120350107030041020075038890000b080c400066a000c050400d80783d4203c8100c0d0145a00910303885505405800000e141203426555805840461580b002100400b010203403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 377172023 1250 377170773 377170777
    0xd05040308150a08101113030507030c05120616050706020d0e06060a1a03040c27110c06010e04110904141005090a0201030e0c060706091203090803150a0b 68
    0x64480e07110041d20b402c201c288611240c0a610505000b04030802d400c01c640e60000540c20780c0804e04050000b02e001d0a0700203002544900e40313505c2082940701a00100700301300000d03480c9c2103c1c01040c080d0003032511101044690602c480d040c405a601c2200030990100b20310750710a4440380503040041c40e00c001c660340c0c802a070f001030502041240d0388201000a04000344a29548810201c84a2028609002c5443c000d9007a5100311780c100c010110004040151b600c01c80400b600803002c0c0485c5880d00000950900d08103081030007440c900f04000581404d241d4819240315146410262050780e081200941408100500c00d4480704883e400f68009611613210150150307018120050503088100f01041c070b84240007090f0703039049240034200202500e010400311003503a42440d0114043d024810040d151400c0d440009500c040000b03004820402680e01c400600c070721907000350105a0031401c06401300c482c2c201000d49882d1081000904a1180c011070ba0090340004020dc0040781c1c61b008030040c07039 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 377173273 1250 377172023 377172031
    0x100516140c04050f04030804020105071a1b0a0f1202091f0e010203090f090702100f1a030c090402012d030b09060a080706030e0304050306090a120f09030b0c0d05 71
    0x56008260845082406021000440406030b40c180444d0074204049412000010406000c002c10300003c138003168480d00483d409280c100b1070075070016001d8085c09046443c20b444071642c0e04e1030184c1205088a68100361002100d441c1c132052101c0242d440c06594540e5040c600c1000b0580c2004410310940e50130000301c480075007080384460009010034000c4e00801045000741e05540c4144207805403590f40031030410b5014020741c0d254002e81c0362041c00303a1401c03807201049580c290400c01c0900c039003852a4006c5000c0282c00075024003000e60541850b8485890310101604002c40400113405540a1181e41d00b80b01041c010204009404080c080000c03034a00d0606400a92110703c94080c80c0343c80e200064011300121001c0c11501d00d000ba44540d900032601c5030400341512174030400500070302801542d00404000d030603901d80d480c100c29240d071241946101114441001018808001d11138091300b030b80580d0584800c18124195200c12008401c0144440740c07072041000b02c43c0942401e07004140c05 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 377174523 1250 377173273 377173283
    0x40608060412030218010f020a050f06070f090807050909033001052d061b07050102250522020a030906051305060c0315100207140a030201020c100516 66
    0x568141898044104200302502c0400c2600511450401c201d080c401c4115a00090809000c21482038030706a0800301403200c00707821030298030aa00703070302c0b080030400ba440f4034411f0703840e5200c40c90492001c1c1c41803038850040c00c0d46680720103818011802c011840340e80000e0300388100ca0910700f00c1190041c0304010261a82d094200c0d06046100303900c02d0050700350142904481c0f000292095800301e070340c00990389015078610250b0380680341450711100115043c3c0340100c02031703440e404030039540559104841e11403a4010b00c03948009840107142002108480b024040d030448600c1d02e02010410b4107c55195038500041da1030000c1c980810702031004040b4203540c0d03140442da201c624200082102d03001014840012200f00041001aa000ca03819611402d1001c00d0b940381d4075160212004509030320a83da0300400383c064094441c54000515000f222081a102181d6500150900045841c54803009015038082c0d028a040b40ca0100700c00907031259a460079500300100340d1508403049400310001e9807 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 377175773 1250 377174523 377174533
    0xd09090c050c06041227030b06101d03012901020f030c0a031b0b01060c0506091b063718030f020d08160c09051b030711070302040608 59
    0x8940029401180103481190802a0800c0e051241c80d9440d080000c000502502141e0b100754a070600664041c800301c2420740c02034020b41080c45070086802e1440c007054a10801d450000b81a03481c0101c0c41c0420b4800720340e101130040300030400100347c01d898000303459031654941041c2601c502c02c14105280540035150181000e240311400641400300328110030100d60410030010482240004070901040d0f41490100002988040429103012000030018911003c0350000211254003039042c101c0e0501038020780b1542d40f1181740342c0f60745a51201d8110366940c803451b40000507140120150000c560152811451203c07000300002c04804070f490307034071500031091a5a94a29a00508100c0c0040c40d07115a804200e080d078403505080c0382012802445034205400010421007000140c40360000302c0000981090968604143c0c088210b00880e081c00b0300d0180041c40f41d540c40048503551039680f60000d850341d15064070407038604800d044501c141e44103c200000040c1c030b651180c207005040350700c0900 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 377177023 1250 377175773 377175779
    0x903031216020a0309050d060b0603010815100317070221100c09050603060d0201050706022106010503071d040e06040f050c0901030507122a03020f2209030e030d09 72
    0x5012840c0c8641d5000c56020201c002c00280e0014004000c0d81c0302100e0020044580d0324045001c0c103080c043e41d5812420210000805000c0001d10b002c9100d489026600da90f80d602d0341060440313600d440068070b003000c400180c880d41130854000b0f0603031390f002401000441042a04121038460421610300095000204484040300c01d40f00341c090300f41040ca080c012003840d00c400900c10f4040a81094842e040304c520003811a8010001c4540c0b01e44c1c4004195121200855200c2d415180f41a590060b08031282c002003030b6620031400c4906c200c44903101c0a4600c06114031010000f10040d1011343c1065490407100003c0c00c1c100134040c80f642c0f08200b00c2130a25864540345003081c1800c034201e40190000401800003550202c0c40c102030300d075503450f80828400b0302c0c01c12007481d109016007842c070b001004010700d0300116050201d0090340e00236101048480a05014003d03030b01e42d40c2c6081606500c1c5c0301d0313244070303070300c50540001c3c0202c0e01a1500b60f01c5e01d5001e40c0081e0a00c1450515200420044c1d84c2c10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 377178273 1250 377177023 377177041
    0x90705041d1b0414010b0a0e27090f010e010b0a1403060406020307020c04020403110f060406050d201b0f03030c040612110a050904050a020702060f030c09030312 71
    0x1d030824a800901c2401e2240e03003800103540ca0900b081c1c1181150010080b1110070340303980d40711020f08040415525a156543d40820916500c202d104200040d080c181441a5081003951080d8000080c0928080a103186c0c298800c1c04501801c0720045010340145031100e40c40c24040c6000070002000000383c01e024900c1003100810290348240c591500780c02542c54242d4001c14803c1d4000d4008e40f001d6503a0750703561000c82c10640c07024540d9600c0380c40458003105125415903000041007042d01c84080704030f1035004222260080340b00f040001482003102c0303c880b0b0140d8100303400e00314401400c09850300520780d40510302d8010391a80d15074500081d101c41d000b224100141a42120320902540c61810240118080c0e440f59000c1d503000d2001c00c0d181359400850030340c090204407503540002c039250f6418002c020300c59400903040900c11400d02d40415100440d1340b08a0311403070f90050100d403402c142c4180e911800d03000103051040e07482c01400100c0d000d4400344000e010320403003041c070496546000101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 377179523 1250 377178273 377178281
    0x90115050603091c18050909060408070609020a060c02030f0622060204090203150a09020a0e060a110627031303060507051b01150b03060117060a05060c060117120301090c09050909070504 82
    0x21f4401d03500c4c80b092166040300416203c0e003050b0060301c090303690440381c10701401070194048001e40084100000156841c0c5c080320b0303520928421002c1c0c850140c3d1041030156600c0e800c0d54a548000e00003010a000f044001c50024101c600c510302c05824941e4a401c4c03c0202d800407945150100c0c00c0b901081e10702d01d095095a405013198840441c14049614401480303180c0b401820750151200040d41c0c907a5500a215506180d50714004569403403600b89010130701c030000b0403030450742c150b940d004500711a00c1c04825140c000700d446d1201c14580f80fa54450303c015060140130b0038140102003040046c19a620324405669420300780000c124a40c003600180c400d82d4042d0b000d071691b08401c0c0103000c481c1ea070140c40d8140c8144843d5800780300c0c5d15108002480003507194001540007000041d0402203240204103e41200e24850315104d05000c1d0126207501c840c8444950008003c041005000c2260347c0d602c0740050110f9445c0185403ea241c4021402c0d03d030040c1d45598040c1d028940410052905000b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 377180773 1250 377179523 377179529
    0x60c0c0f030705030d090807140d0f0e060d091106030718060801180906110c16051203040611120a020a0c09060510030e0a0803130b090115050603091c18 67
    0x25882c010207521102e8880c040ca0081140c6903403284405410301c0081003d503144950460f040100a03603400c0010b9664041c05070641003c9090100050815070050543c0d800348680135104505c3c3c4603010000200401d50700d0170413624101100341521840d215180510f21501440d2603442c5068030b80006802e0700040d40e400300f03040000040052040504007a100d1200c3c151020020840f402c4a240400142503e09111f001500c00810a023000c1900000c030180c500841100d964107598440c010700070104141b00036052154000c000c20414a0701c904000140002143e003511040051040031805d640d000000c81c03c01640308003860400d0060701e040090040403880c00802c43c1c0e500d01b07004900d50050201a0304140345e0341e0356281030810414002c00390101d40c803880c203e60301c1c036040c030812894481d4640c0035144c501e440400501040350504c10341051440a1071400801ca2903c410021680e00040603215140612603c1203110032290603054180300d000e80b60000c40781d0343e45d09240040900c0d40c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 377182023 1250 377180773 377180803
    0x10f060b030403083102031c0504090f0b280b16060c020a171e030915090a0203071401050c01050f090d1704080702010c050708060118050f070e03010e060c0c 69
    0x3104c1c0c403001140034030705d0440131103624207000700360240e000080c00e04440e0401039543d003600e94104205e00e50b000c001030007501c62919080000000c1481c8080031144501d19183e004046940c62010b0501082002103044445190403000385e0b4661205552980011a4600000e9640c80602e01000494011307500c500400e0f1009000b14516500c8034100203400c010300455a280010b40140d00c00000001f160b0700c0c03510450302550780d00300070413801c0c3d8603102c141ca50402c4507c0d0340003003000c0306000704100380c2403030300100205030460a140c1480d039110140e07010a81445820402528911002c0c002c0ac2d202e80c001c10145145403918150071414081d4200c075003410850310f01d218040380040c5a03c074039002604440e00c00c0d1100351920041c1c45070b4007002c502030034602c200240010710010005445060f5488024088000442c1e0080c150641d00162210504290305000245801d4070641d0303069640c8000038000f0079103030060500c0c1414400c00765030303240044000150a54041900b000030320721510081d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 377183273 1250 377182023 377182051
    0xf0201030b012f0312010b09040b03061b1810020a030e0d050619020405150307090f081504020301180605090f061b1606021804060509070c0b0603010f060b03040308 72
    0x2440714100ca000140503440c0c6083c3c441d0055010440810075210110f100140150035941c55500c80c03411030f00302c0c0c02c24911417410052510b10031f050209050740036100c0d204140161004940b0800e000d60002c40c0c1d6001042c0d080040c40c4020390b190300200202000c02e8001e001500300b5030400a05041d5601d040d02c1c01010003162480c00180300042079980007920b140318000203008200418083d200c0c507408240e0080c0c024001c1000710f40747c5800bc40c041c0c1d5885d25200c00c1c0035a190316042d40b8032030302d00c1a9112030b00300d840320404183c5100341300c3c1c1d0702620081c0009400b00314002c0888002500c0381003079484035926810040d0b1414104203d40c100d000c81c00c01400c844c580403280c1c04400300d03034080383c06407041d0200d0283e00b4800200840b01601d42d000400707640701c0800d60701080c00107a4410f02d07582708a0a0440c00607a900300700c1c8600b4004e090640d5081411840c0f500d038516903102c0544402c1c0c142d0b60341c2164205c00c2d011446404083c0c1400703c074155480c146030a004140c290041c03e440c0003c00c00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 377184523 1250 377183273 377183297
    0x607030218062808100e0c0d2f1305040e03090120010911040b0409020114070804030f0c030201080c0301050913240c02101a0103051b070f0201030b01 66
    0x519200c460301c01150a140d07102d840b60f5603003101c00c481c182e1100d0020b042e59060f00e807298002c00311a100700100030214071115900e040100924009880c0108010420091b140055603641c00443d024403950161150a01a9401180d50907801c2010314010344004505180e10400b14040c1d50001c00f8211414010b50102010f81500d038843c151585051040a2101d004080003000481e2010207490b0300070002c11400c1c2c140340c4d5440b0300ba100b0480c8554503041e003054861500c1c0c450200159010b80d07404032806011104007081d80e024610988040c1c1d4280400000241600740c2c028109200e00364204a03c2c1c80c510014003800c001900c00d44841c6018001400140c45138100182d000606c004440720719055410203c00c075015004038200c59a081003036078003072000a5000501c0d024104e500712030350350308940030750310898071700100d818050360504100c404550302c65000f071a0440e44290801401c3c0e0000c00b030044056200080854445400100040945d070b00342c81034811030034083c2049203160702 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 377185773 1250 377184523 377184547
    0x50102010b09011a16050a0303050f0f091c050717040617160509061204031e03020f041e12051f051e04030201020c0106030b0115050405030615010216090e06070302 72
    0x8101c20360b02c0e26940c04950105c10203900340081503442c1d00030064440d85a4103003801005414210386502440b45000c2c0850004c90306064a01d20901c441400b07411001040003100c044603105420001c10000c05001c5100030581810504120041c006a216a110b180100c0900304040200320355014210803010003819038142d50031110f00c0381d014549169a10444000280d2500540d80ca030240b4500c03020803c0101030b0401c0c1030805078014a100380882c0320a080d0110140d208034403140d50b20000c1030104124540b180402c0c403030000780c01390414030107a0312540360140000e81c0c0301060b20650f00c41d0250705e810420700000000c0f00b04003a04207000038980140800c61001042c007401d003001c5040000170301498400c0d410f81c0c0040d01034400030f2052540d28100084421030038020f03026102c6894103044600b034050400c0b0740840d040903000c2c041c0d560300c20b12803030001c2d00c81050040c158010001072a0030b0a02c401206c8010745a1110002201003048440c9494540010725240c02c1c5481000300b122022 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 377187023 1250 377185773 377185799
    0x4140f1f1a0102030d201801110f0a0605060303090d0c0e06010e011b0201090f0609050103141608071e120c03050c0f0c030d06140111190204021b1006050102010b0901 73
    0x20440c0c140807540c000894043c0009040e0742e141500d8201b40030500f0000d840040700c084c1c1c190f0009a0302e03c814020f170309403015161981c500d420016588001c002c0c00000d07a10340c00c0540d1050008080c0e9080804000104143c07460031181103440341141041400302e0b981c80844c0a0b04418203103400e10020000100182102440d10310f900441e0030044509811a0b11884444019143d681c8011300d001d6a03812000d0841e4640740285404281400c0c109030940d0780c0702c80c180c2e210750002000d081c10765003054015120718001510013402c105024050340f002000303840188d03405980c140e54002101c00c401a41c02c1c1102c00e0b0700306003070415003070000748800c0592420556600000d00c002966841003d506420301c1e510400101d010741c1800c01000044810b011010501c40b80760a0325180e090316090440562548500603641c2c08689980d8421000740c1031540c0580490540c0d0070700580e811015101081ca02460300445094540d2941818481942d080c001c03080310700d00c251002141755052120120100b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 377188273 1250 377187023 377187037
    0xf0b070c1211010e010c0509180603030301140d12021f050f0613060509090a11090c0d0f09231b01020309040e01180614060a03080304140f1f1a010203 66
    0xb1442c40e80308008500d0030342c80134a650305540002c2201c4850040c010b00a90048450b03280304552003c29241c0403100100d000784a854010f01a514580c00d10100081c50b00030040782a800c00d1440e040b120008a0140d51501004bc0a40080000b80c00420200e00111040142020001c0c2400103100380304280e02401d9401c9001141d4680240803403c2c10786004003404d602941c1e12443d80750901202c03010101d00840701602811340342c4c00c122a81014894914002c0d544180500000c0110100751007080d441014a2020719001096045107034640a0122142100b18403207036414009048144004008403080e40040c000159110180180043d4981c040c003144240226110b800a00000e1020340c8200036030f460031000159404070900300034008101d006064501d0600b8540458220b01e0816480070444c0da008040f24903590307072a951401c4141c40f55143d8403447c82000500c8403250010300c8141c40d044000c54681a000110401c000b050350303054050003101d240c0d4191800c00702d90b4048102e6410b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 377189523 1250 377188273 377188277
    0x70e0d0b0402030f0106180506030a0f1b05040905060f0f090703020f1809060412020303010b04031118090d02100b010e120f010c030209100f09090b01030b0d0f0b070c12 74
    0x1280e07158004242000b4400038400030359481c0031808070b042c400904100290286544c01002030703a440c10141641c82080b03450244c02d407a000640c107400035100c0302e900e071241072541e610841c0f999501c0d0041019108a10011501604100c040042a9410707003200340d803040354180c26507442d0a01500c03a40e2030390380500000e401643c04d002c400095071240d00c2010340c1241c148881040c80c0c540000380989941007036408450807a903c9072000000d80c400030643c0d0581c2c0030718510b1460039145031345069020b20b5030381419410040400c00402038030a11410329102c0c0c113801c4017a00c6a09101c40d0000e06200c9110983c01765035107803584401c20350340c1c0200326521480060320300b00d1070550713501a140c2c905014804920010741c20002419051030b03250b0050701007610300340c2e8510029400e101090380d10035214506c00001846540c010440e08600e0b802c5076400c82c80c10704000510a40c0d079004a0080000b480c07003500c6101c001071501d810480da400401d41e000c9124540121a0f41c000d503503141c0440480310220003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 377190773 1250 377189523 377189543
    0xa0b0a05100c020907020109030f08090c090a0e010f02040f080303090303040219030f110a0b09030d0521010e06030f1902061e0d14060402041409041b14030105070e0d 73
    0x1114003a0000c086203d80080c0101120324111714002d02030001140300701c00045149032144e00c030300d006510701030241003650054100c0e8041c1405012214000410454a6903264410054007040a1160380e941000590000d82d9460030280c0e0011030020701c2e400b00c14a50710410070031041c14008000e4a030071a03411241003500450107040030000461940010700401c440c80c08040070440e03060f007000b202d107900f0b40300d03201003540d50201800c80340605c1c230516030160410710304044203d02c5040100b68a8481343c03001c410780395200c1d6007070440c1007007600080100074586003482100d10b0200f020040e402c2900000b800c00d900d00d0381640c16000c003203110082c0500c02c08602c4070031500e0403079480e1710000d00075203081e5201c00f0504081d0000d0041d500d8640724500b080000b0502906083c000c85050307a42044c104041002034505100c20050300400c00d5a85844401d280e050307058002086c80000c1c0b11481494020050b075001f05421038002810f00c0050061a2424414586813901102803031600104050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 377192023 1250 377190773 377190799
    0xa0b040605041106180405060405160c060e07180e0102040f060c0c0b0d02090108091908030a0f0c091403012307020a0203120d0b0a060c0b0907180f050a0b0a05 70
    0x10180c00b14001407258801c901240c178000c1c03d858100030070b040302800c4405002d142c88030400e11045078000c2e10088096038410300d040c56068000c5080c100369500c20140062001e507030000e99400c02d5a903400a01e180035040e406400c5090943c0581c1c402d00e602100214034140c80d01814a602d0043d03441020107004000000701c007800080c1c881c100080024140280c0c0c0c13002d260107441c00a51001170100c3c081043c000100c3d203901400a0102500c8000a04689a0410036150b00384190001007040c0345858541c01100540c0703541d40170300c0b002c0c05003c0e180c5500c00d90800100c08181500c00020754040c1e807510703100c0c105180b031400e03290820000c12905040702e501d03078640483c00c2101180008e07415101e00c06004907046a00001062419180c6800700030450b0381d0320070031507103403a9445407400007012212248041194540d09941120b001402c4813011541e58010114400b0b4014501180070383d0340c9162011106580a13080d440b94042c1c2042000004010008801c503040e401002c1c05106182690303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 377193273 1250 377192023 377192033
    0x312050121080c0601030f020405130201080a0b2b0c08160506160c0b030108010c0302041518030b0115030b011b030e03100e0c0f03030705030301210803071106090a0b04060504 77
    0x4640c041842d2044d55030030f684030b0400e00c5051213204030403400b031881c100001d100c4d41500400d001c2c41c2c95050703603550410f44a000b0036a001e48922400d1590040d2190010b1500c11005100c03200b03080c1e010310301d0040b100c41030704000d83c0d0346c001da42c091800d1340c000c10440068a01000040c2c0261042103805d02e0315421440500b40450881d0034004011036401c18000c94007428100245048886440c020f0007040c010140807026400b443c07280d00407424090030003140d090b0007040340044240c002d89800c10b21550701d88458550110aa000c01c8034041207221848000b0345c14041c00c04444000e00704a21a40700d80d03c0c00062040110a003d81003100c4800d03180196542880240204070b0011800d00040030518640d54868122200040c462a0070800100940c1000320a07500210340010255040d82c0c03800c88442447d0010100031440c2120510040e000107071010f000d13601504003559200591440c08408620300311001c1d0001819510560318500001d0341701341c1280d88243d00040c080342175101c40c940 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 377194523 1250 377193273 377193277
    0x204270c0206132301140103151a060c0a02101205070807170405030c01020c1c1814010e040218010311030105031e032503020114060603010311030a0c0f03031205012108 74
    0x1c60095400c0000a4400010b0520610f0582740038554246820007aa00c658084507a0082607040d090204618a42140b034a6006045078800b1328040d82c0c940e14032507000a40c080914055400810156401e030840d080c0c41e440b4156000a007402d000d052810000800b40400e41a581c070600c4506a0f900003078104101407055550f450b00e980025901d82d1516046a910f030008101c030410006000e10b80704150038401c81e811210110507115a01489081c10102064503c11000690511030041441d140a8965200401c0704982d402036800001e400c107400103040e10324000d624070001c0d40600050040e580c0c081858101c1e0300740107a006a019408070400380c11801360342070240b090000313044128502003a07100700d400d004d88258000c1221600c03007a002d1814030401d549040c1c10881c06d00042c030000d00c4120034150100da00604035100002c103642c403c0401c401a80042c00300301d5000b03030208101600001c007a144028020420301c0150706008841184603030180040c29050168a603079003d200080c0c00f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 377195773 1250 377194523 377194583
    0x20402130305060108030a02150609131703070908060723130f08030309060f070203040509060409020a03060b040e0615041e0207031d031516030204270c020613 70
    0x800e40301c0c0f941e903c1d94907603181d03009480314a0240c051010440700600c40c814019106000003064810161030b040c89048420010000442d2030180c0328074120703c0000060061803052105580c2d0050042c2000009401c00501801c2c00040c008480c141c2481100c032119520b994484155215031642c80201c03046410359503030303884000d000100007004242c03030001100440c0308051031000c55019448107512540c581d2030480c3c0c544010380051206100700d1400c0c00580d508020000e1020640400e141c0004448055a0340211820713642c41d1548421800c0c11b0203a41d1160003004042e00e21440c0c40500d994861001c480102e202d42d0f41c80c4054504c00b0416200c1d0743c0703d820500b00440d21405245005400c1e08000304180042c2c0030300c01d0040400d4680092400c0988200300e10126041d1a0074018510b000c1c0c0c5406030100781a004d01002c10701c0c468000401c1183c10026110039021050010300b001214102071400003190446000c101c02076040304000ca601c40e43c00300c403c1079001d126100880e94110540 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 377197023 1250 377195773 377195783
    0x30b0a06180b030706080115050f040512070519051c081e131a0d05060a05060d1e02040b030c180d12020606041e05090c040510030b06030307030c0204021303 69
    0x11000310540603400b0402c401e0080d001c407000b10740c41d100b090394440801d210b1001020701121541e0946031142000e01141c603000308a860602d42c80c0c000080c0c0d4000c9801075142c41c1c1c0d01c086010005442c00c0380c40b00c40e01800c0c2e04001404c4c10305050100e410b6005101c404103e032020303d1030f00c0c1c1c02c00076200200c030001700c4044a20084009080311307840c407580c01841c11801095030504040f800c0021840e0112020500001c1145003030f00300100c1d803001d8000103003c641e00400b031355000295521000000d0072921a000c0c00014952411801c1007125110490a010054410b11041c80004184e000312500901c0824206480b0a550101c0070a6510600a42030704040744101c201d04010029070003002440454090300c225035a600300303110880b20701045241e2200d0b02340d60510810056644410b800007184020b41d411001010702003000d0383d8007601d0a03800d60700300910800901003036080d40c0783c12090480165240c1840ca45006001500000020348981e40c000380004000b4170500200000355804 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 377198273 1250 377197023 377197049
    0x16020301050f011401090b0306010c03020a050609030417060403050405060d090c09020c0d171311180108070f05030d140909010602010f0f1503080c25030210050a020601030b0a06 78
    0xc002e0042c1020080c864801e09040c034a440c1c001079030090b0040d03c103558502850b0b504540d00d00700115081c540c2c10f001a01540a4508910003041043c800b042c4108420350003103581c1e40c0b40801e0181c40d204400180d42e5190030240600c00000d600c8000c07141212000c44054bd240d8003103008400040c855000d004100009403480007a509190f50041d08101e030b045000c1e9540320080e4070050380c903e01100c00a02010b00100c3c002010504a148038052443c000c3c0d208890704145d6001242c03142c440c445542e881c210156004206000041203080e000e005001e0210380c0c1c031440c02c00407940d2080041120710a2100c41d10200304031004400c02d603403c0b954024401c0c00c07a541d503080702134000c04030390700c042c03034880d062908944007400980101501484c3e07a4500040c22172a54460600d180c110b082088400d00405804491500340d00302c500c00070f6403a00b141190b8884c0b46104000b4813070408861902440010b105c00f00c506500401c5190442c0d4000c45840a9961380c0c00340400104190b030403079449041d031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 377199523 1250 377198273 377198281
    0x80d09080d020c1b0f0906040507020a08070803090f0a0f2310051626281b0c080a080601020c040f0f1409030403082a0309030709061503021602030105 66
    0x83c50741c14005031141d107015405113034007032010403441500e050382c0002d090400700d0340301e040607800194440c4c02481139829800307240c1d603a580142e01105054440074000b20512810000901c072500c90065510001e2448003d25a030703501204001c40710207000b0070701f4240218480c4200c1c0c03042e1003031550007805503500201a000c0c8503000f007005480078000062011608542903005142d8551105003802000c400421803003060301e601c042c01448182c400000c080701d180380500c0c0e8920342e640c0148002000c92205850343d0884001400251128200240f0000900124000800710b0321038001c503140000190b543e110050780b90907400316002e81c10624101c04c01c565401d0541c07258542001000382481880303920300810010081c1030390840d40f01d4200b00010800603127202d004102071140544c213006401411750301443c03095640c40c0701e01055000016409142d240601076403019000100c0100a501d041108070141240403965210500d1750000d02a4540100c0035500303200654028024400380c41c0c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 377200773 1250 377199523 377199547
    0x70c021908010c09170c0402070203030723060f160c0c050901080c15070209190b03071203030f062301020109050f03040f0e09211c05070e030a080d09080d02 69
    0x2507001d0400b00004c100400105400d16100898180105218010906000e009007004000d500064049038507200c10040d040024120603c0c4401c2001d1902d132034000071941403072590804c48010510b48100d80b0f050100091582d0382d1919500d081041d160190410a0721300d040c144500c110f40180d98408000000000d800c1c2c4006180050044190b41321003002c0c1504071582c141b40511000250301c800850300040070015000d0030010180020040030400300380103004641170010315081442070101984500c024550580076030204510f403e0700c100060741c680204068803294071a200c58131680700301c2030300c4544d81c401d41203400c44542020a85500d2a078420030695603901c5807083c901034450500c0f0002d10810002c42080c4140c100c03a01a0a440b032140403141b01c3c2d40d404c81181044004180007114922802c0b485070900d2884200780000d0a0134804009030184643c40100c0f0320030340c09024001c00091980b0107440d0f001300c41c0780002c65000d40615080390b180c001c03d0060b090315440852844170900c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 377202023 1250 377200773 377200781
    0x15060705060f1006020c03030d0c090f03080301090b0f130c12062402070b040b090d080307020d12060f150201020c120304033b060903120d050108030a08070c02190801 73
    0x80b03c0128401c40495603010180d03140c050601850b9896003080c400c40e020121942c00090b108003c0c0d10304000c0c0c05460b6880c062003503070590000d03561100040014000d203c164072074205c00042c200c3d42d0341c4045c1100e000090320600c01c2109014090f40310181d46400c180101c1903040c0400e456a01030141700e0f1205003440360b802900064030704d00343e9162684440700b40082000300030344e88560090741c0f809051114058866111215160b0045210000c14002c00c50000165004401c02e42c0544800356182c0c00c02400030100c0300d4800e8031286000c1c8104540c500411400040b40c10029200042c00c071500405c0e8028000c555003042980a030954980c1030349050001584218071907118444000a00000c0340e0f4000351440c0c0150200090600410b801118114040b015070310040c10700c2e00d04055880404e050034907208620f1104000070608104484040c01042c0c0505214002541401c6040e500180f9040c000340542c01801400003c503030540d2510600140d500c5c2da011105500d059851004600030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 377203273 1250 377202023 377202031
    0x60409090b090c06030702031608040f060e10031109011404170703030210090c05060706150603020d14040c1806090218031e07061107050d1b090507050315060705060f 73
    0x83e01503416000118036205040d03900034070890b1700541c1402d030440000c000b080f134002c01c20342d00028244000282d582c16030313054030003070300329035030344a00c0b6000c0750b414010b0200c541040e000c02c1c907040c01403030b103844540e045c1511550b007003d180c6030307c440c209901300b100340380b1498000404121003070b020440d11910000d9140e0880e44a0b030b00311002c12131809101c004407007195000803c0c2d40300c2e0310420000e80c03500d036025010507400303100300049460348007001da0300b03c091540c06640442d4022641c1c0da803c010601c195075900d0141c10070f541d00c0e485c06640e0741da5512010b0203100c802c0c0c5082c0d00402c1402400380e0240001e0f0820040c210341c0c540803961491003400c820304050348648100c08003c000c40c0d200051103080080b0400c01490400c3c10721800703030344107816507040710010300c078001001609503144c2090301c4450b4010503000b070f048140799005030281120358005404c860f08040c188604150b008044036448102c00465072140d190450005040344141403024115106001c144420102440445409 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 377204523 1250 377203273 377203291
    0x50408010c031509110a031d070e180a05030a11030c0d0903060f1505151201030f0b0c0301060c030c032105090c04090b0a0c02010605150a032a0e060409090b 69
    0x3c896a80c030040d000b0744008001c140d0042806000f890805070003034104060880c08807613401040d01c05540410714014403a44649240f403688000c3c0a6034115044c0100e40c440f02e401c01600c02400c007a01c41990782c0c416802120304004000074484203000c814020788096000c004181c0b600600c1e013050060481c40980800d6a0007032405014840401162140329134104051901c1e12a040c0b43c81d04000704080e4114100045440420440024264007620a030103540b18910b80c00c680c0c4610f044c0880d161000800002804c41e003000188034268010300c01c1900581d15151503801c1c0e400c00d00c5e0484a1050031000b00100100300001c0180070705081d001580318892000455405e441b0303120030032055075128400501259550004a040001c1e2500284060039140c0000301d1050b1384d4501203003588203550030455020402150060446a05001c0d03100c56800c185009440012b030700c403400041390200c003007070810301c1a0030103003440640746c001c01d82e0f008002603501000005102c0c140540200c00071500188 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 377205773 1250 377204523 377204561
    0xf1406100e10110d0512150105090429010503011d04150501080609120901140c160e0429131502040f030506090102040605030f04030201090203060a0f0e0c150a050408010c03 76
    0x1181c0c4a8819106c5d10404030fa503030052030302c1341440780143d4401c000340d09040020400020401d91542d00400c01003592a0030000e424409400389000a2000e0100c41410044200010400319a0742c1092150202050069241c07a440328501b000c4008100c6404e410410704140002658203004511a032082d040d10b401d541881d2150100e950441c411120303100c0c00700c0c046120920007807001c400030f409140b1406049603600300c041c600d00d844800c03450b40076440d0200c0140400c401c0041444040c6541800417075000146500380c0f5000347c0180c0000c2800030000305180503c024081c2448444540d0009400210f50f91600c07000c41c00f01e02d68690000340c513070740302c3e10300801c50420703051088808a49440c0d0b02c40342180c44d100c0703814440350809041541150740b101516009a81c09112041c001c018521001600414160310b50058a0701c0c0b00741c41d501d5802c8a07122602c95110306402d8864108880c414950320245030400380c6290145800c417891b698a41804800081c1d0954408160340854040c012 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 377207023 1250 377205773 377205793
    0xc0905040b1303090b130906081f0b100507050c040527070503060403031d06010b18040c0e0f0d080304050102070b100803040b0a0516150f1406100e1011 67
    0x146002c1c80c070242c000c00140160b1400c006150100d03014120001c4d590310b80071115940e90100d01c09132616500546041c1d00924418291030f03840740600702408070702c03810621102074407200007541c47d0021010001031100000e1404200705050000266849004000304181d003404005524001100740d150140020b610b0f01000b1035000c0002d149041320340050092501c3d944540e030441c0035110790f5544050150b508070400c80c0d2114144400d0f8064a84034040c1912442e0120302c0f148201d1403100b8142c0158981040c080103190300c03003071510410b40300b03407000b804682000000c150184a41c0801910144001c001d00c4208041034005141c1c860080c080300d0f02c6501e80b81c1991081000700d12541c2ca459004000c100100124003001e41090013035402c0003820059141d031a281d00384910310045940500c0c03160700c19120050b502c16641012044181005002450b9030704004851000d401ca501c50080e400396615114440d6001560a54010704181ca4085840c00c02900000c0903d0000c945801002692 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 377208273 1250 377207023 377207041
    0x32d0d090c1509140d0c0311060f0301090c02011103070c0609051c030915050f0f071407080a12230a0b040c0c1a0f040809030111160605060d0b010303080a090c0905040b 74
    0x60104030741080c0050180d0349941c0c0c0c0ca4120061507054230f500b0140901070b010044040b01c01450090a10502c0481d104c60348007402402c445003000b10441c412020300c14808000ea10a03898803c2c02d607c2000081c2c0700c400d508106190040100c5000c100c05800080203000950503040712000303034404c6444c0c08403d628081c5032815101c0c129100d241d240740d00000500b4902a4900c1e19030006100e082010010280d0308c1244c000703600c40c6800303548a801c0090076098855200261507108010448204030300b5107500d4032600b03624600c40048494030000b04c04034209034040d510407041e0400081003007060914004014159054445040e1100a10246d2903000e440d41105510703c240b80a03401124030780d580707075110441c1d604100e14954040d0b581d4065021141c2401d002020840400004c5000031f544526100060b554020b025902405540d40490700040c3c80007012415250302d4208001207554903000c03040101030f04c00000d0f101810785400050281c01550140307024a001c1c9404803400e507200000e03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 377209523 1250 377208273 377208289
    0x706030b1c030212071e11011206051507080c030706151d060105031e01030302160602010207110d0305120c04090c020102070b01050f130e032d0d090c150914 69
    0x10b0056004500746242c01c2544a0042103d54800e0380181301d42c03850240107150521303241100326906580d0b80755814081da080004805207020010050001a0034200440d17082c1e110108440300c80c000106202d002c02142d18180c0e65101042011241c86405505141c4c0c040c0c0529041409800446100410304111049081c41c3c41f01c005451000240c6803540111101e90000f001d0300c04407503406800c10003114843d0f03c21802140039034000c0040c0700c0c0c0ba0183c4c54215115501c50401d581c4100031580009601c400403c803000300480e0710500c00000da09041d51188100c80c4003529070142e10302009541d4119070045c2060b42c50544040008182c101020f900700c0c4500c00000c1e140d80c410300010807092815134182c60b00690081c1c0501074560500d1149429210188080e0603907030004603901b42c00425a1020340002c2008895034002d00120b10702d101010300c1000c80c005216611034003000107000c8008950f80040108208000300329003401c80080c00344241c3d0280300441008800941100d20700490 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 377210773 1250 377209523 377209579
    0x40b0306010e040f0204020702030d030e010605220c05040503060c180a0506090d020f06070332030406020c191202060709230d050f060f0a23040203010e0706030b 71
    0x51040d440d403103a8540c0c1c0440410130704102e07400382d006c010800041c0c50034010b0281182003520082260980010101d094441300d4002c18011845544075566604903003260281c441030b0050005003031062107008440707511403608110342500c2260180544d1508840042204440c50101c1152140790401040800a0a0f02c215540700344180a0044603141c20b50003504150f20023041010040e580b5000304d01203810111043d408205400415080c00302c00c4840d0002200031801c41d00041000311800b80750900000d0300162003150301143c020f20044040090078005055550f181e0340c51a038a10f481d51a4600500345030006001e41404155414000c5540f007080d0b40e80c412980e03010140e0145558459000c1e019000e901c44a926204400315000340405540301d035000c07002c1c002510703040c601010b034050007a14243c0100c0c60a20070707450000d590050011980705001a400803500c450000901401442280341c1042c003810500241c840c2c0c250b80f001c80000b80c1601c04e180d0341030b004180003100e0543c8007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 377212023 1250 377210773 377210789
    0x305070b0a120b030c040f02070224070f061107230106050604090c03061d0402121c0c02192402030f070b1b0408060420010f1b06051005040b030601 65
    0x94064400d042c0303607400c1401c4031140130781281e03c491711680c0007074141c45510010001d0583d0016400d412742c00c00e5290380c0780004207000100040c05028030156107611400d03a0103450403040c0c4140008000051300b11100f1340303409008507034076080c0904255010440b03540c145060030a480d0421030310741d10107004e03d004481c002403205061501e080e044c80080d000c650003d00401d07560700b4000c01c1a0655061012480340c0301800c2410707615141c4140101c83c110701066800300d601c060602aa131008001c0c011101e84498134018030b0784413541c07011841d4003140c11302d00030f12030442040202d00c0304065550041c00c559070404031040070702c105400381c6c0c507403041802c1010100d100b04142c0001c5140c2e04070803a005108882c914101d9144044140001e030455081191603402c00c405110170301c400742c0c0040604805001c95092200904070000e0002250501c0040900a103012004410711a6030f20038196190046420300ca903161000200c14445100d001d43c611403441d00c54111018103000441038107882004e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 377213273 1250 377212023 377212037
    0x10e040c05060c070e01030c0801060b0304081c0e1509070605090102280c0f05030c0402120a0e0c04060806061f080705030903040504020f07260f13080706090305070b0a 74
    0x8803090081d10f9220016552141c4100400082c140c030032a80014001e40c060210803c249050034111429500c02e58042d00500300d041c0280008610203004881039844101001c048004445841380041c00d51201c04552078010301c28200309500c0d015003c0f51103460b15100395000b664842e101920140165090580142c0c03180b8180c1011302400c05003101e102542c0744182031802c407280c0e0352105815a41d005510f090540c008100003504003000280c000210450701542403000c4450040680c1c140142441d060a4540410848180060200c64a840e0003e00140078260b143d0320050b40d50b4500f6260030380201d2010325060b264a1b12203000c01200642590303106003507220f061040313510b508050000c10b910b0000300700015080c0e03280d10092003c0500d5003440380e260300b02c0741403640105018103402e4130f13032040240c41a031501c0c0c4500102c920504a903000d294641808a07400521041c142c0c102e500035100e800c4000c10180d4218044d4000ca922401c00c9810b210749860a8004500502e007114001c2065 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 377214523 1250 377213273 377213279
    0xe0106050a1a071b0b130803090f040b0d021c051009030206180f0115050f0f09010b181002010617030415080703020d0f0c020c0102070b0f07081b15010e040c 69
    0x503520003000458080c50540f03818580300c0c168032001c1006540070502e00c140001b11600310559000c542d600814015018509001510010625101400c0c21080c4a01d03541c010a044075524480c24200c89074000c0c1511001d02e000107610f007500000311409540382d00c68100840760300603d80c01640322040e4982c0c060021520384915400300c0603004207040c111030045415845c2061030901c1841c080e044c20425030f40e4804d10381824020024240340d03d05006030b9603004181000c3e11400170303da0440d800c1407030041d52201d11419001c52407620781c90090340210700c00000445564150880003e03100c05d00070749001c0c3c584c80020755640744281d10807a5505c0c001404050401c6000d006178030380c030003501d00f0013502c4e012401a52208031650380404c290070f10742c0c0e141800319040d8100f0540340310400c00c3c0000c1101d90706014030001c01d0f028400415045160001d401020040a1800d0743c2030090b00300e80c2902c44e818101c00d03258032001d000f00d41c4040781c035004c80009500326400491f18003c6400210750f100301c0c0d003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 377215773 1250 377214523 377214569
    0x6090b0d0f050708030c1605030a200a030212030c01140f0f04030311030a092102060f040501060e040f0b220209071b1505070203090a090903090e0106030e0106050a 72
    0x3421400d4a40f4020b04900058003902070000b0b2103c04044005019450041020704e0441520390700b081d0b001c0d500090a000000d0036103030400360000a041007d042110707281c1d00290802c1e80503000250009030620741860a16800400f40000002c280b0007400098200032124401c500e0407510080d0449050f030106024613124281c481d00301e0300929010400a0184240000a038815035481620316a00c0c000ca106025040082041d1030b04100207028510118400082d035034140542908140611503003c1000c01200350b00000c0200111008858140f40608080028001c40fa505981200e0005c0005010351141c0d1680d00103241500c84139000402c5680070310243e40002000c0c0424045800388401171040d1001c079050200348112007054180c00c0180b47c1400f038510180c01803055520500c01c100a940d1004540003c0da940300714002880401d60504807101d461a0b44032058850041001248607581600258074014488009200b0555240144034803044644a03603a820315840e00e018040780 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 377217023 1250 377215773 377215793
    0x150b0607060f18141c05040504150504090b010f0f031a06220207050c040203010608061c060203070c1a010305030f0c010e010614030708010504030c031202160c050406090b0d 76
    0x1c0d007890000380580035550f89540300300004006541818503190b07016800c1100300444003000c071000a1a821030309181c01c002c1c02e1801103000319889142c5900c00911802d420180c1e000042200620034401030165040c0501c0c288028014262030301c00341a40480c0c0965100c001804803640210542e180080205070020122405001580c1c4031048200003400c82000c410380107825002814010b90344c40c8146401403510a4248400d030140f801400104000b640103083d5580c8203005448040d500003296040184401840e10000c1c0b01a1001c82844107072980309407941501841019420004030003440c0040d45141d09100040c0103600c1000001c2290000308041c04a44a41034004501952070748185030a43d00141c020201c28a40582c45015901c0c0c00c00c0000c004214082c020001d5081c0b644005200000e4420b01a0600c035129030702c500d82c4e060300e034119500d0400001001c180c8003900d1421903207080c03851142d60702c036909222000c02c2003512446595080c41c0b0081810308a50803a0340d0718803041d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 377218273 1250 377217023 377217041
    0x3092503080c1c050a0906082215020c06011716090e030927010b04030b2206090c0e10081e0304050a0b0301050a0906030809131b02010207150b060706 66
    0x43c0207103d40346041a52101d42c4035034182c00c40c0c41d690303164003015800411860300c0745c0c00b00c0c08103c02003052180124452000d13030407100da0000c2840ca0303e803050525590755500346484c02002440014000108200031403558103039401d401c40d000c0024200e51840780c1c0c03132901c5010010150500c407010402c102450744092941107036802581c0c18218140300085150b000d4545810240d40d0414401c2e0b0b60b0140d542a40c0e002d030060995450400c0e045032964480482c000b044060b020100500d0701000340920b0106d03100282c0e204000f40440c03030702440e12072402c44403841290b001640e504080b40c2140000d0700010142e41c42c407001030040300180e030003491018000188403041400204404100d540300d0b520040701406181900c5035a9500d02803e001c210159030384040102413400c80300f0700000c2d00440454481400447d10070328038040e40d424150041442c0d28128180c00480640307445010b4042d0090b000c1c050055450607040c200b429440000c0c2d4444440b41680110304005200000b9a40c0e0b2002040c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 377219523 1250 377218273 377218297
    0x30c02070f0902040f06030606020a030c1106030703021207032d0f0203070519021f02090f0307090c0e0913080d2c190b0109270303020309250308 64
    0x1103036540c0c01040c1c0303400c89422080003580c00003410311405240c0c3d28000c000304800e250401515140400c0203448403901d000040801035801c2154080c400d003210003030318101c00200090390b00d00740741c54090002c0d48000342030381c00403d2140015002034000d209a15a02d000740041030142c04415100d800c0c04c1d02a00c48412103140d4070104148a004c4c40e10240d441601b0a44466a0302e2030054841c203086048400c800e821980880c5032481d5900742200e0346001008104805030329100000d00203046031500310903d0b80c0511034098005403404294000390fa000c540307a00c0303000031031100c0d03418841c0b4280d00300c4a0b80c1786060711032090b9000401c41d900420741c2c0202d0000000340d042c40b49600682c410880d00b80d4000c155900c1103101c010b0320081c0001d00845840022662504c0c000f9611580310340014402e880d403940c0e64101d111a180d05038420030003041c02c0b2500c0380c03103800304a1801130029001544c076080f2501c50b043c45810000b9901c452120480040d040600f00300c0d285559469440e8850755003140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 377220773 1250 377219523 377219533
    0x1503070504021c1404030216061704020418030302031909080307050708122a0901020604020f030106120f0b0f01080a0f02010e03030c010501060e04020403021305090109021806010e0f060a030c02 85
    0x5195a40c0d1081300d260001ca0f00056071070b030800f424000d103000c0018101c500c0c403024603802000159009120004000440301c0d40840640d15400020010b001c44c904503200810641003107010198180d0003903200b4a00d514070f04480e904e00915a004850500740020001c050400c0131843da00c0c00785024080c42c92042c40341c2c0e80b030000015404181c5840a440410710202d8007070310500e0311907900122002e601110319000703041240900000303680d000d020b40080c0c01520a008513407940e440070b41004018102c03001421601ca0b1091034072820178103910000380c4031140c211001c100e0032008c0d0036815040703403c8203000341030071640e90300d0b0040035515a22003281881140c003601c00c42074500b4409015108840700001505600d08240585051140382d41b107031003548104000d0005940c2c40720058641441e0403400103039035030780d12020f0f030040074140b202035403000f42c00300d03008240074603101181d11851003a89c1c2c4601c0d0030401424020803452043c082c95110000340460381c5020712951150400201520440e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 377222023 1250 377220773 377220817
    0x80121020913050d0908100c0c1101140a1806080103020d1127040507050906060d09110415031106030f1302031c0302120f16120209180f150307050402 66
    0x51601305030040000c0440e204001c100301260003404041c01048054900707103c1ca0f40e2503240201580b0441800810700e120810b0031a455910811104040d6010500166a1400624400303011810500503407080150b5110703010425030b10451141341202c0d4042c0940c0303d00111542c03445540d21501c0d5010380c210300d0b260503984980001070764041c0c080340620742d50611410582040c0381400c0a50700701c10f0058080200380259615040226842d81c400c0d600000354140031440c000032805071504d4510b81c01418184224840155503901030201c1c1d00c40c10107000e544ea03100d030901c512030000311004a020aa00c030f0000b501d0400c800c03442420644001c09850b00590003045585100c4150703810080003a901141e00c880160040d0200368008944600c7d00c0081c2c40c00d03200d64070000c0301504c039010401c410940710a0a51180e1380569694a200520202135540d441c5801c0da4040c0c000c803148003400c4085ca003c03030481034110b9405c800c2140b002d400b030828039040c4030601000e54058454081084900c040407 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 377223273 1250 377222023 377222033
    0x90705071e021801230a050d0b061206010501120c050d0f2301150c021f02150622180606080705010201110a020d0e0a031a07080121020913 61
    0x40c0051081d120000641002140140001e8209103c88444981c004000501450300d01e801810540a5803840c0394464240d560042031a680c2c41c3c0c0d00044e0080d0b02100c6403c200040400341520520056506080300100c8403a0140d440d4400c1c0700d820302084040700109032204843c1c116a09840245c1480c0d45440c1c4041c4102048603a00c15401080719510013640d808800180b165011040001ca8030481c01d5040400b4150ac0c503082c00c072240300788030100800208549070507003074102100002015800204085101948a0000c0c5a18403c2e228019000840130300d0050a0100c1c80c3c04040e01940013546025008002000c00703008140d400d227401f10b4110700090700c03800781c60040e1203103c01401200345401300190940702210010141d0f110140301c50404c2c3c0303900259114001c0000d00e8071100e030424003004100306213090703000580000c1d1100d141041d040220200b0074014000c9a5424213aa0ba9809040151204159075003035030301c86548070f800151030300151040e0402d401c0085800b08550070354903 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 377224523 1250 377223273 377223293
    0x1080a1d010c0f090509151f0305040201020705041a01030e0c0607051c030b1c0618060203060a080706050703200304030b04060c1419120f0e0c10080609070507 70
    0x21a00d0140e454400d101501503200d41851465420303814043c04480c2020006400d001009002d140002ca154050a806596103981854450140c5c2459084022407203030003009414100c40c2a0301500c9001030002d841d09180c82044224212140004104441d100045010b401114038860b454401c0d115003003442e60350000104081ea109200130120503000300b001c0d0702c0c00500d0074203000515203040000120707a1109800c88031b20020402a1280c800780c24580071008040719110710b0301c4074142c2c880190400001d41c0c01035000715012904005c440781d450003c175596004900926000a00a11220340080c0c021110f0200086d0012000311014000600703036803454215900c20b80d42652103505200900c1414815400e0b254010f02d45201400710390f80c0034910b14420060f14003408d103c229941315245116000d02c1e0b042040010061150715a050f1000010340092801d00d03410303000b6102030414910342004000741030350240c0c8030158240e8940f0100101454010160028001e00704820341c002141c0c480 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 377225773 1250 377224523 377224571
    0xc0d0f0311160801061410180308030109021c0b03030a0302090307120c030b0114031207031205040b060102070509041533060801060f0c0b06010e04060b09010e01180501080a 76
    0x1c1060b00c0b145064015030039500190322841d03400580500301c2d10075459516500c10340d4045e5007080d4081d92850a040b007540c2c0481d41c00036100100101c00803d84490f150010201c00c40c09240c50107020b03011540d01421103140d10030a9070315a0040002140b040d0007a0054500c80d000201912001c40e590f4082c14481c00300c0550448209100c04024801c01c0a024500c0c0d001d420402c8451043d0b540b4507011903030300e940c0f446a8100d65180800d000f003c02d0300c250101100604550010b108034146480c0c1080442026203004c0c1c0580101c01c4003080500300110782e1481250003441c0e0402c03100b00303002000010210401e80c3c400c01181d02c2d40507148020141d0780c0c02c01c444002d00301c41d941c0380d180c840000c02150040e004403003045443c1280113002648600302444507034110514480d03986176600181c403402c02c0c2012494109051a000250450f5200b001d00071505003030300c0d00500c0c0907070140111102001d4403c0d014440302c070070006100d01d5204002c030076409030071010005074200445426220700000b1710 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 377227023 1250 377225773 377225803
    0x2a0304061b080106090902180d20040b01080402100e061204031706030607030b0f19081005011224020705060601020c060f120603120a050d0b030c0d0f0311 68
    0x2a104180600c070035480d00c08100024501540700754104400248a0310007031042450040c1c0110700401c0e03102c102c1070100c100398002041d04080d01404d12380642400000d07058265050a01c8010801d40c4c01c0c14040c0075080d0605030350b01c07250350381c81d90708000c01c022182c44140304001ea4541400540c1c0c40b00d00c01001484510310340020340e40703070518000b0302440080407000c1e007858400c1c00780b142c2503c0000f86c5507045420350902243d0704181002103540140e00240403948440180e0707800c416405040e2800d41a600500240c4040480200458090320028490086d1020070340e45141c001c51a4903040c04501c004031401c030304104001300b40000c1039800c80d020903a441d400032814000150380401501c0c0305000f05070f900301c1c14555040180d811728018038606203580f210070300018a0036034090220343c0103034034450384d40c5840d0381d00080000d0540e040100140705091070016000014540040c140c1200b400080030740c1e100344001d503190302690541c240c040b03003441024140e8140240c030038882106000100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 377228273 1250 377227023 377227031
    0xc09070503090d03060b0d0b15030c1305040209010f080703020f0304210e09130804030b040501150b090a05220c120f05040b1f03080c0102130902122a030406 69
    0x45940e0904060f21150a14141460000d013000f80c942c850066407050042c8250008420a003a80811003c02c50f244c01d805240c00c0001c100b040c201c00c1e90018295030152031816580d840e840354240001c13413140c4804c65020807012240079240501c01e4400780d40c800b02900e0058180700c8800754000d581e420948040700c0418083c02e000041d0315000c4900c0c0d95410031490701145410840c0c1c0441c40703605001d041d1000c40350700401b00d0802d108801049600a5612046d00426440c150800c02c0c004c141640b0800355510071300f0800500c1c2c520b041c05444070480006c003d025500e2900c0d0401c10301d2030f500100306210480c054044684ca29842c4140700b14510507448400803a411059910121001d807410601400d1074101404082200051003d03400b41403404a00c83c030241400a1848000707030307940010700d100c0000600b00800c52040d0080e06210f001c03d881c6001b0701e030310b403181d02080c0e00841c603070040440b10b24400500320040407198881c0084d007241050394a07a2010907269032a500454041d655141c40e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 377229523 1250 377228273 377228281
    0xb0f0d15020a050a0809011404080a09081504030305010b070819110d030b030105311407080c09010b071a04141002040509010f150302030601020118050c030706050f0901030e0c09070503 81
    0x110fa2044006e0f008015028000c4250021a14047d0001d081c0c003002140b01c031074090142c022000505464000c54800303203100c1035000741040c4226401c0300040d04180002950710000025140d2b00307680000c000b401e09181c00c036280a600c0c600c0c03101c08108505e240001c0d005100031b01c092040d00f11207a030003043c03000c00b40041c503080d10400741031308013001a1003900300280101c5a282030010400e00342c5095810107542007001200b9031b0143c0f8240140903503c00081c0d24900064000082171041c1d603c820b541e130b07032040e07481c0c0d09014020010300350701d501c0c0c205800c5402c010300c007030f0784d01c10712038001e00070904c01e4000c0980ca80000814180c4130301d68006014841703485c20b5a0031500404011381001042400c000542c403500344001109014140c0200104406070700030340000a90554000c01d1880303031121801c00076541d20014038468001d0040040c0441c645110b00211500d01c000c40250900e03001001004500414a8007003201d00e50191702d244403410340e190a200340c05046256103072034413828 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 377230773 1250 377229523 377229527
    0xc0303020f0d0806010e0d1a011205070501080402090703050916060f020f011a190801110d1508060105130608070803040f08060f01051c171308010b0f0d15020a050a 72
    0x1c2c46103200c02c14048414200403a507071703112424401e900d2081c1c0e050541d0185a01e84108041101c0d03940c0c001829072080003140e01c011001b8106803c41c029811580300981e62001075880050a650180d0421560000280300d18040d4001d19000581c81e004c5401d11144008041d841200700d030484400118807801d00b042c43e03a0304000c0701c210041d483c8001c20001c241c04513a4201140300a943c02d02078840a8400340f07604140c808080001c03e4103100902200c44801000c0000b588608510b01c5200c0c030b4019810703443c000c06d0880405a40d2400028256039087c0717400c1203445400882d0581402d0f840307400225211005200810090039024000d644030380c28540303d68900e6909410030750340c1e03070304c80c10803c028040302c50071032811510240c6d0070740240c4840c82c05964079a4810320018103a880d030b1540305400209008024540780c1c218006140601e91203551160036109000c20f0740e5070101c07000117441a1443c0c11605218074602c0342d604103208005d000d5a600c141d822180600c80402e001056205e1115 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 377232023 1250 377230773 377230783
    0x40e07050111070b040e190c03050106120b0a0504020c012403170c15100e10050108160e040e01020909070507020a0b03091b0f061b011503030c110d0c0303020f 70
    0x82c120181400c1030030400c80389101d01440c411b0540403100c3c2e1020490718218080243c5060301a007506100007201c402002d00501001e1141500065140354550b104180d14820450351240081201d2170052405082101a4102d500c90f000d03035558441100d10342060300036001034400c110901402c6005d1a60405107920701184000080f5103400700001c2881071008181e64403054216003a06a07140c440c1101c160b60040641c001380d12040c030301130500100029981669003100d8090b40d41500594401440803550560109d109020480c44940c2c0111403511340c100c0342c03003926484001402c1c210303403030b001502c007080036a4520301007880000c8000070b504050001c0e0014000483d8810726500b005040b49541360762020b01c4000c2c0d034410740400e0390941c0e175541018983c028000d000c2c40c0ca0750390302c0c000b070035001269004403001c541c42c003010082c6505880c03618100303c070303059101c3c0d56500e0101d0f21000328003041d21000300c1d4040c200038500c1002810480280002e503020382c3c01000525030611368103180c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 377233273 1250 377232023 377232047
    0x609060d050402040e0a05030304030c11041a1e01021005040f02030601062d0801030807030c0c0f170705030d050c031e07020103050601020c0f12030c07060309031e0e0d11040e070501 80
    0x160025807607000440c100200b1203820030b915140000c0400702d43d080607103c91402500c540e43c801d080084020444400d034446020804040354503078103002090000d800c088100c20211400353e00100365110b422011f503409035a01600440304c020321410306078000b030704041003608000045180c000180718401161780d268445940152489881650440b2016110503414031004050f200d00103008410584905042200d0399408003009580d40c0c1c41e801c044000030094020171403a0311a59402d040c903c800000c920085070005806801e041203400d00c2298039501c2540f0303542e1035101c200641c00c105403000c1642c5240c03440441d2155110540303480010306071203001d09000d0466000d41f40340040d136501d200c003c06003e0b80440f980c1005101c10048542140a03800785c58216004d80103000604a0b0540c001e503440e0741c03003541c07840041400c1034161581c0d81e0000d81403178000303100c02002040905000001c011014025134141080301140400182030724005911010306d44c00c143c42c100500d5800000340414 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 377234523 1250 377233273 377233301
    0x11120705030c03010302130e0a0b090c01080c04150c0b0f15060c100203130f0b01290706020a09030516240e0d060905240f160e0609060d05040204 64
    0x10398100303820b000d0382d2400103010180c480d800162500f4503045c3d0a038010201d01d0f02c1e550503619040c100c2c3c280703202e400c00f00b2105400795000d00210340c0da003503101e944801c0c4a01e54883c04a030401c1d081040040c02001140c0044092000f2603e001010039011120301d4030030801c4c400802558549241d03030b0042428000c0e80030703001c0e100030700008030008004152002c510101c030300010380713a0356018444040d95090b11400362058500f94424410303c440c024009058030403007407003d8800c1d8a0700071581c400c00f02d800042c4914400510542c40000c0320ba2700103007190300b441d2030981d00075a02e0783c4a85040c948080000310840341e1024040092210042c581c403103900f41c03850074040f035040c1c0442c0038007555400802103114070700c030030b0781c010410a40781d00c80f00e04183c2001c12074501e01e0000038400103a0245c2031a03603100c200c4090006401c1c60700604428403403c6003442015400303100c01d1040d03c1c141c400c01c00303440e804117043c08105c0b00780c2c680d000a445000380354000400d141c14940140400c41e00c0e1000c1c5601 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 377235773 1250 377234523 377234527
    0xf0601090f140108040618050109060b010801030b0103110a1d06040c09060f050d0f0207030f08060d0c0620060a150806040c03080d1b0309060c181701090611120705 72
    0x8071440945102e441c21a007800d000e281070307959181000007480b0003140c13400340d42124141d86090003015805620140d101e4801040711032079110040d03807040340034070004124071010b01c0140000b614031075400d040c0750f10141c007141c00240c03140140300044001c07034031180c6250403010420181e445d0502070742010321440c1c02e000108509103240202031500d0000c004c1c0510100103542d401c0802c0d03a9118040c104a03d82007151110102e02d00240402600d280107400141608041a03141c40c1c0050070b5194242c0c408030740e800301e503d840002d550f00d603240c00c88072503a08066400c0700000a01882158411420b800c80040c5448140804c26140107060b00802400c1c3c1c443e101300320000d9030f0060750400744c0f50032180c3c1540310311540034481e002c1e040d0361240c45000c1400d10207150344c290300740e0890700500388644070a00c48070403100001c881610010015959507255031008108041d0701e82082c6803981e01007070011680310156100c035015034220507034002602e10009044800a841c00b040036402006a140c194 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 377237023 1250 377235773 377235779
    0x9060703051006031104170c1e100e03010b0a080f0d030e2113030b0604180f0210091a1201050109030804030204150e0406090b0105180a0b0d0b0f0601090f 68
    0x4142c0e680e000b400c0600d07690310340c00101c0c000c48030300303580c020000b042030001c1c4000000300f0203449545507540540142c0400c0e28401d00c40700d26070900c640c280c0d03000e44a004203040b003100807202104000181030b095565020002880d850b10b00c44c41000e000a03000400d0103a03030300e100580c600a01815450105450014400e00b450f0b00491542070f001d9442c0490414400000c8480516101381d82c4c11411210b10401d00104100a01034014841c1008490800c4400c09103921865419034020b40280f8803a0360042410051800e003052844400444c9003180505c1d4413880c8500c03400481800c40c110f581c03008100f5001c0142220402409040286031501010380b550b610003190340154040203104941722804416041c0c034504001004002e0300078804680e04043c10810018404481c094910801ca50008951801c2582203a0750030307007143c600d510311551000d111400405200b01c0741c0d80d20042e1960900e000c00e01c00c1381c039140205210101811103040801c00900711407a981e21440c00002000700170 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 377238273 1250 377237023 377237041
    0x140402040515030717250c020d1b080f0f010b030c01120504110a090f060f0501090b03101a0414011e0e12030d020a170c04120311060a050906070305 65
    0x140005074802c19075166114060291507501140b9503a00500450000f04115004601c0b241e420900c01740803175121080306c0309000ca404a80194000c1d412918490040300003c071003681060306a090807007120205a00c2d68866400d2005d001c420342c8081d481610f61110183c001e12510300582801c8000b0074400b440440060b10701031080c0207400000e0f03036078400a0140004480595400c0100403ea1000e80383c480e1400301c0200307011103d070303441c16240040120b54062111040400e03107005845410360186489051083ea620003003075481101d503411b100186e8002c10303025030400700e07807020001500c990520ba6801440b0440d04521810418101203c00b2000c080354400559003c981c501080040900408030391100400c3d400003c0c10300c4006540d601181d40f5902034030b034801841c1e541c8155240e064182c80e0724118292600d20400608100070007000384051003106c40b282c400e04020389010fa50441e42400c10340d048840d446016220341c10400922028401194001268241006141803900708 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 377239523 1250 377238273 377238289
    0x4020a03020d06020909011d0f0c03162105010e0903070f110f030d02100b0103060f090e120403050604060506120d081e041208011703090418060e071404020405 70
    0x8082d000b0301a4410b10b03030030b010300790f01100c01401d0301034440c0000b540e6500080342c440e0704214003040c0068141001c20010a40f51041c80d000f111a0012241140c803984d00d1807030700039401041202031000704800c10982c40c54195416000360707080000085c807507141042049010740c0007008070300180c104000f0040040c0904912403103458001302d4000081d004c0c41c011510240b1030305801035040c49513404d02c609136540060500b4510100b00c0e01800781d08045c0303006505490300350203200002494410280403400441d407058030f080c4000700840c2c1d040c0d0380090005003d9840707504190761a400c060108400c1c051140a4a600441c06452610001d041640c5164456250741301400421180c3c0c0007041d0310800c0714154401150411961020600f002e18010317544040303a03461400401d00400000800600c0000030f00c035000602c0001e03600d0420442d007080018440d0514a409040b041c04101c40459198412074002030b03940300081a07400d041c0048540300540c0c03480343c54469801044140701544031584 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 377240773 1250 377239523 377239529
    0x140421050a1409040e010c09060201060503191a070f090f0320011e020102040f08190b090a0c08010f050606160f0f0506040c140105040f0605031f1401031404020a 71
    0x1502c50052821000c00300700724483e0520496005042000002c11400b06510103415a401620b031403994507540e01060f82684c8444c85a2945500701541c2c201c448844014081c0500c0e1050034031340c2c480200010342e005956001d4403c4000203406016415820713400c0711024024110f00c04400c3c40c840c1c80c5907261586180d14240d00711200c0b0150001d004641d00071b100c8030b580c40d029080ca051842d041924003d00170340040c403505440d04803411000403e001d002c00e501c06d09071800c002440f421466911307070080800000c0c12034032941c41a55240c80100744282c01071340c007916017400045011241040020706861020700690701c112010440704201c0340b600c4603800c01c4e03070f50310880c4072070820818200000845d4000e60050490b01544e4100010000f925009030b081e104d003610031000c0700c40304200444250086008580ca1501d00c5031080c070285000b0f00146a000d504040100d9051411003c944540015503100c51003880d8000340e1001d0944c3c0501640c00343e920b04c1c0911466624094000403060450340c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 377242023 1250 377240773 377240777
    0x82b090e01030303150306230c09010503040f030e03100203090115061b03022b11010c05180f04090b090c031c050a050c0109080702040b0d0b040305030712140421050a 73
    0x8070b80c121200307401036454006580007001000b881d82c2e05105103034618148110b02344019600e50000e004211b514080c0c0d45843d01c1a9607044c2590b031150f68824500005500907002d014000302502040d035410003a4266200060102581f24100f0448481c20b4541e030f080300c10b040612102041c040d240d40050340b0011280061540000841c0c1414264106000c0034401001403146410020f01c090700c030164510100901d642e00c030040940c598000742210b14803503050f40000c0e020044000e4860380d440c00d4000c4407900070000c40703003040200c0c005030854000342c0c0d0848401c070b4440100115402c00b0b008059007407405801a0090700c1d800c20440c04001107204880b8240311022400e10221440340c0e06650f000300246000300039009482c2000380940c0c0080070b0032403086080201c4841039080c22001e1124151b4007440620054450ba903054038160030050240d0200400c10006c80510141341c00703005900c2c01c0b200740030310700790400382032141c5124031480d0081d0881074000001c1c050300d0360210484507038001e94 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 377243273 1250 377242023 377242031
    0x90607050318060a0c0906020a0210120b0901080a0b0f010e060f0105161103070f050a03081303080c060118020f0d1e1401080f0a0308070c050c1e01030b0a05010203040e0a06082b090e01030303 84
    0x323318054001e2030030301082c54109440c01c001140158000030b0040c4068040c84600782155104c0110340450182400b54900130f0002c2400300c0d0003424101c9411461400504086c0d040624003d500941d0001c01a420b0340d030115840302c0e00226090510220000e420710b00b104500e100d0070940800c0d00781031684030090020301c2c00038401c0000020541c401d8051544004d02d1031752000e111b80c19a035540d01c01e02a5035a20b00005807100380031525882211201c5000070030a6051035540304004c8018822009050340400b80c001140e940c107612481141d103a0720040340d1203155541080e4003546400f07034010200c0002e902c900b0031400440e8101603100da00403001d1820941c1030003185006418440d01d02038040c2c11002e100c140301c0321180600300b80201b6035001e0b6010404000b0b04800c018a070580d41c4509070260308100020b12038180740038040d550100c6041030208020741d841d02050724000e50400742c80c0513424581e61001c4d00ca4401000d00c600d0342c0340e52500d0780c40f150808110686a0006110080600da5a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 377244523 1250 377243273 377243297
    0x7081504060e0a0503030f0c190f03060b0408030703020c060a020a0b040f05060a0605010f0e0a06030b060702060d0204030b100f12050a0b16030b09090607050318060a0c0906020a0210 80
    0x705801c03107034103200d1080990340000c81c0d6142c1169282c0003925417032841d40c00400000d9241e103488094555004245407131601300c094042068810104a45a0504041d01e4030742c0410142061001403004000c21710003169101202e040080c03c0648000e00350340720700304c10003021707075519400514000c0f00307600000c3c00d12042d11145020881c0f01840e00000f0202e02a840030041640c3d00395009200b2941d084e201c140401032607100440700340c0841c10280364408034800044c05464801d50007074103031b0440542000d250080036000101c05030000c0d0701c10101e050b0002014410000005142c0360003042c41241c0d5010355041041c03c840040c02e50013090b4200e1031071804001801000c000b8445000c2e0802c0d5410f90604202240c0b100481c02004c261012a040c49404107403401d00703d540c28454410200948526198244d08030b58030350000c1c0a410790203058442d88c1c000ca0409001c0140120203100c00012411791452015018200d40d5001ca015034000010501c00b44e103404174201680001d42c0340c500da00d091 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 377245773 1250 377244523 377244533
    0x60c0209160207031b05010f0219080f040302060d0e01111c09031b060507021e030415020708030a0e0405061e040b0a0801090c080f0105060604060c050a0b040f0b0907081504 76
    0x69140d10152034040f0f8105d0308590300c5401104902130b901c0a036240080c0145c0320600340e903541c8404040000e61340c07010307039048040350b5548064200c0d0713602d44040d6460a81d5030f800086082e0020900544455a0f44441810201007440b981040024003013120f41014010b1302103c070780001c030072181620b8645441046040601c51103c01100c08964462000b452485062850040008a0f4010058441d482c0d00d0109201d05180606140c01804000c502d018100b2850200000043c0902004d40c0b00e4450046034101091000d07010a4070140d4440000d81c62000c10801511005440c0c3d0b03001d035490703649604803c042001444110181a01d003c82c40d500c02c1000325455001551144d0950352030f12402d170003086840310400045401d15011109901d03020600e070f900301e13a01034500940c4150308202c01c001180c003821444042034025015603982811580302c0f04120f400445040303808081d000c1020080008100c1c540382c00c042c0640c0100401800e20300c913142d03652481941440500c0c00308000600b004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 377247023 1250 377245773 377245783
    0x105030d0203161a012c1006031a09011d16080402040b010c020406080a170a09050118080d120e06010b0406110715030506090a0e03030601141207050405010207060c02091602 76
    0x1180a20401300640c2e540301d440e0015408031400e0242000c42d0100302e03850202082e0514080c006000e503c4501518154007034004000d4603401d4a03a2011220030b1000d250350341e0061500030104810304001c4424003c00300c0c0400140200380b840e0f800d0781592070a020030750129a0661056059a000901180c17480050300e080319076401c02940182801404038140c500070800d0f17001e182c40741000b8950111000c680c00c25601400d18003000281c42d40500f04410b6200f0000a48401c0c2620032215440792074034902414281d920309000302188000c400840c2030b83c50f03407042c60002d2441d0300c0644215410420240c10520561155008200c507004c0082e540c050140200300007040d42c0c0100340c285d41001d080280103081c0843c0c41c113100300d240c440024640d031068000d030080c20601101941c41c41d41c03480019200029440921005440148041802a445c003815503000304516201c243c0c6030b0380b8082c00245003040d160070410070420514107032001600e4000c10650061061600200d00f100f850004038684 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 377248273 1250 377247023 377247053
    0x3160507081b1e0f0d03090f0204110d05041110030504050c040f0e1006061403040503071205190e040509010216080d090c060507020406050901080d0c050c100909050105030d020316 79
    0x1c0c0d4400088080000300001d940303007a130803102080d81d2180d0350b1a0300640c112192140050714404495000200601d440d621000541d090a04928104610b03100400103c4400300d170100c48513103102102c07460510300800340b501000400c3c901400145000c1c1c0d6101d895050300e02c501405143c039a546064108460b400640f4210701c5401244e101181c3c800c040d0025040700c1c0718134004107000c003560b285c001d0050710480c0d114542140c001e510b031600303c0d6940d59072100358515030000c0010510088044007441100e00307041381c1444e0b44207182d4048400030070040303035806840813806a20401118001c400d0006080d0103880e00035030307080c1c2c4800354808840040c0c51540720050045251806c0841d401342c0100280103028020749007000745035240c038140020218280640541e030741c040030922035410f101d501d000f00014482c4059074000407a1401003202c200b01d0001c85008145990028804054244600c0340180170880013003c803600d0b8404007030b459100748075401c00008451803011041c45003d0201c0030701 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 377249523 1250 377248273 377248303
    0x1e0c040b0a031e09081912020703020a020306090d0c02060705010e010c0c05100506010503010302040209130f020d0e0c01050301030201120e120702010f030c081302041b0503160507081b 81
    0x6660240940240200030503400b42c04040036903c041007480e4198070407401030940c40544585041540c07030fa04801d40013491010010403030107002034180500310f400a001070b107101744c0003051030000d648100b500b80300c3c1c001e140c901d096111002010056a00060300030b04245c0517214543ea800c15810300030b014140885031010103600700508802c0859002001005540c050b80c15a0394040400e0111f100359070b0242c500328001130b81840140050700d070a070f0003840e0700318005101c441d20300b80c6030b01c4070025241020030582c0210b1340400c4100c1310707481d00d02442179501044c2000c0c2900489500c0003030020302060001a040105500c4058020300d00f035440f40465400c3c490440d005042e4072044140144c0c40320104a0005854030709801c9200e009004000c19000c0c281c4560300550f4840540130841e00c0011400d80e0f010b5140c0241c881c110000284000740c0c0211650780c50b550f840c0195012580c000710364a2401041410019200801e4003003040c1c40322030200c09540309000c0a87c403038061038070000c0c0b022240 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 377250773 1250 377249523 377249527
    0x181517040f03020f01020304050718090b010915050a0b0d020a1205040c150509010e270c0c07230436110121090203071d01050906091e0c040b 62
    0x414420403a58806101d407003a404c4a114000c0459181c3c00c1c0e0006542c01040c2d6408034900344204121040640889950b41d90300140c0c5107441c2d01c0b00c1905500a900101c02c296039100740c0c6251010181d00c02000d00010b40b4070013080c070320704240091a481140c1c060001a0b6001c211401da8611401c01007009418000080c001c0d4100b40c1080c0200f07400310f01c03d82903568401c854244e020b41c059010744a40140507154882000f507014140100120340d07001000c4400382c9184040c0c110144482583e002d14140c0c64529240d1034840b5400e4641000c1d9000034000c0b400001c51303c4004d100042400115600550300402d50b103a54021240410455010380c01640c1d202c000c6d00340149000caa400c00c4020300401021025400c5c1100561702e402c60101c00c0200004001162030760134240ea0408001d69101504990034159107404200040c1480828154050744560040080b07260a11410750020310032507504c006400c0110303218001d4903a5403d2418060840000110001303110029103000f400341403c0d40f9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 377252023 1250 377250773 377250781
    0x915030703020c010f1406090406150e0412050403020d150603020616020a0603051009150506040b040602011401050f10090b0d02090118151202070507060c06050601181517 75
    0x7402a4201d0310a000e050343c07800c240c41e4158200303070060081400303800c00050129200e000c10b21034031040041058030304c1c80c0c4a00741190340300081c442d09070080903001c8600d801810103203440c80b660040688904100801800240050f81d40c02d001d00010301d600c00d050108180041c20a203001c4c0c580e650001e035002c01c0100d105120750f90380c98140e503d114400c507040740c402d50300c0f4070f015801c644041d280d0b80d41c9406020000e01600348039501c03c160000149007074102142d44c40000074800d0740a604114a25100410208943c41d0240201c9210560746400016998103140102d400d1004045550b40302c1c140c6601d80740f40d87c5005400e0305001c1c00c00741c85455503440403c2d010b00007941c41030070441d00281c1c02c0499180c5019450700100c0580c2c1c140400300c108066505c000b200c3c1d44014074202a08207034200840302c0050401c2005500504880d01c409044810b90b0400b1412103000400b194103000c024900072440c0ca0020b1000e1013601d0301c21401004038038110170708644007046001089807140441040c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 377253273 1250 377252023 377252027
    0xf0c1205031806010b04051314100e070f020a03121e0b10030b03060403030209031603061e020a020d031e0f14090a0b010e070e041b090602030708090609150307 70
    0x11846403159071103007940c50700c0500036566143d200f4400c40c820711a00b4002070240e4074000b1080441c003049420301094150b1300000e110744003082543e1802c0d04000000c0704110304281c00c107505030301c01c11a080c4440d09209007080a5103c42c40b0340c2c001010000740c10351216200b400c2c0e50103d0b0048400200f081001922140c4d00b0005001c6819124400da0401030f0030501e85220703000301000c0c00005030207402c040d2a140d8040d8069001040380c3c41e1706024804210801c804c10100320740085008403008100400200d41105411004141c0305034990b0040041a0546400144d45e405e0f00d8400d00d00040c251241e82960105442e45190a40c22325003054a0010b440b0342981040302a201641c20400142c0c841000595550709032080061014a48030b00400c07800c2e4220a1503680b101d8181014a4986030310000141141c8000e0a4549040040f4603c20003036a0701904280c0600348034001189081d01c0c0da01e07924003034002c01e610305104540c001101001a100e6203504491100d004004039101e003422100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 377254523 1250 377253273 377253277
    0x1902011d0c011b080c1c1e0e13180609020907030c0c0b0613140f161709010f1103091207020a030204181e0c0b03090601060f0c1205 58
    0x3419510105054962401000101d664802038034161500810343c03041511a540303e40d40440251402c40c02448003404400c41031122100712440802c02c41001944200301030b01a40c000f49442c2001a0724214042c03000c0d400a075a180d6960307080b40d105100c00c20401c818000780c0220740c0701c0f4140e600714070f06d81c0c0200061078200740ca01c2c602c210340b80b80b201c1d03442ca50100c00b21803052061000086c81c0081000c0400c030001c3c07541d6001031002d03150310482c0040511100a0b10413000308500d03901100f074200544440944c80f00c03078001c0c90fa1100310050040c108001410300301c070140b20200160303070b881c0070500001003540003002003200c0220a0040300c0b041010305410790012512950306008048200c5000900c21301183c5055a00030b004444407810754080c04000c0583c09988031440c4080d01c4280045841c481c07007845032005010b03100f01c0d511042e2905915130303c0325034030412003000140103210021502003182815034015107000340c00120343e20000c40c4e0040c4802c0b00905490011210b41e620180d0082c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 377255773 1250 377254523 377254541
    0xc0509010908010c021c09080601172a0415030203060c211909020301140f061003020304050309010c02130f050a0612031d06070209090604050f030414010c030302190201 74
    0x310504900d0b0346410541c240d50466100074016000160180b00180c201c20203114001c01510b0700c0000c00d40c0b10b8400c14035011003a004100c0c1c00ba440c100c040d5100c442041800b0003000412640c28071888501c940c507000e81a8407101030300c034a81341c0b10a10b0640741c41c07922410056130010111503103410314100f03000056001e181a92400c9002d0109102c0c00c800d00c1282900440e50810300792000400b00104030010604101c040382d055403140300d82d80f043c1070240301143c054510b08140526074186071082140d81000d4207600c030140b60041c41000081000030081d202c0f40c50084c281081042003900c0000c01c51218203400c80060ba14141d10720b0810103580d4040c1e071183c00d0280c000c00500d521150040f101d42200140200001d54450303034055640100450120a02ca01a003800d0505c2020790014400c00c0302112040d22a9010720100410310100300010448040c1ca04055440d140c20080001e0381001c28004c124140903142d10000c1c00c2600c20f0381292069034248603a04919611000000c0c064a4040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 377257023 1250 377255773 377255777
    0x9130f05040c080d020d051b0d030e100b010c08031003080708030601090f05060315060c01063f0305030c0d02030103050f10111803070302150a12060501050301180f0c050901 76
    0x102c040b81c05240010b15000c0311100d0380040064000118048030b940e44000f01c08814013680c88a901c80130007040141160711480341d100402c21b00f40266482d441c0603507481c01c003041303282008403010850760404c001c00200d5070080d10309540c0303503100f00b45021800e819600040ca20030340046d8101c1440003510155015034000d9035003102c00c80d0786440015500e415809460340c00758080011910007800345403000180c10000e00168241019001c079203007144c03a00d030310001711100c2c915811b807400d502c2c0803400d9110320f281002c0201c2e1400500d00c1454050a5040c00030b0521200002291072a00c582082d0382c0b0000810005540d00e41e1640303446901d034071030103540d00003500c00e4a0303000040c254980100348101003084070243c03d010300d44c110030b0520540c14200d00e0b0180a5528003001503218002e2440701004100440c2d0703503510401d079004011010001640d00031a2921800340116a841021030f03044560510315070095260103200e010042c04050446100c45241050000c00b441d0000003500468000b6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 377258273 1250 377257023 377257043
    0x612011403031804090f08030901021305040c0207120c0e040c080c0103050f061e0a0303171807150e041d010c0206270a061404060e030a080c09130f0504 67
    0x11424160790340522110f450600c0d82c803841a0055041540c81411203d000d40030b44da500c030501380c9a052059100b0f41d0902c4059400107160320010384e0540c610700040030207617001c00140c081024025100c1c15640a22220407500d0380346d0105014600302c10f136000c3c3c100000d104c5194180341c83e000401c80100d118a1906002e150141150741d070003442441d1250910212210a82e80c5800412444403800c041c018620580e250106809032900311811000d580f10341c441c03920600e1003d40480e03003100000e1900514040c1000c60f00151352010070b02c0b40803182c40307d1010861011003441924840252116030790030515140e000d506c1505110a01b043c140003010003007204601c40c00342241c1340c020480e40c1180911480002041c0b9180c01031140325408051003e940f080401690341c28282c500c41300082895030040020b03c0700303100d0346101d0040040e0341d100017146442402c0d80050001c12008160014100c0007242d403500f00e44558514103204000c08a00304a12070545d4510300080c4401c0d00e00b0b407040745030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 377259523 1250 377258273 377258309
    0x303091c05090d150e0f0f06010e01030f0b07050913050103060c180b0c01020c0706091d090c2809061e03020108010b070204320c030112061802061201 66
    0x684100c4040d014060300181007411a41ca8140c502d04807a14140c44959175680c00a0501c1814400441445818801b1703105109605125914048041c0c1010b445034880c034004100189504010405082d400019000180c0d1141c1056402c0d01541c10901d0300001c40c2e040c07039100c01a60307501c8181a00d115650411034044461001c80d00d4840d060911498200784038014414100722a0190000c41d500400141c60400488012403c166403a400702c40496021242031202181c1001c020030380110804508460b0301c3c1c0350681c0e598645001c1031450140c4043c240d010406d990406003074580380d900d2030315410f100b5690000c0000178603862168603042410304403d61890103104251004894059603038007250703420511f81b00710950010303404990155440302d808a0032035071507075010a000c0b014260006030901d00156001c0501c402800907405142c20401403040d001100303030b180600d6410400c00180040d542500c01040440c40501a51100000c00d0ba00070b490300c5030040c11b042c0c0d126400031031000c00c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 377260773 1250 377259523 377259527
    0xf060b0a1704050703080714010606031103010905060d020306280614190302041b08070306080714130e010e0712030f0e0d020d030203220503060609180303091c 70
    0x40206250015800c007103800c034045507a6858907003140c01803065030342007a603075a074620f03160707111343d600319500c1c0c02c0342c10500a40c64003841888001c200c0c504041c4041030240040802e82d10050064240b85c56030744022901c8d58440c500c00c0034405a01500b2207006040c0030050300310760049110040301110800d200807800300028011042200e030300010301c12084442c40c04200882c00c1040c80210491100040000540c0e00d6000c1c2c09401c412640c8503c0c890a107506000b4981c60b0014035000515082c1a800c0000000001e030f0001254006001d100f4550185000604643e9a684031030b843c0d1820021103103400501940241960101d1500305c901d030a55070ba840c0541e442c1600e80c0500070640d000490a19103001d41440701e80401c0c014130008551070b40e03070300180c00072080b07840235001a03201003801d80160300301d03148807401e41900c1084903481d1850300e00000c0c0d40c8d00004101c00d00070074084011444201c450840c4c1010300c1c5d00c07042560b8403807822603802c0707503600303d04d000b200000e010f0400d006010038 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 377262023 1250 377260773 377260777
    0x31801110a030e0d06110a030b0603040507090506040e0a301209060603050a0f02091e010308090d1e02190506180f0307030606080615091504090c090f060b 68
    0x4061030016007006501d94505803110725101c03241c41d8101c4441916400051054451000c4440b910245140c845a24500040403246c40340c80e0540124400c00c00e210214400068800071a070010300045040e03030329030340420007403c1d420105081d00d10446a846040100010402d8130b1222080d0741500c04442c01e541031480340703081e85076031004244582d00340c000b6280ca5801c8a030700140101000b048480c1d80380c0d00c10703140007003043d800d07540340440c1c2d4104411031401070801e5402c002039042c500285a020358420141581c107101c024100d0b00d0001c0c09444a48400c0070003800e4542007c54091004440048800e07a10360004040340305a20301e6841420170800015210182d40f0060911802c081c00c0459060307191001031000c03940b005001c0306604841c1c0d8100100400341d4807400c004038116150080aa1030108050900750190305003600c00101c584801154552120341050b0207203104100c031010800902c40c00c0005840c840c565500401e19074410f0f04402d900e0450a0000c200441e600d0740d40d011b40e4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 377263273 1250 377262023 377262047
    0xf0c060604090308160504030206030405010f05010821031b0412050f071d070c080309070513020307210605030106060c03021b010233010807030c08010b090402060705010e0f031801 79
    0xc100258040389514408a40120040340c0c5402d00780d150682340e80016409410440d41100c83c3e17074443e07504610030381079406481d0052602c0d1005000024240900c2200d5100c4501c2e00000b4500200002d04090340c044902d4100740c0000d00e07805c0e682d9407203d20f4483c0c0412a01e80a98003031054803e0442c10410000b1240221400d907600050201d40c42e01d584404594040d26200c104038400342d6200104d80482c00460207042e8040c005d0a06501d00001d022205e01d0750034034100c0b2503205200b00550150040d27441d01000750410314410070a00704201d0034006001c3d60700101e403d0340c41c00b1000300310683c00c204841c1c0d000e4005d0b0221415030300071190141e41748800100d0140160050480703400101c0c1c0d11b01003c0c030320703100443c4440c1600c010b004125428074026402481c1c030380c0c00b618042080c0201c60050a000d410150000e01000e0b22150205900d18400b40000b03000e45070004000081c4442940405c50007039180082e101550700d400405a5650000042e0354146010b01440b61603030740c01341240c0145 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 377264523 1250 377263273 377263277
    0x80c0909010603020304050a020901060815041103010605030c0c030a08180d0c0308060307050418060c110a113706020f0606060a0207180507020d030905150604020f0f0c0606040903 79
    0x80c0d03820030308214042e400c068402c03600ca100720164100140e40c0e00ca0194042c0c00c969441c040c15281080902c1840c40c0558800f0740214a04243c01c04006542021030f0305451007400c4c440c0d41c0e52100410f00509102f094001c0b2040d01011030040041d50b80200081d00a10200440e5a500d1100c85002910b5200318961500890741d02d03081c00c17002a000c0c0504580c011001410f41d08201d42d40d1011806442100c42140000210302c254501040703501d20408059514514020310210f000c0c0e901180d0b54140511301401d0ba500d403901a4100e580c0780e51554441c940007070420784005046070fa640c5800307842c0848141e141d51f5516404200a407000031804071480141009140c50740f04c0a060000d1039101e0400c04046000d00b070f1000c10011461101c0030354800382000b0004482c44d020700000e00341032010301038204042c00d01220300040780001441d0780404c42e01e44003104540d00e40c900010000e204214000803001404221030480e8400003001c1c0c514095003800359001ca80d18441004110355450f040100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 377265773 1250 377264523 377264539
    0x15030402040b0a1d01080f0c010f120204031a18060c0f071703090d02011506050307052b0c031a1f0504051507062a05090a09020706060303080c09 64
    0x400351400b5002001008400352400b001280c54691107080d58511404040c1e402c440000108191481004100d02c0f80745448088c05e040004180000c0c400f40a0b04001303001c210b003041c00740c5c5d003210103507044400542d440070099051002c00c0c00b02081802080b03515080b1034003446058050640f002c6050f0784240d503a00340a07031520f140e441040700c0701e42080500391100302942c1c1d5540700c01c4030700b04000c5014104180082c8504d2a011b40d000303003552482a01003038800b099141c00c00c00e181c1c01800341c07034116205040c6907881c2d0108000c0045505101105500c078610010290449242260b02c02d19822002d90341c04e00480440c0000d07800c2c2c0c819000505c42e0422100303003040c3c04203a40c82c41c0c1a030460b00350745805440d16540740d000995a0240b2045640032803400105601000058803429032801854410300e0100b80058840d01c0c2d14107860180c0c20180503001a0304247d41c1e44140c0c000300070384007107c0d0441d110003040c1003090041c0314a00045000c6a042004a251035801c00c0944540c1d0b44000c200c01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 377267023 1250 377265773 377265781
    0x30305010e091c14071703010515041d090102090a06110f061005010c020114041d06030c1509010e0310150e10050d030905040905060604063507080a0c0e061503 70
    0x89541c030313210134000c41c0c030384050080b0000622140044000c400500d550075440c0d50508080140b00034441201d0107940d00c00304810170400c0c00941441c0014002c190411490382c0d43c00c2031490291150103102d41e4440c03130000340420700070b8015441e841c00d5402d82d0708407100950100691980c03120b00703a80c182001d0441d03000422842d07110b03003401d016040c8103240400a140845c10071044c250490f8100752074080d031510000050032141d492039580200100c0c0103149070200030010403095600540f680300c0600c0d00060006441e4081d65482c0c03c1d500005d03003210081503403075802c0e00040103031070030052000700d0007a4002810012115150b020b000c80079804030840349094108a82c4203484003049003071003181e45d0009400d54a500c99078040038050340280c90180390080401c01240c1464006001c60f086483c104407041d100c02034251030f07461421140040340358030041c0b42850010141c2c0248090303c074105510781008007141c0b0003402c5500c03a03540060300362545000c104003d03240c0d072041c4241520520000d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 377268273 1250 377267023 377267027
    0xc0219020f1203280e090127152c0402060301150327020103060504150b071110230306090703180c06020307051902030a08030a0f050103030305010e091c 67
    0x44500b0012040c222490501d1850004405a050200c2c8181d81c012101c3c0101130282c0000148000320003c840840d86981000c400746c074031030004011003d001c4642003001100f10f00f01d42c8801001c1c6035100803888141e03580c1c4c07903180f1501c0138403041004068400701f0100ca5285100308060041d0741c01480b4a007580e00f402d198010b0482030b1000403082688a0202c0d442d101001000206c0c118084132440b10841c10038000901610440c0c1e2001c2c1c09075203443c4042109204d18600c95094560b002c5007036649402905100505080307201059601511280e4503500558002c00d001d4052071035184c1806224100402c8005140001c40e00300b500030380c154001802003031096100501ca030404488115184c04940c5503810110001d0b0071a0001d41e000007015001e0100c2006040c40c1c8000f042e0031181d40b05001c0e80031070345a12400c40000c190310070110100e074081d0703603903002032030846a103610400882da581d0074001c02504082c801c00301030700c0002d40070a580260104600c0300b40d0603c1f100014002d520500c00b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 377269523 1250 377268273 377268289
    0x1902010c0606030c121b05060313030203041503091b05030307020f0111060f0106031128050403080c071d1014010905030304030b07020606010f0f12090b0403030c0219020f 75
    0x10407103080380d0325070b4048000b0720f10a202002505500002500c500124945802a49081d0061b01e18540000314100295640ca034126688800103a2140e60b64600d82c0c901a407840c01590409003400f48018483c076030095140d8050722045001c0e840310f40c3d266004003030203c1c40c00494059150150010845000541407070184040740c030b0410314048400494001e000c5040c800180e41d0f010f180ca001b00010080c1c150715015000b00c0b550340740092460b01d035481c00c0c9041e1400359030042d042410b0400340703084c201c1c0f40a24280c0c2c3c0259041910130b66540014691710340c8a0440e07016201c030b4483c14050b910554950b10360118418000102622112400c00040c49144040784442034100002e064010803203403418005031004610440c001640c0703040c80c400c00390070032000401580c104400d814001d240c0700e601200e409641c50311030134003844440c002d070070035005080c5203c40640400300c40800c1c0001c2542c142d12424084285501b5541c9880c00000180c1d1a41101d032000b9502158003030104115140c0a00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 377270773 1250 377269523 377269547
    0x150f120206280305060306100501120c1704030210050f06061b07080a03020609120a0518010207090e060a05010f080a1106130609030c0b031b0a120e031308190201 71
    0x4400c0c6902e8190b07400000c0b03442010709a80080d0300c0d034081c0000350a003001001e400074117201025a00c2400c0900081542000039450091a9100c0e0303440e00006020301a03c1d01c1c0c410b1910700c1ca46032032070603080203996061302c5115080c110f8a4039000070a581c8a550200b400350000808003482c04201c190310060300d810306840342c1081d01410300005400390b410040030610314800c0c0c002e041680785c5125914100101c0c102182c4410204001c8000c2ea26841022280f6031b04403610006808511400101e02d41b50050b00409001c0c1d20b0400076075110b0314002183d038441c000701841400143c1c0c8801c1c9140840c682407140c02032950044408d8400a40800301c004180c0401800003400d01000e03211040050b0740c3d43d40183c000c5a40c181e070074410b00c94105006006002d14a40441c42d40c05d00819031800c01c10006a070000005010880f880300c80d101d2031405110500c00403050042c101c000c0e507503607100d43c8060307800b01480111200000b13412101040030040700c072590075658410000c5070019a0310443d002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 377272023 1250 377270773 377270797
    0x1020f031317040f0e01080102040303050702100201110f03010918230309061204021c0b010924060201020c0c03070305060411010507150f051807050111070306050901150f120206 78
    0x2082d00302540d4240a400201020540784501341d180c00e822402c18101a081448541d00420061003c00d400c0780488130b40560548009141402001007240140300550111080303e4000907406c007a101940301843c1a900411410003440c041d9031050790305951040d4006100d0341d50701601141d2020000e50201c02103040101b500c2c585144880010185d900610a1442811500742444103505206980b050b145881003c0a44610259217500d0400c060500c29107202d142c032140d4103460001600c00881c00204815003040c499522504081e010750820b03450701c0e605200d10707000c186062400056400803030341c0040c0540200e481d01c1c0ca403c000d140a4030f00f014184001008240c0c0055119106d002c0ea0f0101c203900003070451a0540360509440c0040c0c00d640d01588808410600c5e48000308443d41260404d0a0601d10711042080940c101895540050441850641007148503241034100040c440c40c0c400401c0c08050300c904039070300c0d4500c071b50140506003007a0080d6400141402001032402017104d03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 377273273 1250 377272023 377272043
    0x1031b0f050f0c15010f0303052b090507030b070507031d0a080f010c0212210703180b0115051312020a12150501081c0810050a0608160201020f0313 65
    0xc0303600080e036400b652405076142d1204c8100348800041418040c00b410701940048002440d684000b1300501a0007490000d9000c0441400c003245006144644403c440400500200c13120b420a03e85a4205100c00d5a039010b0020000c4e200ca071240b011503121507810f45820060440f121000c00d10f4502c00c0600d9500110103410208146904014101030001031500224050a00b01c10003414410b0051700d84449030818043c58003440d600d800382d4080307118403030083e88a507a224a0110040c00006c020441e51840122040c414032401ca86c506043e107400342da2441408025100031507003403068800d000c100b0403850a00340550005400d02c4480103000809070059651502c02e0781a011407203c0044174a10201c01d80f000303401c4021300800c3d006211800c060150745540c00c07440450a0020b089081c10002c25100003201a0b58074604040030b004080c10981ca01a100c02c8051700000c001d031402400840c1822060002600c14003c035403000c1103080c01141151680c4500700031459898030216560412 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 377274523 1250 377273273 377273287
    0xf01022703011508030703032a12060308192312090f01050a0218010f050a0c0204020403050303010b0912010203060d022e120b04020403020a0e10030f15060501031b0f05 74
    0x89503e0300050140780001c0d40d40c0715464500501242c02c90010801c000c83e007002180780000405030b106461814908010500102c6501900c00070070507900010f1482c00007213601c00b0b00401c025100c8030380d802c0301d4032001060203088400000200c2c0035581c1040444041081400301d01c01406821703041002130040320009008010200d0075244100c80c024a0183e02042c000015840c440750428513200c00e080c01c00c070000d00e00c103008026114151a2809000c0203803900b50854583d54100c0c0c2c02150000c0070341e512940c540c40c07220980d60007458140d100d144099100c0386c011f041842224020003005242c62600c840c95800d009000084111001040c240b18981300568501003403210007440050351001c0c40d1202400002c0100c81e06000c1e41405984140814001a118241c4407010741d06070030303804206503940091600075075074542c000a000714040c03203521041098241ca5400c1031209424140071254a410044040f5181d02003000144135050400e170343d2050103082000f103459407d1804900e40b0b00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 377275773 1250 377274523 377274551
    0x7080d02193c020a1d2710020904110c0307030f0e060307020a02211504021f08040204060515070212010219020f060906010b0409020903070509010303110f0102270301 73
    0x31280b42206529003406452011840c040e400c0c000500051405500043c1041e00d6010150900070700c6010004854549060746199005491003c031030003604499880c038202074118040d4214283c03180c021400c0c02e01d4114580400ea0580c0c0e400300040b80254105807050b10115401200ca01095040c040041000682c50300c0303c400941c461902d1b1740003480c2400c1070b80306101c801c021604d03283c3c10310301c0e48000c040b19440f008943d00c0c1e0b004500026901c0c0301d0326140001000d0f2034100994015080000c0a65100c040c1c224100a2181c0d000f02c8042200030350f80c0e4140001c0ca00c0184076600b490104000318801850300540d000c1680c04030f58001820001c84090300000b071710300c0010040c056402082d101001100410820340d0050b0400f010b003c1a516180c51100c880c01140105102c6980206905107a914108001402850000c0c801402541d49081c080c2014030100f00860306801211408c200400c414022038416051940882540d440e80e444160102d1056081d040da055498010201d8000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 377277023 1250 377275773 377275853
    0xa0f02011209080315030c060a03091406011502070f030b040807030c080301090617030403030906050a020307060c080403020d0206040206090409080f07060c0810030c060819050907080d0219 83
    0x42c4200f070095540d00f00311184020754109198401c0c170983c05190500e84945464041d10400103441c103012814882070302c4c083c0d21891000c010031185105820000800302040c0d00e0080d0701c9422038007510140c0392200b20205070748040f400054140380342c0d0710124000074030701001090014081d1034140d82c29810359a076400d05074002c0c0c0c00440d000d80c4402051290a81c005c024001e010204001146068a960303005001c001c1103100e14014028089420306055000303004445060b42c0c80f0404100142a0340d1000e0140402580c05078014807802202ca5565400058071a010301e800510003804c0c1610382c020840030b041440030840d41400148590310300d28240c6406003c0c0d0a00c02c04010901a08503907000f444088010a03500040c003400e4410070100300c8030b03400c0406955079440c1c9520113a44021300701509070030300c030101c0f00c441c0d20382410803e03259004607000f0260380702d000c1510051500104100e80d02d000281414000018081c0040c000404506408141098030034100012203203519114101d1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 377278273 1250 377277023 377277041
    0xa2301090803060f0603010f0902091c05060f0c18120a0c1d09070f0506090109080a05061915050616170c060109090f0b060f0a1d06030606030a0f020112 67
    0x40c401c0032060048070324202c0102c554215080d2034180c119858940324000d0440144501146c8a40c0010000c4082e1036880a01e003000200c44071000e614129803070b000b03984600032590b01400c04110004990f6210400c0c00b00c03500040020003600c1c400401d10100000c0c0c1d000610300382c00c6445040c9400000914030601d03803000300505c0340c2d0104a8082e0044a0003040e4000b4141d203059008400240000c0c500c8684600a486054403800c0d1940040001070307030390a00c1e03034000c15035511a05003110100000000c0492140143d201c4504580680c004550240c0781415801000104048014030a0b42001c501406260a966241443e02003d40c1c503448101c10f24100705c8000b00d50001940c2d450507108106890042007120000c02128a5a84a2000c034100320800240b0503c403200c00300e8076076680c00402c0000c2c240d0045c0041201503584800c0d404440c14440811412801c0800141075480d000c200c251103010050050a1350200d80e0b941c1800c1c80d00a0041241030000700203c1442a802c0b920600d041 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 377279523 1250 377278273 377278283
    0x1c020f0a08040503010f020c030f03100b0c1c1b08030606070b0f041b0b181201021c06050a060f08180109140606040504020109090914030f0a0f050703020a230109 71
    0x284900f00303001e050948220542000465004200301003580d280001125110f0200d007820329125201e40390f0780c5400403c5640110010b280c0840d80e40030040001c03a61040d180c0d00d201c0601e41c41c104910050352100760700c0229203840c1d134515a600d4041141d2400131580f140c0014015440c2c0f10b46a640c15190352426148a107802c902141000104031482c0b160104201c46001c9001c41c0c10f00c0c0081c151454480c1146841d08046000d507851140d8503843c00c0024500000ca00a640380c82141130300c5d2655440c0d481c036585810f42842c40024036410410000c400f03a99107030b82c9560700e4402d508816520850040c0bc460002d5080c40712a0000385000e2150030202c901c142180402c51503408403040c6084000f91103140301d64508000c3c0700c0182c1e084414001102c0c10410f000c22552114180340507502030020000420340400281681c3c44941b21005102c3c100c0940c51342262007040882c229514040e156004015038402000311010910700b0035a0800b01c01c0d841c0485480c400704240081c01c0d108018021a4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 377280773 1250 377279523 377279527
    0xa0c0804150210020304111e31090503030601050a17070c0b01080d0807030b030307060204120b010602060f06040f060803130311010f0210090203150f040b0f06031c020f0a08 76
    0x50041e41c140840100c0d000b000b1001c4d419030410340c49500c410142804098450854654403403050408009252089480100600110300080c401d9030800180600d100c100f0151340700c0c2200d45034030503110307443d16a41c001005509541e143c2005403407541c846503546d818030a46440d41c0a02c1c03414440c0c3c0510a024507070302c1d0f0078032017041c1c50302105102040c0c012401680081710006800343d4002d0740c80741d0000b034a06d03000c21100544800310b0b003503100d5202d0143c1a41e00010300402d0007100c541d89044818800d010f040030030b0ba42c4e894105e03220f680a82d407a4465400600c003068491a01d900325851403404542e001900a070703240302c12841c50344901e0b9071403100304104030200103000c00b03030340b0b20b00100c00c080c03c02c0c1a800ea545d00b0020344500c5040c5070001f07080d039911800b2082d0340741000752145003405050010503c0c200400c00420700d200c1164222100100480001d000300701030b88200e4081da2028000f490140310b0381c08000781d00540f01d10108210f1140400c0a6011101000810703070b014041c4042c2a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 377282023 1250 377280773 377280809
    0x30e032b0b0d1104150305060f2502030414010e0627060c0c0102010f0c0f11030d1118010e090126030d020414060304080304140f010603060506031b0907050a0c0804 72
    0x84c2d03128170010515403030011404001040d008521603078000040d110301221075950040803802000060304494600d209001d0741c603040340d00000204180d0b00000700007002003a20100449034040324440850b0414020b002200585401d203038044d070448410701418049010a0011400f00e4100350320190840c0c2c8000e0201d4030f03958080c0f1608a10340104107040c880f1454044024100109403140d00041100c5000c04c0031b0480014402d58440711491003090005101103141d40f11540c01a8000c0c5410007404280c2107403560003401682200c010261400039103032301c0e10a4004c00d101c1950381100c0c02055103081c2005280040c4001c103038001804000603221428650300c034040603c90481c15000380b50070402e0002080c005d5080c0d130381c0550700a80810001000c1c911490030144641c2088040e503080c105c01000700b143c943c0107984140001c1c0d044544007140390080350700d1101518485a000064103002c5150207100b000100360890f964184084140050390381c40c841a8065409220100090040d10b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 377283273 1250 377282023 377282029
    0x30901110c06160213090b0c07030c021c0209070305100b0d0b091008100b0622030506010f06030506030a0c0312051606020a02010b090f0a05280507030e032b0b0d11 72
    0x1785d564000070a030b080086120658508104038000760242950702000b183c04001c140c0b241801c01c5c082c5034080c00d5024000104040700d050070594440487c4240000130008801500c07a101d03152003140c031040e00000321072500c00300b1102684011520141d440c0c4030782030b03098580c441e00e05040c0540c990303501032481e5178985400e40703050042c1c0b1541e1415850500c04040780c3c2c0c0e075901040d00d03419100881242d0704081001c5400c4c5588025500061060040308000148004101159021640142c80c00d003c607650341801c140e143e14030400024103c00c0d1a40092000c070360300041800400502c1e043c428500701030541c230710104a005507400ca4000c2d40009488030000c0d828021400d8160090310014218144009000750b07002004122122403656100000c124403803051104200c1c0f43c00721203840c500b81c1011010800f501c0101c0340304001c03d00308008410a00c5000080780c42c09004000d070f040c400300c1501b5211106807100504420040e84504124040396a982e8520458620032889240035064240038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 377284523 1250 377283273 377283289
    0xd051501050406090e060c09040b031e0105101d0403030605060d0207020f09040206040b160209130302011104050d0312020927010b030f0c07210f020609030705030901110c061602 78
    0x2094a119061002c40301006400261454003c0d420800d0103407101e208d0f0340810010718150907000d50512840c1040d0543d01c1d404810180683d04040090140f036882d0310f03c041c8040000d21031164501c1c03040700d640502c2d40035600e41c213400c01e2003883e01048007545c6200150380c50300716801c4d41d844103500251040441c5040a0380c0c1c41c00007810381c0e00c100c5524281d0006034941c0110700c241031041400185030500800c022101c0c03184660b00600204150406110740c8228120400d000c50142d8644428011610450300035a400c450f00106410904042a0340455034480382465496001ba028024000607a8401014006150803808103074902d040c0400c04802921041e48800703440c1e8010070901c5558000410180d0340002080c8060f680c0d02d0543c504410001070180c403608400041003016902e840d0303c214005441031069003207940380d86603c20340944034464044001d003a540204005170b420b500594142c80051200302c142c1d25080b40c504082101075000c0b141c1100d00c02481d8004200310324003011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 377285773 1250 377284523 377284529
    0x3030c181d0a06050a1707030219210b180a050a14100207030c062415020c1804061e060608010521101d0102040e0108060718140d051501050406 63
    0x1c2c081c051540780c0b41c040b4500001c20b00861011501c51080a0401d44081141000860b406807030814900c0d2174146448500000e40241082e5800b600c00c40d4001d40700201e600c405564000e8040b40403901c03080030341c4146019008844465009101c040d0011501c00d10422003a2802030f0b41c40d40381c2104600b2450f04202419070074000f4207105200160200303502034a060030003a400b40c40010302140b02540c0d03204444003000d074184040d441d9000411004111403074018514910740844240711030000c10003000586000ca4030358407a0441d8001800707d103042d00560701848207441800d002d016a0600f80003a160b03160062030102d25094010029070a200c034928000b5403052040c61019103007401079940310041c220071581c000d0344a0544504910034216090060350090008642e2076680382d2045482490900c1696594000c40d8001407210f8002c82450f9020852a40c0d00c030441820800c1c05008100c041d00f040e9009001c6901e0100014010080c9107883c0100c00405001989403500f04025280190 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 377287023 1250 377285773 377285791
    0xf0e011407050301060f030b040e070e2805071b030306230603041b0518040b0708060901210f1b06030c0207061d030a120e0d0b0403030c181d 62
    0x4000c011140b5801020b480c19030354549488200b000c0144e10481c00b4001c4005102c1d0300c24a00740d02040d01c000006080f6048502560000302ea503500e041011240c0200c81d540318004014854008040f440c0660059600c00c60a0174030b1900c0c521030007014064124921012030120b03586031020b00006629058000d48a07a56451003a071403e42c0c1404580302d4040500020607415071f0002da40380000d0000b0000024281c09000782d03404440703002211100300b0f01900e00341d40030300e142000301d00940d03c90b400c490b1003440040e20300e003866440c5c40030162003010b085130904026400300001c40c000a901c040d510700c00300c4c044d0006064036000d140721103100c2c011590003907003814a000083d8281c0380c2c0104e2003008894803410013103405180b00e00544d00c0300003110103c503031501541600c0e5003004582410011081c40703d41d501080d15642205000400080300f0000d401130a40704002000240f1070f400c028180340031071601d110030b22005112090040f8082e0001c01c48a05c101e1b03120302c3c0450300ca507281c561107000d030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 377288273 1250 377287023 377287061
    0xb0c090d020d020411030901140903030108072c04060b040b09090714130603030201051b040b040909061b02071a310e0c0a202503060f0e01 61
    0x29200186824400420003030140a14907658020341da036660220240d88100241282d43c0e1070802c41c110700900b01074001e440341c680e4031004211110303000000d0740d06a03a6828020704210f814141c00c40f440c41401070460707041003254180035009980c1000018001ca100b103001080c800001360400046c3c0d6040070882c1d010301507590810040b801e0005600046071201c60010383d02d028090f01241130380c036100400a00c0b03182400300020405a0541c050fa01c250f07104400308034800c07203030710000100788904d2050200c069800e000503c01200d1541c44284854492a0000384403030b41d11804840002c040c090860242c0c03c500c0301045601c41c44010340c201c420b51a50740b0f40c604005200280da42c1020801d1401f0151500a00ca924204298030748601034884240038000a142035061881a40e0203070244c0000903614406c50109600300380281c8011541d14805070524406000424446180d109420182001e0080300000880c0007072141202e007a40700400880c250310410712041c02e40f400156200901444 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 377289523 1250 377288273 377288287
    0x1080906040c15030e0111040501020705030703030c03030216050a030f090f0308042606010806420609040603050304050a0b1201090b03031e03190605030706030b0a120b040b0c 77
    0x2020320000e080d10307180e00e80900043c2900c00304030000c0584160303a5000398030302a00b100340c0158a101410031540241d00300c0e030f44079488609054031403c46100040200c0c40840022000070300a801420015074020400307000100c2503100e2602c0c2c031500a00503004101001c11070702c0c02c290b01a0366100170b0700746103c07200c001d01d240d40d803402014869846410458040038040b000351258500c9100032031f844007403c0302c03001d5071030b00d1625440f0201a185141e0401102d007080400c00b40303500e040c013990b40c020402107035400402c503031001d04007000310f00082d03005004204054241d581ca105030000b0798062002941c40700d050009000841d40103070010030300c01c40d00b405020501c42d103d0308050306542c44a0004034141200101081c80c601403043c0030450015444680101d1016507405944245070011080500105c01d004c2042140c442c0d0040300e8140d000000c05208290007900002d0103a10701515462400784d450b138080d900d0b0713100460100c95a99a800503c805e0142000000d500700710b14011341840c6c089 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 377290773 1250 377289523 377289533
    0x1104030201110a0c1d0912040e0622020408071703031902091e040b01094211120c0703020904081603051b19020909071a04050108090604 60
    0x46200003810090075049030111410184080369020b40d1080704103010a441d1111901d000a20040c4007400381c1c410800201105030000b000000d002d44078901c1450300b0306015100214410040c0150f80210010a0209a69000b514118442d401d041c03801612142050501c909020f0198031101c190241b4003d00350444401000722908005800c12210f18521042c070240040e008440600f50b0000d5154070075001052141c0391119240e40c2101c0400c0650f074000015101c80c1c07024003c1060b00300680620420383c5000061880d180c8200e012640616642966440c40a0150050200015611070303005004440d040000030803642d603001480303003054412080f60741c0d200624030000c0d115140c81d0011800b4811020202c03912a0a00584d59a10800c0c605006d04940e100021000c80103050420303507904414007003004030011400710440305100c1d507950200300d6107690141c12021030740150b507c000341d29504e841c40ca05820003901030160701ca901d404000340428800508018281c0c201c0b20030040000c2d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 377292023 1250 377290773 377290777
    0x120503040603150819110105030f06040b0d0609052d2d0d0f08060301020c03040b0d02121005030d0807050910031104031103061e040308041e080315010311 68
    0x50503034030300083c5504030f403818044814081c2c3d002c00620b009000e200000f60049007041e4000c1d42c09140541c0c51084540c1c01124070b8481101c181c034501c200c803004552245010b40001640203c01000b500800c4110344401003116070400c42200e4507400b240340c00820550203c0020a101041c030024070000501c00341054450311010000031140b8044a0076001c00e21170b50200d02d41c00807400c800c65484040c5a01c01400d28603034036100d4000704400600103074452805008881748220b07040d02079810540361000d0045240c01044840e0035058007444000800c204020301588168500313104540c2c0c10345002d0500d410400140003000404c070a41d0100001c49802508440742c0603411f84001048008110045000308403014501e0950080010b0000501c02c1044a18842503030403429200b041d19040c060050400409000d680410b490701d0015010030b02411034240e0090103400306c1500c00b190b0009410401d0705000c0100e80182c00841400000103816025021482c0c0c00e080030400c40f640750b007620800d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 377293273 1250 377292023 377292029
    0x3020304120c0902032a09010e0609060d0e100b09250309060c0504050a0e04050d080414061303080601110303280c1709070608010902091c05070f12050304 68
    0x1107056a201808002006400c00c0040a020038215124140050064140c0340c441681200006c0f9011094003451210004c840c28041e0503116084a030712031000b80a0190400181168440b40500c40980c01102a010346466860040003600c046a4060054400c41c0c401450050127400d0705810000520000b50a0180d000c00030400c4810742c04080a045019080d04400205000d040c03045403005e164021015006640003180c2e01a142a143c5002a54526080310058569446004a009168040c12512350028082d44504084052000b407091910006564401c071f4034000a5032081459401681e9680001c82440c0c4030a140394901d810540d01c2c00094180681d0000e0010004007401c000024410002c501440602c00380780c8440700038001140025003041d40c1d03410b01c1c0028070b090401088203019203100b038945003c21307400d102c5040c00a40000c0c402a0304184808103091020345200d8211280502c6200207000c0c0c44c0c1000341d04603100195038400c403240d060401b2000c002a6020080d00e0139 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 377294523 1250 377293273 377293289
    0x1021009050c120a050f061b1305010509010210020a1809051005130905060f010f0f08070b090604030503031305010c050a14070215130e0c09180712020d02030f07080403020304 77
    0xd040e83d414203150828544510080143c445e507140c00504583c0496100d101c0d05450030580c0c14a00000d40f41c01103482002c203103a4400102c2102440158081e0010344100c22041c03044504e819031720680281240e103c000c450340462822003200c8100d00b400d20208010b030201c404240300600700050280c500030b074280682c1784622010500410400c1c025400910103940013401c0b02c0f65030412400d0b10340c40130401c0c01800c4040040c0000410581d442000010480d19020007c004151404d628006250450002980d100100300400070214200f007000d180070b46032608511400e402140742030750840b800d44614805000e0140034046c80e058118104840310115011071075074070b005a10000d0042d552030240c590100c840810040d4500041c1640c81c02550303a208040e484c1d94a84002200c4c69004214046a1141a52417800805030360315102c076401016508202441548415892050b40c02443e21401020b5022081204035480628413a420006c40c2c20488280e0815032030082d2070b48507901500c60 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 377295773 1250 377294523 377294539
    0x180105120f180114010302091006080103080706110301060203131719050f060c03071106011212030b0a090b040b0402030c070f031403070806100e010f030e0a02180601021009050c 78
    0x1c1454812940080c02c2006000300180c0ea07501e03096400f1138000b03000581c003800c050740000e4009040f03110b1b140d081d40c00c2e548031640c00d680f82d0350f110303c041c6d031040900721501c1d6280c00207050514041e5000d0350103882d068010310780710b902ca003080700da401180e0350000719002240c41d011000b60001003114071000c801c3d024004031a941e9070030440e250501c03252008030b541c41001c1c200994404000701443c000d050030f42d1100c0e80c40030044100d503501c0f48203028000c2084640c4031008001000c49520315820226801c0c0814420104170020f2080358007a441002e07480c0d100c0c3c0a410040c6850300c15103814603800c8074214114100303044041018080d51100030302403001c2803040010b160041481540786122001302039034a1a20400080c405401074503d68080c0c0d58150722110f10314000c80b00f0710030b07292040c0d5507034102c00b44002d011409072100101c40e0441d8002c0880300c4003d41c403a074040403a142c011800074005030400000082c03403c039446584421307440c504650f41c40010804a242d42c01d43e00c003110105 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 377297023 1250 377295773 377295781
    0x3060f07110106080a080a110606060405010503060f0301090b0106090602031611180a090b09011b0509010c0c0801050f09030a12022a010b0102120c0a0b0c13080102180105120f 77
    0x103005003c9500b204449104144000c8104506440240351002040da14403031450f1076400c00b560740b44003c3e1500c6500803c180418030141d44200042c5520003c006c0c040c05c401c40c49103000c02e0071500c1090b815603e4811040c0140712081c0c10407a07410040c210791000f1860001981d04920004400e010010940046071020001c0c03660b45101551800c655a1030f440441d090491001000700382c43d040455025a144000442d5108180320b04210000c15192111500300203c01c01c40313095016400ca181800030003d081d00202e10441c8441c0050500c1031300004035030403e006c0191144000a00543c0a64820441d070580b595000c03455070030b850000d880150700c030390803010100201c01c0e15200d1040010b06403d00130881c01d50540150440070303004e8003500c0082074511401d403031a100d001000800781c0d000202d120009503a0815441d0310107045510348d4100314413a040c13203000390559801407540d6034000c1541011100741d551541c81703004003420318600c0c1541e4182d50002418000b0504090b00400c98009 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 377298273 1250 377297023 377297057
    0x102190f050f030924030a0906060909051024030303020717030903071703060d0b04020d080a0519180303030218030111070309090b1f050c03190e03060f07 68
    0x403800c0300d910206507000c00e03069030129540c9802083c9054850841c40c1541c4040e081da2000000c0a420190020340c90355484940403005010741060458800365102e500090054491103140d0480e803042001e071895010084d5400243c440780404020a000010302c10040d040e00210364504896141c200941c80c0c2c60982030019550aa182d0704d222a0180041004071101020004090891040024800c003071201c400d0346449000c101c54583c0c010364044142000701d40800c850aa00c40e04c0100300d46d90041480c0d0b00c451854000d0751010001c99404613500c0341d8000000103200041d4514606850503001d05011f08210380c51340c1c4006000c2c19800a03c04008201400d0f4007a00041c01030024002101541ca8074803007039121001c10380c00070b480c00b80c000c01c0c0038165010706c40c0710050040c021203501407411911503941c0504c6c030b8410b00340842000070704c020040a10151849041d4143d040c0340a482210024250f038001c0040c0501ca07411000400c504a1091082e460b0400307054644103a090b280d00c254 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 377299523 1250 377298273 377298293
    0x2808040f0c0f030305040503011a0a090f020c01180c090b1c051603030206011809050c0f060d23010e040c0e09070305071401030c050c060a050402060409020a020a031409010219 77
    0x6010b600190038404418190850700600894206030b000700300c0808071840c2c0748a101341e90404250301502d078a80400c0381194079000f20908450f00750b0014540042081d100b42114019541d0100c4419800a50b80c144400703590054010702c4100414000303002c04600051540e411b041011200ea005244071405001040151050b42005c00c0b000380909612418060750700d0109100707e503070905400300d6607854007200d80078200c42203a0180081845002e01c408100240700780000494000205100c0d043c00c02c41603000e1003ca03014041034503d45240b5000f503020221005802845a14505d1000d0100180d081c6184000701c42c02c0b203070001d2258891503250b0b4180100d41e0300207001841644804989111092140758081000340c80410000c0c400000c05c1d6050300a2802c0c036152900030700000341c8a011a40c0180e64480c1c07008002502c2d280c1c9440b001d000b00d0f0000016040164408003000b0105904a07410107010901100118203207015640001d540d114080492030041d110301042c2e808002718221 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 377300773 1250 377299523 377299529
    0x190b0a02090607030c0c092c010b0d06060f060507020f0d020406170f010e0606150c0a02040912090915060e0402090a060f02070b04140108041b0b2808040f0c 69
    0x1660f96800c41410f0003070150a043c2419280f82030310a000041c904041c0c820506541c4c4040c1a8008401e102c0070309540e1400015900145035481c1c0624501e6030791090521503031503200d81000201a801c2000241d00b55203d0b401c2103051040402802c0d0241ea9240395a12015800b00d443c414201480d10204000d032042d64003043c0c00308202c2da1001450b40700403501c51800280c550007005003090800410355250030965409402100030307020035110140d003c00809840d107140084482041c00340d40407500310350503518203071148404c1c00102020385038011301c001c1c02044403034018800c500c0b000007013038030000440c401c140074003503c00d220200d981c59131b03015a208a40010140481c0c559655805400c598071512450011b0041401c081000c0c5000010349082e1248a01200c07010400c03400191201100640241c071420b11600350000c0d03100036003030002d01034102900103d4854507105041c0c0301c8403198207440b15440341da51a42c0c006085c0e004d4881580650002041f0b0f80039041c504054000d084560 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 377302023 1250 377300773 377300779
    0x60f05033702090f1512040609080a050a020f070602101a040207081b0105040308041101021f0c0e180f180607030c0e030312162f0f190b0a0209 63
    0x304071282031650950150a2204003655010059002101001100c4c01c0c03a1580c076203030340420b11080740140a01c0c0d2840342d0040c41040d00003046d0b1540d8840e0310154014215013030001d40300041d0b410b000e59051002c0e41881e503000d00200441814080040d480304074802400a0a03550ba011020b44411929609036007840090011550381d50203050542da030394031189900c403e8004c482ca0048002030148107007480b454140d07a48000315121566540c0d0759400500e512811446085c400360303452500d000c2c11040e6001d201c00e001507007020001018250b13144010809200b8000040710b103110301d4003420103540c448400d0140c0100740d522065144102506000c54011500c1404100080160103034004942e0401d140c80b481d88800950007050703a02c1c85034120070781500c030040c0c000c07602c0030300b41c3c484521030089141009804543d1481886a2140b81d15242008110344000040042042440031190a00d46000500544161031000c04190041e00c0c00044c904160314000030a0511541c0c141c4107000380003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 377303273 1250 377302023 377302111
    0x702150a020705060702070605030604090c050907030506090c040605070b0703061a0310092307030219020105010302100305010303020304060e0102100c0206100806270c090f070306060f0503 83
    0xe144000035004400100c0d1144140c6001c40e40f03640c000142c501c21a400350fa00c01e480d40e41e40c0418000a00100c44048500311641c02012440d5501c00300013a02c2400c01e0b41c1c001441d07240900801920036009885c00940d45820441444060342c05070444102c01e4005070308070311076140c0640840090a10f580074a80440e60110041007410611f80118021311081030f07030320300c110717107030f8a02504442142040c103030300c3c10b1030000c42c01c0c441003440d02503648491282001806c00c00801c840c0740300d04500c1f04e00724006035074070070061046103422035140383c0e07204940c0340401c42507041da90041c3d503a110f0390080c0d00c00e100b40481d5540d660b80c0700b00011040e401d203614007440183d410800c007035981c603401e58204100a1018401248034a00050501d100b10001d800d01c010442c3d00ca44c81090099442c1d242d20100c1c080c04090000c1601c4112455018100ca149500c91b00c0c94500030040440384140c02c45420402802c0e003400916034400705507600500810084802000d80d14034a1544595219151044e4444 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 377304523 1250 377303273 377303281
    0x302130308030c0c010f02131806051e12030f03011703130303080114030a12050d020405030307050f16050d1101021501090501170a0b0c0c0f0f01050a0b0306090a020405070215 77
    0x20740b5020307207130750090400203010406600aa4900382e010392411411900541d000130003100381c0418901200429007040050419110300c0800e00400d0a04c0c044d07030312607c6404141c0b00354185860454550740d00e40d405181090810b0100f46600c1c80184584c1d804904000c11841d540c607024000c441c03101c03003c0000c40c10050b680b8940a040903209204d4000b800700381c0180f03090181008214281081c0d4031400d030001000c68481b064403541c200c07013004e005003a030074040801c803601c04200030107150340940d004009174030040302c01c03624009054480c485071100b03044c0c04104d035131a4242c800180c40d038440c01114400d802c0c000100c1c60400003000075032982210f04000203801c0d0300f030b41c4814145c0344025013001002250075059550380541b484000d001c0c400e13800c000340058181a01a00301d5181000030384240300a841509403401c03e0310b00440e4102d941d00e1301031004400c0c0600c2014903002c1e00360082d08280c903041720441e0315030391014400f0340229110000a00c144d0b2083c0010718034089100c001240e1070038 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 377305773 1250 377304523 377304541
    0x803280c0206060405092b050c01020f19051c0c050f0304030806030d02030a02100507021f0606080f07020a030c030509030f0f06070206060a21020d150c09080d030213030803 76
    0x100580f4814029444c04010a50141010990000c1c400204c600c0580351240d40106181800101000c007080290030b00c4005207103c800c0c002041050030701c5502c152215144c0c44100704002040108000b031200130891010544541542c914074161854030000b2001e040f5a416a03140c46138004240e1900d50000801c420560000d00301c600560341a0b080b9a0030b1881c48109980d00d1003040244805a4016040d41c080324659070041036001d1103500c155410110103c0444400e0700d00e04912810490301c40106101e0300e40d006007803039408010320305440d0b82d074248440f01075122881508050104070150216030241402041118040d00024040b9494a01c5084110351240711406016900b409210041034009100090b09401214010300c00405e8514049917509000419660703180c051850208000140e070b100355100541a00804080311602c40c1404101d04940100440e01e050065180c428082103400007400041d1104508005a0740c0107800718100c030b0b01c070307169000600c0306100008001c0c000ca = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 377307023 1250 377305773 377305783
    0x5240a05040e150c0a0c0f110409030503090c040b010e0613210311010902011709010f02030f0106020c090108070512030c030301030305090307060905010503040303020d2c0d0504030803280c02 84
    0x2a143c0d03c9180181c1c460080c90f002a01c0b65000314800150003c01410104c1c1a201c03440d0b011074031407088001100c2444010405a448641e41070f00416800b00800240c44001e2100e4141804101c40c00c00c0404070361030010705500d503c1e4812902840012620012000d642e0f24080c02a0a08000c046c282c034000800d448550030320044100c0000f5804600c1d10120201400744210403581619a0309104802a540103603036200240a8042c079900d4071082d01c8098018801580a01c10742c1c145d80303600e5810200f0103440e041d0680b0f8064019030745100104000c0b5000310344001940c0f000c658000844104200092860041c200204294080040000704140e0090b00405080e00140c080d40c000c3d69498009075034030030141c410240440c0e01040010700003031181c0e004141146d450304000500800b0710b04810402c012800b0080405a101040001c03000b000700071b06812030b92986802483c1174150745c2d940c0740600000e404918041e04a2030034245a084481e6486500d140076402041000c1d40700700000d40d15 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 377308273 1250 377307023 377307043
    0xc110111090f09011404050403020312010603091103030c06010605030a1e14060d05100903120504030903020109140a0306023103120813020d02040e070801021b0105240a05040e 77
    0x207001d0b00d5480780043c20664102412511040b003070407442d80811060001502006000b1011804100100d040c0d90007641000c03800f82086980004014a41c1e20305031940c103000c1c0020900c20707401440514071300300d000100c2a05480300c502d0066203d40760501148050b1091448081d020421038030104082d01540c2d010b10307841ca45001641c0051344420302404982d040041010300117800201c00030791040740541080c040076210f454202c000b0440c1148000032240e00755800c078005601904100295a48012100c010382521050301074440020320014181e140c2c00e01c401480340c1e40100d40b03441d0a860403041c030b03c520940d5021800301c8628400803040c1c078640341c8c001111400d101e003080f117035110301c902c02091040111041c00b14841034035800300007480a4046040740e0158690140380e413041c00502c400300c028500100050b886000501000c211014400301d0031189078900301c02c10580841741d0b0101203070403440100da0082c40c800203000c2004c2c4107058025540190402c02c605040f400009441054 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 377309523 1250 377308273 377308279
    0x1202190812010f030515061c060506030606400e060106110307030918060503030f1309050417030c040503010203040c290f0d0603060f02030414120a030c11011109 71
    0x441e030325910008035903c003e020107007040d80950030b50701074401c1c40d00c5442d4018a0080c540903108200580c1c07080b0107040c40340226001600c1e00280001410b0030840180c014000320340120036405050100b900c0200da401d4100a16400245004500c64111040c0c000000e2140c00500000503a10007403a03070343e082032040c2e030001081400002c12800380401602e0f051a07041d030360740440034071308132500401c81e00e00f0603070000d80c5548100003c1c0d40d5608100030302e01240411203031500c0c0c1d0f040f00c58002c03aa145a500c01c00585042c1420040040c01a1081d030040111000c4515100c0c0c0381d0b004c4070f4885005503042590150b1001040c030081c08010340301c400403a0b1a62b5514100fa146a4555090428040f0740a8203000000e01c4580310005402018100008117100001004ca80d03c1e210b44040e01e050000c00d04a0940c00410b00c41403101c84101d1180b8100c0001c010050034003054048242841105056803c00d80d03903081c902c3c000792244050000e40f1802c14020302c030b44000390592105507800103e10501c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 377310773 1250 377309523 377309557
    0x17040f0e13030509010e031606030b040e070e130507030605010b030103120f0e1e090a0204080d09060819110310060206011a1207090308130e06010503040206030412021908 75
    0x800072020341c14125155905955072803d00c598440103481d84403440e5401589070040000c036601000d902c40300c420040c07403559804503a40d0220f02c103100803500d241c0d10441e1607800c0a94140b1003110305503003640d0002c12080c0040c00f2600035003010350400081d90801080b9605000000511513610405141680d000354404000d91280700000d0701d2100808408002107041584103000d1032428400400c8080407036903510034483c1040c000110700450448042d60f0701c03580400c003402a0314040010107104000c2e41000513006041107009007610300010040b00d203070720161400300e501d150070341c2061400034000c7c0485500c0e404c00c5c0c942c1a610440b54090745006104503400010802200281e81090028072100c4916003105020f1484988000900c0b42c41481026500000000d5002c2c0041408059a400e040000c1e801d00590003414580540010f04002c401d009020150344e6442c100e0b504140e02103021103000c139408105034104100e840c0007000c0815100320007000d004408004000901048130921 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 377312023 1250 377310773 377310781
    0x100e0306070519090303020d0e0406150201020d0e1f0506311407170a060b0c160b0f0904021c020a0f021c02120d0204150504050108061e060717040f0e 66
    0x44d00c0f901c05100c0540140e000c940712040e05406880941207140010b4404110b960301d411444032040d01c0c50b246000141e600144186440805214103544e0390412070180691445d0018030300b000e180984134140b85140c0c1d40d400324440d95141e4102c0d0034a40300c19481014000082d50707450024507a0151f0082d9404e0900e81e000da20781e08110b524503c618030546402c64070154140005152080042c880c1102c0c55446401140c5403034020003600c03403003500c0001800381450f80d6802c640140c5241d80115081e05041c04680d040312100300c1130f1242240c040c4d4005882d00b400d9004d4120911054000c5001079200060b00c41c0030b00c0d070201120b28401110380848480d40381003855502c004680c0344a00c0d0043e0850000e8800c541d00c7c0d07000826007030031880c00c05810662615406d10f02400c20302000b0001c604006010805960040c09856004800700ca40c0030360700d08a408801040301c0015005131240c44c002819808100f0724050f041c1603803041a000546030b544074290070942003451300074044840306081c005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 377313273 1250 377312023 377312027
    0x20409051501120207050f06012c130201050a03140a0b030111070209040f020a081516020102091f0320090108060621180f0c0f03030414100e0306070519 67
    0x2041d2422060707440e1030441128a051500035040404200d419010f0308610742204502004007502038040c1100100c510900c0903c024400000c0396000b0803d0310007507081082011000440e20095a02800c1c110b41c1e500e40c56004a00400109180c080d00d038204400303106406589034404c0d0500030041c0d00070403c01165501c0003500d801002002540410b2890020300054501c000c88c640141c4043c1031145032a886050713841c101026020315501c6a0032071400c104c0455034503a8038203a6622640021441c02841402081011880108003030000149414044007148a5800030448040d03002c220601180b04010b442e2080c1d2200d003d02d400a183c2c8008208203140c40021148140d100c0b2007802c01408241e514001c469400034a91814100c862000e191500703414090380721007a030390202820420683c2c00c2080480030345000c0b0301c5d0080d0320500050140e2079045043d40b03e10b4408894020041c13032f803823400720750095110402d580c0600440003030184140c0c01c02c028080319030070038092a2001c9801401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 377314523 1250 377313273 377313301
    0x8030c04171b060403150216020a03030201020c1b0d030c050f070602030405030c0105030c16030c02091603110c0718180c18090b0a1d0d0207060206060a06020c060a05090a0902040905 80
    0x1010f090a11540b0070a031606c4000e40c014000c882c0585400228007813660002034040b810b9a20a0300540d40010703206e00541424041c40b4030003805c8140d8000c51071a10008103502480c01070000341400715a00300032040c010304012610102d103001301150140354503018001e4481d08588602030180c8110001421198055019688201074888180c0d082039008018003c1c0984280d00c1a02400f03404c03080b580168a51112581c0318100544000c0003400f04040e00600b1104162440300c481201802550b07202100070546900b1103902c6468240c00c4808822807030000d008c0c10010900c4550401c0ca041d0030040520344000c122920300a03040c01100880301c02006850705004010820400301d03000402c08021503104a4141b8203003048000f0f00f00a4107040341c80c2002e031848000250b8880340003048a594100720b1140c1c860340035161400020700d80030000e0340e240f103290090361080001040e591140d031321501c00d40d00c41c0381000340168043c96594981c10000c3d030080c0542c20241d801d02c80000c1c1e140740388401c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 377315773 1250 377314523 377314529
    0x50925050f10050910030504120309030503070f090b0a03060305060c040308120424020408210d111606060f060219020f06040b030a05090d0206100308030c04171b0604 73
    0x7080095035900304200c4802d5110703030440140b280903c01440180c80b401c03482c02e002d1000d0b844c000307480e080c1428186210341441d96901c041508082ca0000001e0303200301902d17000085810180c1c0e41c81c00700702065600c842240c21015035804041036003250190701d60803180c112401041901c10580f100b540b0084144918000584032150030010031180109040000d54014041d401405000c402d0069080c071000c10b8080907805c0680200f02489001003d00c415001d050203406446400b40714040c00c0a0a4052408808081d6944140c08001e405a2074121b800f030002d40c0c50501c03d1000c081c42c0400081000f4021941c04000b003210105d02140000795020107011031411600d02d2031825070800901200255040da0012414040018107440b05d0010310300030360900a02040c5131410b042700526160a4510003c00c40d4080d2080c03110100e00e96100105480d0402c1045560713668164402c8000d1143d680025148001d41013194034280e03020030000b01d03030300180465014071043c680810190703010f640 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 377317023 1250 377315773 377315779
    0xe070f05070602090303030403180603020a1b14060f090115060203120702012d0c03090b015105030115031503120203120105041107060e010f05092505 66
    0x4240004094003610107045950722030640545800c0c400d601007421900242c0781180455042085000c0e105005032014019015514085052044442005181041c0e400c804d0121400020b410700c14000716509960840860508580007428a140c4103000354408480480d825403074000c404590311200158502100e004e50300441c00d103803d80f00900710b001c40181c40d08056650711301c41d00c416041040c8006440041072200d04141002602409003a9032002004104051610560800007001040824155602c940b180895124141a58500c22440c460103014007011043e4200805003080704c82080c0c203020070844111025072103001d640d140000c0c05200c03418034100103c22500d03071080d44509200440c450840740f0040c0d41751200d11920318003107081c6c401070b00700242070550800450000340c01010700703840420040c41801488002c5020702c010051031242c03598000b021101c1d09401529451000b444100b1060030f00c03900c030315aa540010019800411002000003e01c250141c002044400203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 377318273 1250 377317023 377317037
    0x4020d230145060f060c211e020c06031005030c040908030a1e02040311011103040e010b03040f05010608031b010209180405030d182013020306030f060a090c0e07 71
    0x24003032215141402c190190390b8070400a15006070105210003030034107440e46500031043d1300f03203100a21066104010b000c0082c0b040d420305194441c0380307002079100c080d01c0030b4010b40c1e590724121709004001034950742c400004414048088400406030301112400c4085459140c0d00b50288001d0303495030b40b806080000c00b070000607000741e01c60b040b2041441e1004030252a03650403002c0c0e4800c0381c100d070700240d42040010551070b1455800400560405003848015401d0520b0000800901581401441d83c42e59020003c1010000c641c0310500040d68023400a00a864480e02c5c8107990f50885002032a850032000c5041103940d01c103108903120702c540a8040c503c00b650f4a513006070408000750046400d44000c120901488045210f504100e000ca9642c4000320f03025818880078400d1401401008040d12980a130281d030348011006402c14440d01d409600c0750789000009062229060188599009a408102c0b80002503400f0240c0d091281c0200e00c50b403034455508201c401c03000c1360f10402003062 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 377319523 1250 377318273 377318369
    0x4060806031506090c0c03070b0f060d0c090c120e100507030b061e09180403141911030405120106030b01080d05040e090a0f12110c0d0204020d2301 65
    0x42c4c0c15607944003c2102d0160b1070070004a90441c0b9540c040003058945406207020b1040c26001c0c45440303904401d0403a603048045200780c9890070f50204920401c002959120507460055001e01c1d2801c110134a0310381c0c00c000d965140c030b16041c0c851500c00710302d1180e2803800300000c0d90a0700030b104104500780083c00c42c0c6d040c0100040c0700c104500c1070503003900c41e4200c1807203000a643e0350180c0c046841d066404803103040381441c0c50044d0408400030b10303c1e0052038041c000040d1040c0642545031850701145030000c05408003c0b020b41c254460740e0040b41c0c020300c0d668020304103070317905420007011039119002414031680d071406a284c0310700301d00410400141080000f0001d0b0309802059a0b000045882503924400d042e685101c1a030403504402c8803904921003542400a4100941265400c0030070090b10142018800042101b03d034110028451940840d22002c200780d031358450010760b02c81c80c0f02070002030000158a800c0e1103091143e0743d601084c0a205d145c0700e5210701d048800c9030a003500e0248000381 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 377320773 1250 377319523 377319529
    0x50603130807080a0908010c0e190e0c04081e060105010c081309051806070f05130f17070f030201020c060d0209040501090e0f0f060109110d0903020304060806031506 73
    0x400940600031504211001601140030301c0010110644600085661205290005448040658404211a490040310b209481d070401d40030303112104101d540c0340d1003030000d1008054240864002042400b03101040210390410a8001c00507545030f00101d60411900044401001c0c480e030030811000d800403c0108419401000c01c032040d18400c0c3d00c4c2e1030611407114881500b0f0f44169001c40b081d1a240d500780b0681c0e4101c1500480500441000f403c40b610b04040e0103820a015041b400d01000000500c110580d003810701014064181c1c2c0804403d182d41c1c0c0e4201b00100300011444080c0c50240e000c000a1811a01e1807402c00c43e50706801808050190700c0030801c4580084280c00110707a020842c2110341e03521445000c0c06041c3e1810300003148480f1000c110314111036009403141c2a84400305441301d0ba400007d40c503044481e1040041224807a001000a41d4001d1861075680203003031002c42c004060700440a8000e948482e070310704101e81c0c3e4540c1019a2070074a61907544000018030082a41d41c2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 377322023 1250 377320773 377320777
    0x2109012406200a120e06030402150306130207121e170606070f030305070e04091113021303080c100513120e130605150a0203220f03050312011e0506 65
    0x140e11902c0c4402001d45500c0460f007442c0000e40c044425003204c000c1d41060541011001d10403030303c285d072072500318541540465510405000700c0003d03982c001c00000d40d5035640000b100703070400d0350350400e5480d00300501d815009400c840e80060081018080e03004054078800404841c0091103941c1e07081034080c606007200403080c01a000e150010b4081041e0000300e10080e60303a00840e442a80c0000351803415600c0144207445400c10076120303030f05100c2e801000c59040c039240040c450040340c02c00004400014440d00034802d00080040f001030301c00c00041441480005000303c10804000d58100c6410245c040044070b070100c40c010140e4100d4142d0384003141c88a80c94021403011414095014000b000000c3d40303c16000600744e1525407200c0d814803143c00c04034000216141e0004690781000c06000000c1d4481c003844c444016014005036104003100d1158078664010400324400c00d940c1522800c000e6140e070300414603c00f80303402250000980f064600903100c064295001c5030400c00e81010208005d036 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 377323273 1250 377322023 377322047
    0x21f0c020309041b08070f050d02090d0c0e070e010302030f1306060803040b04030c0f08070e0907120303091a061c0303060801050109020a1826032109012406 69
    0x40c881800a9101602c0f14410b1502c032002c00d9a42546000c0c284100400086005000d901000034802c084501e20381c100c01541d0200c00306500140e15000554007007103c0b6808031001800e0075020740400150141d4007103482d409600c0d20741d14014007008900040d4144d102c242c1d00d07503040e145441d00040b2040c40c0302000102c00ca1040502041460f03907920381c685103400540104002000c001010410410359030020802801040d0520030040e10f00384450392140514494050484140400120040e9050000b580a058100c1c100031110b00f55040080c001d00c12084200c4103140b4150801410a40180b059032291000070a409104007500c080c844020b107252a085051644400002c125000c0038044c160203000c2c95100140ca4480d401c40c020440414180c081800d003844400500c45154081c00724405010210301008000707221000c2549540b003000c61a4103801001c000c01c568043c1c0091f192401140030340c009108100680b607047d401c2e24014000440010302807030080000c280241a640381d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 377324523 1250 377323273 377323277
    0xc01030e010f0e0d0e0a081c120e0a14160306180204060b03061011060106030207080c0a060e01060f260a0b0703050a0f0c0c0228030f0210021f0c 64
    0xa070021003062600766100e43c1603007800b84c1c00c480400003000d5440a4100b840d08030440e500c2d0790403450403203c1615448144591140c2c482e202c0031060b40d003030181c0c4100c8c2c0c250b0000d480400400c0000d814094940344080310407111400940001020a140001c0e03450841c00c511115010341861aa03400c5c1c001c03c0032108a0034050071001180780566141c0c82080000c2c401655825507916240c002c0190a0001c40d070b4980c140f14158480010300c050010f5410306480c010b0400594910060400c0c81050203040e203015420f22501100d0800c02255400003041e40b40640000d021650702d50341d81881c069014025401929080d000d9000f49035460380c00391030303918241c3c000c0d0362000682d900c4102040b070044420b500441d40b80d5050081c1c0c09403a05c54452603548400301009189005100180f80e90442c0310060b114194000b8499100503001c46c600c40c03d800b010948829441d9241340c10250705402440aa00c00d0710354050311480c2a00120700c03800c240c0d2010354699100c1c00b580d08500000d02e8507e45084c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 377325773 1250 377324523 377324531
    0x203130b430f050c0405090616140a0509040b0406060c06110903010504031e02061006051b1b18010b0426030d0b0324241905011803050c01030e01 64
    0x15042a0125001500350701640c8511401c1e00729080c61813030081c1c0403851318060ba291030200500008045040c98008020034540f22010901d00000c40701c130040b8112b203046640700000c841c14282d4000000340200c0400b0340e01440030603444800c00c4200d81c070b1032250748041031440010f0070025400b688201c00d8204002900381c00c003000fa001181c00c4600459044010030700211030700b0b4160305240300c4400b030f140b0640f0052900707107458690480c3e000d1040c860b4005009002c140b1440c0309968440311044c0005500c21901c0740725440c00c180c0c8024484201650060190146203480d1000389030060303050740c480d00d400d1490646008000716001126480800550740040400112440280018400b2400360760020880b021104209820856803c078680021120000c040e0f84442c1e00070030b02e0ba4050a43c21131604096000e021901c5050b814840c100e074800c040b044d048101108216588054640aa982c2c02c08007800e007011004204c02c50001410310381c000803190919610070740004904559610000c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 377327023 1250 377325773 377325877
    0xb130611070303091a0103081209010b2806030608032d071a070e03060601110c090a090c05030a080909150909010b01030b0f0d0f0201140a0203130b 65
    0x22003260489101140000d0712075400c1d1080c000120b81e05890707440000e03684d641552542d0744000300c5110f08151036603803407800e43c0002c951110030741c020f448001001d0284100d10700c2c00360b1080c10f20381d035000141072006100c01021412921903c40c0b802520342850045141c0014030901c03103400b07210556800030809100c80010444d5882c1805800b680f0300c5400740804020807490000b40d815001003442c03007004408021406195000110507030845802e08042400448107007015050500c007200154001100005102d40c89595602151506004903409280103494108042d101d00c01c90030064401e500034494a207451801030b81194010202c440383c62921030701030020079070100f000c0f00c2101160359540c070895034030f5030140502c1d00c4207941110000034104d15200000c8000c54642c0c0c0140100c000186001d045900500902c0108407025448079100c48104038002e540341c0c003e031010104e0040604000a032660741206079030660100d40e040306590b01100c2004100ac5180e01c0c030308510b103204a0006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 377328273 1250 377327023 377327051
    0x1112107080408071202040f0b1c0501020f1210050a0501050a051c050408090306010609260c030613110a03080406081f08210306090403210f0506010810030b1306 71
    0x20a00038512400d07105d100502600400c022265005a0301c10003900b090903108241c1e48400c4070858108036a0446600400c2c40d044c264028041c1002610010304d00007890340011a81c14402840b5203c001e00380706001d5207440910605008a2240b940440c40c14080c40d00058021005003011a4200c1c1184012b8607185a5260a03600250f8040d11030700c80c00541c040b41c078102405018050625414100841450305a07001d010101000c10203030208021640c10f1080001440041e803441401000c440710b0b0b040c146908800c50042880c01c072480600d07841c10164904202e034202e81101d170000f4400d41000d18104042d1901040100f16491105000c0c030342013040021400210054080310005101c04580110801491988160801204041481003000559402011692003030f030614000446d140851807119034102003020119080b41400b180d041c032900f4641c4498810032090741d60800c15225100c40d000e0380d0142d4003014080707454220008845160f808141840113200d40400686000c0010391 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 377329523 1250 377328273 377328283
    0x20a06110d0506181b07050106031a070306080706030e01020405100e120d021209030c090705040f080c100507050709020d0f06140a052403090c0103050c160f020609040e06040201112107080408 84
    0x10441d56510b6070307031403217640e004101289335001e00642402c100690030b04001e59074811507803280101301070f100d061319400e00f0400c1d01039030003c02001d001091001070b4900c01421182c030008000d40181c503444528480060009002c0035095800d40141c540301c00601a581095417107495103036014440c80c0c480451030f8841c1c5012500c0b40701c041e81c80588590800c032907a040010540d100d1400356226022045182d9030b10718504e5584031207805c00950b90200c0d0b10340b0b5400c28059a224140852011940c50000c040030f40000804124880302007140d5611284800307107882007002c21a0f003000700500d06010030704091840150410000f20940d1f0000081480070740d2a80c005c8807001c1c1a604100741c494010358160103000d821126000c49070342498088540c5000c0c05002543c06089041184402c400f035403190800c80d4030b17040d405001400b961600c2c800c402c2d44c035802581c089000404280b40280c0c40c940c0400c101d56040804c184607a42405e104142c42d0254001c49004e45141e0301c2003100103071841d02040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 377330773 1250 377329523 377329529
    0xb0a08060f1c120c08091e030601030c05040c08042105251101020a021f1b050c0f010e0a05011d040c0c030e01141603020a06110d0506181b07050106 65
    0x8031003609141c00d01e401c55140180d0346403c0140034280c0290380001d1a1102911601070302a503076001c010303d41420403644001412030581d0103009020002c014808000b0460080d19020b450a00011051304400c90b62454100c40c054003083c22100506101d502201188000380d4141c90700f0b81c1003900e51142c585400d0010860741c101d0704c0071000c0d02030801c54030a1030b940413200300340050200302d8220b8001c0388aa0b418100040401c04440d48030b0000d00303008604001070311035101c849190b200c406180096890600c179901d50300c130b0f41c0014850100341d84601c02c042c0d0240ca0251141041c285001c0054810303140c52001c07201484082d0100181e90f480b00d1003101644030540d03440307000e030700c08070300300070b4800180507e0703150411102428a82609020100b1140c0c0700c8080b0350075032b01308080c504080307087c95142180103103410b040882070502840c003603020b4001001595002c000e25115081004180d014082e0303c501c102c51072a0000e181381c07042d414640030b0003521000380d51130010250394841c21034025030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 377332023 1250 377330773 377330809
    0x60904111b1501060f081e181603110d0807060203090105041707051c0c1407060f030b03060406020306010512090102071a0601020a0212070b0d0609150b0a08060f 71
    0x20075241a0448104441d032450480d103040c0061950400000621403141c3c6030401041c4807046020500c0f8540b1082c02c500b588000388800015401c000540b91701c1511560540701e102d100e140d1462034003030080c486040c110307544113401c031100100c00c40600903c00504041610001d00500110020a40a0000310321500e004d100008080ca490b180c130000c0403c400e01e8055180c10180580b60000b500041c0189003252505441000c40c02010300840340441602d10003480402070211807070120000161103c180d03001078071260f040d060785100480c11214110003465155022a002c140421903580c019508460107150451400420109038031001c7d5082d42c0d1035515a6000542000b4817032801d29607140c0303100400394801c4070305104000035aa40b0304010040d218958080400701088401c101c210018801d903120540c9031000400402d000b49094881c009090f0b0a100109030305404c2003000c00d060303071203001550b82032041c950401c44180000400060304038440c1e1803454990781d2000e07460a440d00401d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 377333273 1250 377332023 377332057
    0x80a06080a0c0512070b0720060711010e0f1e0103020c1902010305010605031603050a1514100f021905030904060305011d1c030f0f050108030d051b0906090411 70
    0xb00f024400b8034402c00c0700e0a2916045004180070b030b01c0102d000c07500c40c0f503000246035100845104039103040418981070581d00100004030b507000c01020f00040c0ca0490300903283d0390444410401032116800d462041d03e9400003024001800c0e203050745002001c4104107250050030f000000c0801450000b080064008503520b100d032104c210340c0e150180070f002d40201d02d170003402d500340508042450590451041c003890303110400070350031050561110b0b20590f5004c58a030103041c0d40d02585060400c0c4540341e00d000b00d8854080c150b02e94001c50311081c44004a40c014182000c84d1008040d040d009288105c0d02c6010402c071140140c0c1c1c4601904c000f441c01000006201c50a00955800c4800c4840c14180290401e8082c1d0100c181400c0380304150030a01d04000c04c08140a081c0c0b60020319004800c5030459243c0b100110f00d060002010340003181e0009810811500c4900070f00d0b001480d10012488528801c01030300300c87e41810300145c003501401030400315114400010300080764100c180d10541d44510 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 377334523 1250 377333273 377333279
    0xf0e06071110290d020603010b0a0e0f060306090403090503010207060203011e062c1903050d09050906060903100e1c050301030213090c03050312070e040b0a06080a06080a0c 76
    0x1051000d502c000d00e100d0000c0100c054000541c0c04407240030b00580340f48036460000c02c0c2c0c0c241c9484800320070050380249000d68940c0c40312441c401d079400085201c80001c28441c2c0d407143c42d0408800200310b801004120500f10368451080000b2044020003c40400044240c00112074600340050000c2601c00c0c0030140c1c1700e41c14181540c00006207210a404d40d0040c40c0001c000042d0080c1c4103890140b4124400c0f00d4005402d9140748641c5880c0c0a4140c10104543c030b4450402e00e46203e01058a115a06a07035410324103403012200c00c9214001d10341c0c0040014045002442c4c14001400c0d011000f40a48281400c00302002c40dc035071110f04000001c2d00318000706030110400407000510464a41044e500b0365055401007054004c01d02615445166100328400901100350700301c400550348402182c3c5d4400301217000c5c2c904044159440404241400b030950280e1405000e601c0d4808400741170b0140291405074102d0308080083c140700b600c0f569900e8040380301282484452507240c002c00c04000d007a45 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 377335773 1250 377334523 377334557
    0x405040f050a11150901080f07210c03180c090207030c150515010207030b060d0c0e4017160f260301060e030709021602130506030d030f0e0607 63
    0xd00d5190040802004010a1707485a800121460b01b281440c402c1d100e40769a04030040d103030a24504902141c14454000c6122860f0403508045a20107031507030103200701402c400c00704c2400d03020400700908e00203079a11306100d140c00580c082d1240c603000c4d1030081c0d0800c00d20345600360203140d000211082c46031150104069052052100c0305a0a800e200908100b495901ca022400c14007802d9684140b8501380e0340010b01c2000ea17604070250814501080c3c26051002011000c501582500d047d100700441c2003898200d80091844c14001c4016902c14510910fa80e409852404811440c104604240b2a203548280c02c0c03003021000354400c4000c00b1200906080c01031b55880c40d01c8080d01d4204660049005150a04050b6411602d1900700500c40d0b0955900090034a00341342c00c8040403600c0400c158000540ca400c03c0440c050003560048030301104580c1e400300344d84d400c1b81c005400d68840441c0c2c0203851300c03d03440103030130090074030000801c01803c440540c1414001d075180d40000300901c6003400915 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 377337023 1250 377335773 377335789
    0xb030a020a1d01170309151b070f060219020405070315062118140f1b0f15041a09090a02090a09060609051219080c0c09040b01050405040f050a11 64
    0x24400f100002c400c414039030116503078421920140c2c02200001040700c05101101d0a991005140401e800054031080001c8c90b5600300c544180b04804420280000b81c1c1400400c450182012000c425030384041c0907000c0c003000d0280034140303400701a40e0b1211801c0d2901041d1400b00a00702036940c10502d00d158074401440d080200ec02c0fa43d0003072900c55007901c1010550301c050b1586030710809a800c8400404140c40c144904900500c0305030056401803928038040080c1d0315118075044883c0c403c0350b600c0da020701c81850600000c200b02403d0401040c03107a840b05440145419071803c400c03c2c60300d182400440e44004041d10302d03c8415030082110615031400e9005080580010a03041160f40e15004009098035480e01c101c03402103110502842e80503d060000003002850310b4000d444c0246a458024000e610107000f1141502602103551181d2a045001600481e00107103041c8050742000200001041c0180040b142c2401000041c03000030b0060100900203406907000c074203030003020000d020b941 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 377338129 1106 377337023 377337029
    0x14030a0501090c18150b0d060306090b040c0b070503030112080403060903090501090f0b0f0d06052205010905070c060e1f0515060f0d0b030a020a1d01 66
    0x40f2145145034011141c1c0014010807003603800f00304d80120b44680d241c0d40744510b80c0d01d80c100211242c4001800400f90300500009205a0301c0e81e030304040b503501030030403a68020784008020900074480410001041d01c1c0518a240408a41e2100d41f240320500400c54640743c6420510144114501558040c0d640321500300003008040c1005800c500b5640301e4203000456251011030b00c0d20041c603c12048400e00440ea03400c04000380e07003126243c1c001a4950311216691800012155a200b081d509031a0600d810040400e0305001104251507058000c81d030000e043c4002d0007045a40f0003044884580c01240025801100090b00ca05000700850410143e10444140c541160078580c009409105040000074800681c03000748500c60240709030031402c05605000c001c0340448142c00ca080c1d603400007001c0c2c4940300041ea00041c080551170308900c1d0060441c1c000c0300c00000d00445440c0c09 = true := by decide +kernel

theorem cover : BRFrame.Cov 377158273 377338129 := by
  have h0 := BRFrame.cov_init 377158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 377158273 ≤ n) (h2 : n < 377338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
