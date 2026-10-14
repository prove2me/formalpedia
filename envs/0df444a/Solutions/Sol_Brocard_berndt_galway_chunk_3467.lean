-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3467
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:44:40.354187+00:00
-- url     : https://prove2.me/submissions/037dee67-35c2-46c4-9dd2-5bfe974c3344

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 623381294 ≤ n < 623561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 623382544 1250 623381294 623381309
    0x1501030615020304331206050a12051002040b030c030a090209131704060210020c0708070e0a0b040c0f030b03010e070b0703090f150f02030f0d061706010e15010207 72
    0xc0028007550768020000b801a034001e00c54080301514074a180c458141606100c1c41300343c50000c2101d50110748601608160205074600c0401c1c92a610b10000c0c1f42441c550300806615002c40c150481080020010707060780034a90740040d030410345802c1400305580801000302d0385202d00000010980100e0390300100d425540107001c01c1450402e0b100a1100f10003c940856203440440400307007010000000340d800b1a07480f54010320362003040d52031520103504032400b200503501c01c00e000801d10540074440700025051040c113401d06446d001f03280700152100301100c01c1c0154034004090584035801450241071050a080120340082400c02207401410131100703003110350145140100c0d20100300c034000c154040c083d0380c800f8081616041010351080c0548038049404801030365980c002c07401914124000f10460054a042c80415041d0748000d0380036850700f43c140c2c2d0f500d45080c408040030348040400030110307200400302503040500740b41e010380000d07001c1c8041c0030305075440c209640c2c800c0065a0151449 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 623383794 1250 623382544 623382569
    0x807020312100e13150c1107152606011d09010b031602010b09060f0d060c020a0201030c110c36160c0302070312200c0906041415010306 60
    0x1d22401464482030041c9000c1d1425a80443c00468013100804800d50704504410303146400410514000c12a61031100309200070101034418281d002d0100702c0007040700601c50580e07000c100d10000c1c41c408606c03144280308040c0c0410b90f4104420700002c90390200c0d080c03c11843c040908094900449000445241d0102c00d510021600481c24030103940501840310300c807009108402c1081c1c4c00d841c000c020706070300700e00400005010391520348041901e484015190f50b40155040e141c4034142c90598401c0f0015a0025a5110465a152041ba40c948a1030703d0070341000e240d901c01b01902c92044445841c4951a90b0b201401e0602103004640d103140700c1c5044c41c81581030103d5410f840c00c00c0403500b00007091001aa00080c2c035000e00400652030303078198050903a1b0741c20f540d00c081c03112031140c807101c0401200c40d260012010001c215050605107003070041c00003030045030800c0301000005090300c1c020703410035506429190018481941040390342c0a52001c00d400c06004a005050561100320a00d06 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 623385044 1250 623383794 623383801
    0xf180b0c0a05010605060403080702090714120f07050315040506060903010204060c0b0c0c0307030f17090a2609010309080f0f0309060a0207030c11010315080708011401150807020312 80
    0x18030020780d910402c000c0c04016a924100000c5000301d01c17000d000f0240400c01d200041c502110780c2584002517091448102c1e9640b8615843e6410181c00f0407107698030401441110000244402e600c4025881c1403865460701a1418441d40c07065001c050186071943d010466a0303030742d40199002c4501c083c00031500c1b90b6480e5402007014500040c1500e0b012840008112003503907038001c96215248040085140180300d030340456090b255214440108060f4000c501c5001c3e004a15150041e0400c50041c030b25030f161403d1184092414514482840010f85000000c0d0340c1e0210543d000c860090070002941002da08050b40a4828406810f02c5a000001d19040c40c01c1c0324000f8600408072481154425624030440100b24450b0b41000707400300f10410310304c7d40007030903420751401c64001c10315000c900c84042d0680c5480742c1c01207030400c0702140c00110341884655424411125050754222088405515007600c41d03802045816421003084000400211031500030400c0b2181188180c10308209440d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 623386294 1250 623385044 623385067
    0x5090a06020c0705150a020706260106030b03010e0604172a1e01020c0303040f020d140607030b090103110103021b0a11040c08151e0303070605011d070f180b 69
    0x12814000d00d84505c0c4c1c0403070912048118602078409910803500180301071803c10304203640051606410481641c0c1c20000c0740303a142c50b9051168024441602c0205020f14880101401c0d2045203c0e0017503030b40c0c0180c0c10000490158248035a441c0c20030104031360340d0200c031110308501c5004640a9000c0c1280e503800080c01880c0010340340c5004040600501e2000c064001035801e0740710f20307854070615510500111300840c000880c0007650700e10040c444103504165580311304500d904001000c2c841e80002007004070b0150103002c0c403885810102e580101e1907040d9078501221140a641860406501199102c41c80480382c1c40141159811400c48007858510314004545444244a0500503402c00101402e02e600440c03205005807004a20700d0240203065040c86506044a56055000b038a200c0e42c150b5103880910017017100354041d03800411550304103d0310f100020461040c801c07150034081c00b006415540848005081d00f200e18009075164002034808916640035045038141c0103000810840340b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 623387544 1250 623386294 623386303
    0x40b0310061d091c0509130f0c0e0303131703041e03150e033708041407050d0b100512010504060501061b080c0a0803010806070207080a020d0605090a06020c 69
    0x11a105454861560b243c0c11110303102c14000349208214420014465544e60040c0081d12080707202400107120b100900c04a002a50b04200002200c0c6503913101040500340d1121f04018080c1081d4004d52030410f601d0396511310142c85128a6916041e0110300340b038209000e000301c2e0010182540118010540c1200700313130052046201c202c85070065031a5030304200b070090140c1032102c4040380145081180054024002c05045080c840000c41143c8440150504400c1600702e1001603a40d807001d585407034600112524140810500c1c540d2008100308119521130150302062988041920440d441d00e40398040c050005800c400e6000e01020b81200c1218815841710b80b080d800348000b0300090340e0300d14007a544420703401d81034403483c052488050086031651006105284040048600b0584076858450860f082a00b14000780d4100e6001d0004d103650400c100030141010f81d0141c083e003000d56000490108440c80c0090855456400003101c1d06028080e0340b6606030803041c1550f4410340035800d9030300d8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 623388794 1250 623387544 623387579
    0x1502040314061905280e071814060d0f140102030408070308360c0d06021b0d1704030e030f060106090608090307060e070b0f1e090f040b031006 63
    0x1144007540c4400703103d010700e01819000300c0145000e1644402400030810344808004880c840003500d803142802020303020060340000300349000b5454418055803c8a038203503a205a00984003031540c209020b103550300c11082d0f100f00c5502410140110089240010025091240d003050765440402000305101e1805e004200c50f510943d0307080c0681d500c031001121488014210011745020b81c283d9203500300782c00001940801e0460342141e440c8403c03100055407042180d07038120f60003500801e4400d1103403241030b0381c0c00c10440d582000d8110b5000b1800010f00140313803031610a078036501e52000720341410300030054401176180241c10f40f00104241200b59540301070a200380b500040d51801c0c0090014481e0440d18028a0810090352510f0a60385813032003d80300340351410700301c0d00032007030009000c102c1d040c006d00b290960b00310001d444040c040c42460503807a4100700c40210003c1000780ca1560341d6509008800180100c40000d00f0a030110007191512401c0d8003001000f6141140220341990601c104001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 623390044 1250 623388794 623388811
    0x2120103020a091505120703060e250b22030602070b01170d0e0d1e06051005010f0215040c12050f0d181a13060e0906010e030a150204031406 62
    0x102a40d0f0382208011035981c80a000500100715000384090b2514042c0c0c081003140c030b2011954115100e459280498041d00c10a0803640d0020407808100344068408900f002e481082403070009140c00c207914030601c24039000426207440c1e03510b801401000841c5820145822440840d01d502c1940b038003482d091001e0280924060542440d2010413200080362400400e213561295207110f0340405119800d4101001100c48c0032494102528100361000340440c0c03d8020f24001c102801c0800d000310322080f0f25002740741041000b0310404503580e00010140b1003900414102d103510398442c20711036500701e20760b0000d04264010b145aa0f05005000030382d8207001421030196842da405a01040d21500c1c444040c140d1500d521a900300880c24162203171040d904100080103207000341014900c04640c0560b00440085619450103541d64241151402e52200080c00c1c0071141c50702c00d40c002135a030a0407010050031500b005c0009451805150107840003198401d1045900a0b204055123840c0c280481d107000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 623391294 1250 623390044 623390059
    0x18090201022808030408090d030c1a1312020c0907030c030f05040f021903050a0b091e2a150301080625080c090a031202070b040b1213060212010302 65
    0x80341c2d6410b140d5054281203281c1201c20300d2419541c481054000030429108403805015084498480701f0034581e01c688607030346030701c0c07003c000b231504440103904500600c01c410102c0040020360110f6228005500c1c2c0c00c40c0c1d03002c2c0810a101d004038030303200310240c00350707003180c03c2c5003d00c00c00d190140c000c12880c0031140c50030700c01c0c801c101c03010408690045a025014480101c01c2c20098101651a0406038051000a29905032a40c039154508006a50102c5100d00300c1ca080002d0b24409200016134420346140d804804940003042c039641c0c510070108100071461039003a410501100d4215840c1ca100302812000c0c018465900c180301c0c030380003481201058005d80000800382c1d003401101400c80380c415003031441c0402d142c0e41304480d40c84000384410092081049030305a240c1e185140720000310310484030b06e45448a09071000341403940c1c2d9800074801d4902030105100300582c2105650b020031040304041c056581c4c01a5461007089012000f615451000070ba040d503007007030b00b8160f9041e28000c1e281da0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 623392544 1250 623391294 623391313
    0x111032a072103030b030a060614092401050a030e0f03070c0e0705041418130203070b09060318160810060510050a0804021f0c020f0405040308040b07091809020102 72
    0x80141c910b0044141a40d015082c182800007800f035802812000c0001c3e080701c03001c1c005581c6010480d181500513442100307242e04451510316054235542c0d4402c4540c10b070307000484100c0b0f001030750910f0760000030b90500401180e801d824074400e5102444840504085890710000240c00e2500c0e94030510080e2100d80707842c940803500c007003e03030340c0e081c0a0f981a036203d0f0718080c58440c50001444141810301d070312540941c3e02c2e0785107a0822004a02071240002c845200c900b41d40304061900c2200d901100e4041418091103d441e6070702070689a01003014404452000d00d442515420001e04203860149012491408500e541000401c4031042c0944481002441c1d02c5000b04211000710180c810002842000b0b407000940c031860909420a101614001a00d04514404441d0b07500c0040c1e8280041d600112a100f540783c00040e0300b60300601581d0404c50bd060035200100603610045c00681400701b80d6020400c0288545901801011502618084085c0203014000540b80105090380103200380700700d9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 623393794 1250 623392544 623392559
    0x17060a030f080c070902041d09061009050613090308040c0b040b0304030e0111120a0305100803040b070516032108010e0a090c0302030d02070f230111032a07 69
    0x2501e4100100890250380c41da41c0e50683d500240c010100c2c3d0080b1100001d60209a00161001d004c03090119070840d12001c0904000140007441c01100364000c006000100c6160084807064901601000c5030a643d410045090101690b0000c0262444c004d03c10003410751020545010701d1040c46c400040c20b42d541e075141060300481c000c0c18050002000071500103405040444d0080d041070606902c041c082c003503040e08281c10105100d48612000540c941c40c0c662610485074084a031041c0d0489442c10807240c1c0d0380d240264028035500f480001034110900c40100041140c1c643c4e072810b03580034591a0324010940310044540312410445440700c54080601851480341030b00c000100c190318030b98684040c8406400390040c01c0d240134050400c00302c05070f02c09005070030300000310303800424109291540b00c1c25442d02c01d50003003854040c401541040d0303032250300d003a0716084424a0b00d5941c2c22a04074420f070651081c0040140122148008890000c030721910750b000200484050720724190b0358112 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 623395044 1250 623393794 623393809
    0x7030c02100309020f010c0302010905100f0b0319030507080f0c213c130f2102090c04091a01020f0f0a020d030c050f0309101d0127061706 61
    0x1000717601c44005141020345512640e130401c1030601170300c00400d07038014035160302d420316040400d40110551a0784440008103002e001c8c0c00e8075503009800400b0500107000c111640390034102c000030200000050b800c000d000d0b5500c1901d1103000ca41110320750302c0307042e0035107143c2d240051541080e841090030303a942000d0f10290240c0c0e51040304100070f88103051068403c00c0c40c49880928004003a5982c90b030481c007903658031000d01b018044000c6000d001d142031a0000b48040c82550029681111280764128405800d0a0041d151541503880ca0190348882d1040140c0340142d40068001615055284030110006045214810000e07000d99484058036941317642c580c282000000201d501c00c5c5010700040c20078a41001143d80280780c18089101c907540d80e1410701c2c91800030141d896001280324aa03d10f0050046500c191090800440000c03049045415001404010505100c4003a155070031440076078010035102d003540340c540e04442c0d40b1000040e01104900b1002c00402d0b86000000b101806c0201 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 623396294 1250 623395044 623395061
    0x9210201021506060306040e030409020a0504090e0309030a060527060a0f2705030702040608070602190b07030903030902120d03050c0909041e06110c060f010b0f1b0307030c021003 79
    0x5012515543c1d4106c240300203401c9031038105600344010000010a034840380f014000d031469540d10a41d0321442c1140d8041601c00802c80940140c0040204456956001030f030040c1041c0d0190380450710b962400b02107180e140700c210388144001c1c0300e0741d014455401c0104507030380f00382d111400030055000c0c4003a01401311010000d00c403001c0c0030380c00c0c900c4000708035540009502c2d40c0304404503031034200380d80d01103010346103164401682c5a002250034000940c05100c000c01001c508201084035000b1611170411510010300340300181540e561900c014140709421030000c054018050180d007035024140540c4d00c13165041c50900192411003c103178082c85210442d8507110009111042c56202e03130322074480c9998003817182d41c2005103c40c270002c0002c2041c054202c003a001c1214140d01c84203d68080c1342480d800409a81c859218440140b0410101806982185884c0541c0e00e03154880140c0c20404c1c1d04034514103002c98030012411000f05070340030070746028141c03094602c240010300d48102078040e6000300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 623397544 1250 623396294 623396299
    0x1707140c010e0607170408010501050a060201020c0304060f0c1b0503250302150c060708060f010f080115021e0331030213090204050f060a140108010b0a09210201021506 74
    0x10150b035095281c004007515a0324005c4107078000c41c3d100030881940c0c1d9072040c1e110b05620394580e00104080d14001c1051070040c90346000075842d04801c5284a51248114000c2c0010301800480d031701d285511841e440852542d0252502d04400f0007600c6040c00c1d40c40c188915031003440384441d0428a9146101e1095031a0000c024201e071541c119820801c0302520259103110030301090002c02030003941000b11602507122512040c0590900d20180540d00b840480114148221402524022640b181045046812004c004401421610800c070b081500e8240080703031001401031a001c01c5540400201382044000c00c2044851104a52525003442d0b03080442d0740d41a1031000810150600ca05140a2418155030004010303916600007401c40d2002d07a56101c243c4541d00400c00142031a295640180c080186040700348442000004e112a005000d00356103060003040d070043e072a0040c1201c00c080c0484000c550038002d011075401d03403c3c62840ba8140d00601c6004070340900345041e0b40700b050240501 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 623398794 1250 623397544 623397557
    0x6150501051e030a09020a09140606030402030c150904151401030c021c170405030304020a0e0912160501050103080309060a0203100b0a09030203030d0b0f0a080c0910031707140c01 79
    0xb000b009840c02c1e040107203e40180703511a2481ea00603500c1402c2c68020300280c0500003031036103440380310018412000300041d0140404000b4003000d40d500040d0795220350812a0b450030281e0307080d14010390600806c20b0403074025090034445441c04109001440030348841d4a031002070040000f004400b55031681101102581011180718501d00000c103002c4035200d510300b4000410740f6907a800e146200380444050758550004024841107141c03c0c10000014940090b0715503a0341403100364152030340420143d07207c00001c001000c2025580a1442200540d00000208110340e505c0c104015a61300c100c0303001060f8003c50740000d0302d41c0030620a40e405a20121110f00d8141d06281e650040e65026a40d84000d108480c403000005a604200074231940320395a20200ba00080581809548106450801d114040340d40007408294000500c40d20070502c211248142c544407407201c070801c0c245941014045080410907001d081d0f281e100205400d511402011301c440b41c20000075501d0b034040300d443d01d000510 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 623400044 1250 623398794 623398837
    0x7110603061813021e10021b04022d0421170309010f0608030d06080703080d0b0613081507030b010804060e010b1c02010207080303010b04300615050105 67
    0x2160070540d41c04800000403c6485145800040d1540c4c282d4100348035903400701c02108060705080b20024000c1b032090004100206202c04e40b100c21038448403025000f1a13011881c00002031001049907070300c041100f04a18a40022520440c048d4420f024103451203001820302c8082ca000801d201d003203640c00c1082d614030340700401c503030380000c0c2c0c0080c000480c42e42d00c0c0e0042c604d0fa0561441294020030300400155a0750a240e0598400e54002e68071031071b0543c1120801304040b4008c1d000b2601031148081c0005000780c0e85400040311030281c1c4044203044424038201043c00200010303258941039100b0740e90306580e555150100c0070303618000c0e125400610700001040c00036025030841080e61140000101d001b040541c0410445821034003456502d60406102105550b0140800006440406c01440c039560409035102000e1181384038502d24441e2200f140d410314640c504110899035100103070380080241d642010009000c0d8100f104400110500780007500303600420848001c1c0030498881020040b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 623401294 1250 623400044 623400079
    0x3010509130506340503220804060206010f05060c1c02010204080d0801240801061103070609081c0c021b0d02060301080d0315060507290c0711060306 66
    0x580140070503000d000c08003080340001c2d03001e028903846901103d42c1d6030791003140503070100406000c41c2d41039100c0d1051000031011059002c004c40ea8020030f401c01c580d103107900410710154504c0c00001c010b40741e04404100800d0342d07a404561141216000590071300695110010030206101d00301740060725520455030062540600c4401c40200c8201c2d0000505055843c0c501d00e0038000103803030540000c0d02d9007005011542078aa000c50300000d00301c07100041c0c2d0800400c09001700006002d00e80034421008120f00403210100304860300140d011a06001c00505468584c405410026800c1515800803d021101c1400d038030940782d03c0a820f5000b0f10b01c14a404410103900c4041c1d1100c503030008440d001180258503034100850080200720018144115282001403c44003503089140841039000303420061181e014086d6040b468000383d42aa88440c0008141001e6030100d0721031381c50000d4038003003000710aa280040c050142c050a070045095003008100702c4548422240e66520070b42d400722094615 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 623402544 1250 623401294 623401309
    0x170c09100804030c0b070e09102702041d060f01020f06070507060204030804170f1204090507050c0703060c030e06011d06060c0604050703030e0d020d080306030309060423060f030105 80
    0x743c06820481d000c01926103600300030040845907400461080c1c4846203403420003013040c80c2c0c8021118048144c180c180300d40311017110034404584400d44240b0082c21582511a812074000b031424000a00070741c0500303884022006030480300700e40b11b8421175801c10704c1540081b0b40b881100610202402d510f42e80d590003610250040c00003541c0040e824000800000c80a00c02080584002c00c01109080c0c10400e289140c010100f0007956a82c1020302c0755104c4c2d10301c1d1010b5030165694510007280c550f03103840d01241c0500603955150ba8034810400d00109006603a8403000340901e05950601c0003d1401000ca03036150301c2032203168111010201a42c0161801194072500300900904940c0b5280c15005035519011080c3c800791400c4e00021420020590814451719030914150350b0740a0111040d00000d440f6411300c00c005d44032000000004030705a50074011079901080c000c00094681d45c0b5804202807030719801401a1014030054603528031460103070309a680d448000b40c00c1c580b07141c0c280741c00d00400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 623403794 1250 623402544 623402551
    0x130207030e01181a090f0d0b1302120607210b06042117120708041104091707290103120e2106040606091505120708030a170c091008 58
    0x140000c00501094513844400490314441c4413102c135540390354685080198241480303501ca40308003806500c90f400100740c0540d40d81d001c5241c11956003280c2a45c000b192500a1031440c13070300f140c0035520421414940010100400110b8605540c2c00d84201881c0001260b510001d4117078051800e000420242081c0e58001d2a42c102c0c1003108030781800e407542c8203010460354810b02c0b07110190204884a400d0582290704e03922070301ca8602001b40d410180c80300d50303000c400950300c2d500460319100071a05100f0420a01f043c0c0c1581c0301030055a490003800c10401015228a10038030018200c1d121020401040c61801d040c1c94024107240480380c5480c8060f20a44200f030016900001070036a0400540440c20842e1890b004100180c40a8601403a104049035401c0d080106101d103071181c5022800404100c08066400c10349460344c0040c84140c2c1145010b61a500c003149600c000200e48011961001c4c14410b181001d008201c03482c0c0f601c1500181c05d0241618864004032140e00c0007210780d2085020540 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 623405044 1250 623403794 623403827
    0x90302010905010b2d1f090315060303080c090f0a0b09361f0906080607090b03011401090810020a08011401020a080a0e0a1724270d0e130207030e01 65
    0x16860f401c420301c06c2503510500c100b0008100c2800d020000d10070300660000c940b108100b41001054110b5802030182e600151500c6030710f490104444038142c4404c2c1390409403550003045146440c0ea11200b140340381d8898400103000d528940e8100c00c602c0e000c0300d0400d0303000d403904210001c452084407040c0301d034030001000100c0300e4030f4036965414400c18445281e406491a040089019410104014504407000d40707007404011040d00d0811402140c039042c0c030b054402c5072403a407030340c2d001d6240100c40c0c0300d40e1500006064040c1003c3d4010681302c507801418880074a40310640c0d80d07030345d0700207100e0860b20316084680540c20580c8190002250b02008068940090421842030070360300010a1180f42240c1240f000d000b4400410848a901003142b00b0302042c0007140041451040b40c0c140b600a880680721300c4207140c01141100340d6000000790050100340040403145103000310394000782054040440540140140107410103041458000c40d00d11640585509856101030001100c0580c5403414905 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 623406294 1250 623405044 623405059
    0x18070e0102190f061d0d1110151e181508030705071a0a0516060209130f1a1e01090f06050c0c0a0e01030f060f090302010905010b2d 58
    0x300252561512810b0140c040c0318044a42d11162514004a805000e414544040c1ca080c0001c030403680000e454020075030340d2410303c0e503000ca42583c03680344c0007540c0710902e40075060070000032098122007441812102d500c0c0701a0342c000e502c032010520040f01401003a00010015001c403800402e0307508001000344025620b06e4400d80e03a4090700703003103400c803480440d22504452800c000034401c2c0c096080320011100303070a600c1c0c0b92000c0c40181c5107204083c1d00c520040402c010010501203542e0640c1c440503001341c0030700440e611000c0561300814001c041b500030b086c0b40004003203c282510860404200010b452800d0399245404204c84020401e10002d04002d00400081180403c0e00c103490028030003a110705460f460741207105401c0c04002c1a40a00882c2c118a04100c021281c508050441c4c0e001075101c4040d10150820601601c1750340d00c4031410303605006c990300030141e0540c40200703a98081c0b0020054604003404000e941099140c0c202c10010155043c000b1000c6800e02c4001c0d03000b0003d1081 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 623407544 1250 623406294 623406313
    0x60a0305060a090905100614210f0106150f0507151503140d140c0d080c0c0703110103230a0c05090901290c06070518030601091a18070e0102 62
    0x74001c4c1e400c2d1540803100c640003590000d1080b4114001c20029000740c00400c00180e107810302007403501d003615180101c210010070203071580810a0291134038400c0c01c0402481810744400100320b80c0400814094001040102d2004a2a1190084e22401503001d120b041e440701c141e254000280840c40e501c0f00c2408044c000001c00510148000e107100c0d580d2401415a46088030005456940d5203080c58603c98010843c024a02030b012485100300285814120f000f034559185151090040320600921441480000b209000600111412a0000340e0702806041820240d07034066014104a410b007110300c1d48082808500e030380d001010318040b640352860500b0000710005041d032200fa404000c0e0480d021a8400e181c000300d0b004260590450742e08545040310303403940b040da1954000d000c4002c2200200d9a054010001c45501c03450f11030050499a49507118001c460042600540c45030389040d440d811180d143c1003c0c13140d50b01070804da03c20601c082c0e48652003650b52400c0355110904501418081 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 623408794 1250 623407544 623407559
    0x40e031c0608011a1503070c15050f0901020a02151905010b1b0f0303013506070e01030b03120307030216080301030b07030b030c131e0f0b0a0302060a0305060a 70
    0x310a511010100414a545072070101c40c211100d0704c0319020200607201192400740c4454512190191012503450303503035030300c910003219180121310b00203016451201c50750040103256000386005034041c0421100d03903158a80032500300e1149a00040141e000a4402030620483c400030075408595a10514800380b9002138540896909800510100350040b924403628541086104500c0e03030076500030a90070b8040c0402907039038001440380007240b40d2105000ca1680c0e07103010004c0c035400c100c40c0c042d072044600610b075682c5a43c022034108000a442c54040340440d813003030084c4078109901401808516108110303040c0150320042941c402d01d074080007070200c60412003042d012000d00400c0c0c3c0076182c1d411741c07400b4010f121014110200f050300748490070f1650364001c41d5006030641c08580300040c0300b01c1c0c0c10b10340008c8c000c03080b103201da06a007102614502c01303400c1d041030101111000081000401d0041000701704002d07404040d41040c001d0000c640d0660017540083d822900040c001041c16503502034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 623410044 1250 623408794 623408827
    0x2041d0d0f1101060b12130218060409060c0206041101230904150611010c050301050918120a020c0a09051509070903021003060302010e0904050d1808011404051b0f040e03 75
    0x1504400c44002400d081b09120064100d410031900d141c400c01e06401078002800c41000780d01d0b0a000084a9004621a40c2c1c0b1980080000780d80942c0c00d000e07940050b400a51117140417a0141c6084e40124a41c42c072662140300500300418081520704682100e0152000e4580c000d03440182d00942c0c0c0746140005803001c15039460080810360b5900e041c50780d5800c0c180c0d0a607103e1200034810720409000521041e0f031800b003416408030b0010050303840f06c10342b141030710302c0c00340c43e030007210080ba10009403204e40c03a0f030215260054240580d00000c18503680d440600469004a42d941145404a408070b0200c0c030b8501c03078160f0003901510303190011541302c1c1c00252685111100410110ba44c500c5c0401c00c65821440711020200c0403100b42c0c200d49010340302c107602c0302070a001a00803c0f130b1141040419030000203e01d000b4000d07480003001207815100031284002010b0b2010381d51b52040c08980d02803400e2902d4070620030000504090740c034078004010300010b0310782ca401c0309c11140428400101c1c40481d62a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 623411294 1250 623410044 623410049
    0x5070f030c0812040b040909080d0501030809150f0301270c02010b1f0801030b0a090b090109050114090706080a091a060f03010b0306060d021c0602030402041d0d0f110106 75
    0x80100c01c0700c0c54010308919149000e1603d07140c034901840b08020442401042e2002c8941610300410380c1c0300581ba02c80d101c0d00c10340a0201d8520f180600120a10030791f0406890450b1003039800440c00c444680c3c0c0418036001e03c0d0351840d445181000148800d8004145515401c90a44020940941040020f070151810b070354035040141e41d0750340d40f101180b034034641013205070603d0a01845c00c008510b000420300103050001500e1800110007080c0080f989038452051141c10050751013090600800785030180c85440d4040d00d2540c20845181242000420094000d001d0309008064080c9408015210100005e0101c0303006540e644001010840480000303043d01d005081c00f0740949045000c000c210f02814016a01982c50611801c02d55180001c2003904140c0c2203490072401100d130700c0041d80803850341c0040301d421010704000c801040300c903401940c0124401c54003403100d00403805d211a00c0c0b080400141c3e102e68090710000c126140118000b0012114914203101c41449907030f40f603400d503012607 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 623412544 1250 623411294 623411303
    0x13020f12120a08040303061409180c060a1d0f0d03140f0a020f061b04060513050d0b01030b0f0f04080304050c1f031b09150c05120c0c0f091305070f03 66
    0xb01c10001095814814203002d00403844008d914424001c005c640c40c1c2000408580c807920301c0f10400d242c2507108100440c1c0360b140060803582d582105400040c225aa180c8207044001002c08281500d8500728104c010140001b03012464070301c810f518100d078289040c070140070400c0301c10420010088420300003020060115001400d43e6603051034a03d1500d800144400a0346003e000400d00c4035000c2c0c0d00b21400c41e1040d04c1c200c2d071034401030f0100d00340c41041d036402a648000320202c1c01040018a0721414102d80c010200300c2e9250340c840441f203d80400407100b014101c035041000070001b614000c09990818050822140008044408a1030004221554610b0700e4640b402c1149099498000d601c02c0d04d040200111151403401006440c0403042d000707424a802445900220603803044500981031500581144c1d030040d00e1021502c099400a03162004500400314258114104117500c02e040d01d10280042d2034656810802c0700685008036400c548601405000050032501c42803500d0186019 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 623413794 1250 623412544 623412557
    0x1e060114280e0403080708090706030b06091207080607020a03022d010c110c01051602101106070c0c0501030209090a11040f03140712170a0509041d0613020f12120a 72
    0x504010709540f000806e16420405c0381820040800710104425084034600e08010070200701800002d41907000d41240240c0080c1d1b2600b409800040025003001150603520907120790703446403203003280c641e608001e01a015a0001540501e03c0c212034076078802c0440011741e84040402903d52450035190700803948800518100d500102c181c209012103c050442428464541000d10500710b420707005a4001910032103d07000314004050154108502c0b01032500182c62462401941c00b524950000c81c0c1a40d500a01c424046000d50080c801c0340c40c5a80010441c1559039100090f10018021020078a808404148000580000c1040d01480594411540941c6600c02007030b869207051010f03480301c40c103000300c850944e0100307203402001c201c00140302c046255500070724002500c85219008000703822525040c1080c0103030895415521407004008180d4510752203444140d8003042e24502c1c0a5884440301c0500005403a01c440010ba406040034142d400503034100d41080090b8010b45103000100700c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 623415044 1250 623413794 623413801
    0x10080d020d020d0c11040f0b0d0f0c050105030126030903030a17090303010e01030f2d0c081b0409020406050d080c0d08041e06060b03091e060114280e 66
    0x805010f02c0c0ca01c0310302460a410384000d242c035070145150760040c41600031940c8030f2558080b4032042e00080700348080940354183c189880e1901000701050120140c800001030798000c20203601c0342d41168101d84480407451028178000e080c1e540e41c00481d8880e201c0b64481003009544c0c40d20144041d05185409461711032030540800a211080c240041c400465078004100501460b044d00400da410350f50482c144040300041485d18410700344082e42801c24429450311140e090700998004944030600c140b00f000041982c8114550303581c0000700500e805601004000c00090810798411400c4500061011031150340d11000300720211f0040d00183d8a1602c00a86107460031000c0040030320040702840d0205403880c00e0b481d8030301c403400c007280750300d90203240c0c0044141849250b0b01305a01406031008130581e80c0c03d08054030b5607074200a0442440246c09103503c2c0141e107202040d0a8129403290311020321898038501000003010007074400d854a0039801d40c0c036400d60044c4c000340b04003908040c0709060403400c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 623416294 1250 623415044 623415047
    0x100f0c0c090f1b0f050d0b04020d061431020d020a030606090b0906070f0f14060a0b0a080303010510200d080c0702150c01020913050421140310080d020d 67
    0x5584040034055002c1040740b20140951004c55110040c00c5464003035101c0c1086040040a090703090920380d8480e00126040d0540c28940d4804011141070540000f490042070080c4081069048001c084841c0e601401c181c01c560703500f800c01501907404000610f0710741650148012a0468500040020303600d000c140711094004c0d91502c0503040c0d420265082004081c0028564450030800034550b1203000c5950302045000b00456140707960000420744124012101250380f544100c988a0b420b41c201b2a41485508005403000103030307608640a180f56130309000c24030400e6030303040d4030032020800322225001010b40c80b035840710541c40d1010701070070318080c0e07940703004003030030405000c1762403e42042002c45c0044c0d0b19005600032500d26403c08c0c507114220700c10003a00901900b0751b0382e60000c0303210234042c682110f270340c0c002c52103540328501d2007014440c0c0a50000c12110142103032030201c4e4402d4030a0024050300009164130580700c0300c0c500c2c00e240d15075813054241202c0305070010250b0b100c031040143e150b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 623417544 1250 623416294 623416301
    0x220f0e151005122a0301050f0619080304121109101d070e100525140c0607060905120a02011b08060a0b07110a03120806010c02100f0c0c090f 62
    0x1c041c120750f0010807140c10039140d03131101c0701c04a150100c5488001d80001c1c0031405040c600c00e07800300800810043c904018000100d6004403100391003400c1d0220252020074901090b20143d444820085040c41c1c01c2150060040518840540d0880340410404800d40c0c1d545900034426000342194409852401100407a4044e0100c40304035000c005c4800c00c201303164010700c2181455400c4500041d195900c40007503403207101d4800e0080d440c6503c1805000f10902c004080c1c18858842c40d204981103428500b09600c45000544050b8010300c200b0149012806070340054180c64003d00070b07117200342c08506002019038011101800941d454401e0014800040d0000c000054194148100c15150074400a00010228003c0310703541ea00c0030030b0361814003412400c0c40c1a8004081d05c1042002d46074100320402d059913010741c000007611100007860ba035100300500050180d01500050088001c00300603212201c441d807004003001180440c0300c022540c0c0001020060221f09000100c000720700c1c041d001034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 623418794 1250 623417544 623417549
    0x2040b12060109060e10140a0306060e0406030b07080a060b1b0d0e01050306040e12030109150f1a070f0b04111005040503122203060b0f220f0e1510 65
    0x40c021114030030001290051025102e40101b1170307005140c007402c543c09403240060f200540d400020045546000c56400d54001d0f03041e950305031101d4043e07500701c0d000c00098a0f070500001b0610000712011450f41401100a1a0041c480c482c001c91466215814250160001c0b520041640d51101c140b209040b020b0004030060411883c14a400c1c03100c1c440003034900d2002500090203150f0300c1800142500d002c3c08442c81d00d050483c11a80e4070b5035680099400352460032b00038191980c0203000041e0680c004204c40017100d444003940e00070f4a40403a1900959080340c102602c024900685100c00510741b0101070348240c0c414261a0b00307040800c0c2c24402c654010104e041e0900104000502441d170380020100c03016801f034000180d55080901d04440365108810307517000700800c626000700410649400100c1540b50958800f002d00d090781040000c20342e9807240c100c8903039540d07100004100542c0c2c0c10610359401065004034081d0306c1c50b07280d68a4021034882c40844201170300b02748030041c120003c04200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 623420044 1250 623418794 623418797
    0x90c01121401050f120604080a110712030c06060902030a090512040e0f040516060201091a0402130b0a0b07080301050307051008010603052a09030d030e0309010e0f0402040b120601 79
    0x9041d524a560501181041c040c40307100d8150184002800e903035925000d5940801c20381607441509081c81c0c02207054002c00311282c04500108040b82d4260000900a800c46020702c1c9656080082602c055840d25250041541d4998440300f000c1260442400198081c3c0807203000001c20454034107246040200022442c48452410041081420b0140c10002e4101c03000c48080c00c084d03100c51504038900750b10b5212404c89080c422500180898065221050042c05007034bc1007100c1992034280c1c0b8040030204e80095111168454000381e4131255070101c1000701c030141030344982e00e45805000ea041d070022101101c01400000060129080030321810000b00810b44005039919008039005e060710306c2c14010001050341e00e80014144a07490000990b010140c041743c130803000601e00a583c2c15621220390b05010748602c4903407846061091050160300e5003480042c42c201524040110b8101070300601081d40100042441c0303401c1d960300d10082008141c9484110781e147d40441a80c04120710007001c3d80d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 623421294 1250 623420044 623420051
    0x30702011a010f1833090302090a0c020114090c040e070506040515040504020d141e011703250312060e0f04050f010501030c05010e032a18090c0112 65
    0x6074982d0700804084118106810115042100c0c02c001440080c8181e202c0d00c81c0100140000c00000d00601014115640c00d208600103026403040940d841c41c103510009400403424000120240740030307488a0304010091002250800820315044058282900d00ea40342c0c0e00001e64a6a86280074400e601081d01d204000d403030864903080028000313009910440780030380f51031148a2000b0314584c0484010301801001151143d03400c454040007094a0003000904c1040f11001c1003112206140003508003484408a101c10380c04c05101401e4080f5802c610b000621050050503e1820680c80700d0b4980741c0c1e02900f024200e21142001090034003800381d00110720745840424002841c400b00003540c0001980c1c113030381e03082c0c90360301c0c1c158607092480c09201c0b03065103404004010481d00c1480780080b218260380300e4800c8000b4600b015101c040058a904900100212000c2e448000740000707285240300420701c030000c0100d50f881c044c2c0490b00303d071690f4180d001071050f850950b0700130f00303243d090111040c000c2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 623422544 1250 623421294 623421341
    0x10080d0801050303030604110d0203070c1419080a031808120105091e100504050a0603121b0b060604120b09060c041d0604110406080a050708040c12031202030c03070201 74
    0x13520b0740702c05030485000303d45868100041c1400c11040700e1280341f44841c119031307070f2611600081c541200301c0d404440150030310081e24454000000c015600c2103040c44c480b10385103d0766641501c260b0000c800c2c0014941c4406038011402c201103070b1450018040d074a031580da801f07101e550500301c0405030405031140c4248c03414400300c0c86080c583c0d8454000303400309410a44d25207040100400580c1d600056000741800c1c100503c00da0f02c2c0e004081228480d080407910f0a00604042d201c04518021030b494510641321107130042404440c0c0590401c42c060512407419480302c7c40140340701540801a40c010230100c0500603400020400a80c0c040d0300e606041d401c0c1810400207501000200034824080d203010400720762256102e512041d009212041600d0359165550000303049071204507403110469103000c000404d000d0184000d07078425540410706081c41810700b4048400701a140809034100301494114900c3c0b00c2d02c034030045000d00c0c95190005d0b100d203003c010003070941c1c0001144c84811001084507 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 623423794 1250 623422544 623422549
    0x5090604120315120203120a1d04061a0c1203040f0305031902160b1003050c06030c090a1202032103070c0201020a0f06140a020a1e05090910080d080105 67
    0x4803a00694851600c0050549100c4120042d002016a41081c070740d202030005180440e4100321040307140f0a03820b0321349a00d10081a130b0b0140c040e00400b10302141c90070000081c014400386648030031082c0100006000c644880c090559510305000e0b090300c1d1007001480c0c15000d1001c00c407107001350181c01842880c510300781d0307180c03840c8108843d0010140500400418003c00c402840008051000c40c421900e0700a801502e2049058000064070004d1a0300049210030200c40440d2003075a400000800c0c100c80c0810902549500042010701000c2c001c0c4a170a14694640c6800c1004010b210f5410440d03207c0b82c010075040c500902d41d1241c90540036201d650001403050306030307030384241d8a080031106000680010303800c10300030b000b004001e845400c80801c2004025400802001d010044102c0f1030354807105503034100d00c21580040b000c43d80c11410154001d684040b00100340c5c40501d8910304003030404011400c03052050b1514040c0341c041000038005044200075008680f4018a048141035141c03401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 623425044 1250 623423794 623423803
    0x70c020607030c0b0718060806060909130602270402030708070e010e040504060501150203070f20041b181211031f021306030e030a1206080a051f0509 66
    0x100034058200456041d05041c02010160709054004140400e1490407803001003820411901282d4003521218011030818401c50599105800c050800c40c0b815540800704040035100078101c4515030008008035000840b140040c046481155005c050441003801d041100c1003041c0c4041402248140308015041b580100c01a0b040081410704150107120b400040b18408000c00035903401c917007480180020012142e01c81e9040b1a18003039941044c8030a02412a22480b0340107014040d05e2000100f8804207110810100b0710303526104d0206541040c0201260030740303008400741c88407500c0b078001080b090390300244003484211030490411166400c2c041300c200843c094100c0600b412866202c003180b0740d00c2c1000905001a44c0014000c038620713003001c1c5d0001a60103c0310410f131040c40c806000072034074000d00034035400d465640b002d941000c1d034136001100d0700f400080c9003603186600c0d0710000a541c0c1e01804500511405100649030210152980c20014054460088089442c110401c20141804074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 623426294 1250 623425044 623425067
    0x302010b1507020f0105190c02191d1f0909060605041b0806030a060e0615030615010309030903080d1a0904020913080705060c030612010b01093b060310020307 70
    0x8a001c4d82e004180d20049541d0f0140d5000c07000c06100c10a110320115401c41291003070f25100301e4801c4a0a89071461140c140e1000703101d2183c1c0d090074503c8a9981c00501c5084aa2010b502d0f411414132401007111800000c00691000244941c3c81e0580c10a0004a00505001c0c01050310280820381070f4048a8600921301c0c101101005aa45c0c046503495a0501075002c07440c0c3c00c520203016094041f240c1c96240c040a6408294442c07420743c0801c1d50b8240031841601c1401c40610300c2d0708001e0448010342c003506120030218100440400044002010000589108003113200d0000b0218121400d621101054101c0c96206101400401c07005a03980c03100d0a61142d99500c100c1840038451070b02d503240b40900304c001001402a0800c2128403484d00002c1e620500d42166a418405140b10045007200c0362a070846001448181042c00b02005401d10543c50340c59400d5402005801c02c01310810241003910864008902c007001c1c4000c620f400c015011030070111070310451440c1003032580038024a2446 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 623427544 1250 623426294 623426299
    0x10905120c011409030c070602010c0503070309080c07090b13270c030c180c05070c050907051314150c0601030f08160b0703050a062d15020102070302010b150702 71
    0x3034041c96140082d0400300c0009203003400881e030707400c007051910788a810034115402d040c40343e0f0030f001a10910500401c20720300d805444003851503c075040e040740540104201611000e0707042051003000c00003001000010241c0810009600c021002005055202e0712b0a6402c00303414003d03c5a208224541c1c2e60110300d0074542441d0a104030b07480e0001c0900429030000d041066800701c00034000c0b00701fa48802101555203820030040307004090503907050080c400e014040a50020040c000c2d400e00024298110189051241c280200c40e907aa00c07022049800c0502510700d100440e80e614101641c05146800089480f6030621a000c880113903107940510002e82100c0242180a081c4107041c0102d030103443c1040480d9040d01c4850410082c13040c0c3c00c0e00c05c1070000385450009268580184101000c0c1d0311214450120012812003449005040c0c0d800c01a42110700a000102d00e526009101421440750700003684801d01c9040180c2152894910140900120601c0c51242424401201e0780705504 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 623428794 1250 623427544 623427547
    0x4052b1d0102010e0a120306120b0f0411060a0e0a090203040305160c030210051b0303131103010b0424091a01030f1103012d14010f030b1801080c0301090512 69
    0x26500102d0250021824800f220300404040e5814081109664a00011b49440921420741e5800079041c104201090140c003100c4090042054040c0300c580309908140101d1052864004039000590503900034030b80d074004070750341d034070b07501c1d840d00f81003d1603001061401c4007103087d450325072000360491046206038240c0e210408103003c2000900710311540515000f40c01131034540103a080c060100d0707000205a00481140d6400140354080000483e403080907103c8480347ca84490340d446000c904548840d43d07a06540b1254030040c00e845030710071030004248800160304410303410340040442c0d01c01e0707420401c11142802840101e4070381403c1441c1d880c850038078001511109182078800100000c14014038440d030008000030711901c801c040802403a006444000c4880e0035945400c0ac0e04c1050700c00c00415101d02ca281c1b0090358025144c02801842c01d04002c140503010400161901003104840481c0d8807214005024194040007c42400c1b10154020061401980c4803582c1d02d01c4c0351600c0c0c0e04500f40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 623430044 1250 623428794 623428847
    0xb122b0903020108040305040801060308280e0f0109120c0e07020c0d020d1a070518011704020405061c03021b01110c091b0f0702090c0f07020f011704052b 68
    0x1088040308c0c0100400b0000700811900c0e407030080c04642c0300c83d001b05400d41000700e0205015511550030003c413070007078880c00000844c1c10305000c41145a41c840038103000c540080014010140c1c90f00003901031049a400403034505100381c4010b5400d01a00780c00442d40100000062030b02c0b212000c0d0b41030368044980c205240050300e0f100c102d0300c55a141c0d440c00403409c9800d100a02d60000051b24140c9038102c06c40d282c002020b001120140d1408038118000c028070800320b070260601d0340c00700e50400006401da41410300a05040c40040d01c0010040380107a1004182259607888440720007104802464080b13995480000510b44d501495198980b00d448440c000c06c51036554408940300354404280500c2c0c03100015070214105170440780c8107034002c810307850000b80c0c2513001504540740311458680c0c180c1081101d4080c0314481b400000124103002182041c0a0010349400403070f4070441c441c0f070040c1001189180804500a0340b0200d1075904001400518a40c0350461320390051a56080c000031002c60 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 623431294 1250 623430044 623430047
    0x10b030f060d060f02070b0601020607140d1802030d020a0c050907020d08150d0506040b0702011404080708040308041202040c03051302010c1a07050301081504021806040b122b09030201080403 84
    0x4070310740f440702400d1700c006014810002a4484c107031140200360251b81450380d51900c161203c0500d4070011034401e10410051240d00150790001d03041c1c001c00c6003200003001e0039501103442c4c84010080c0c040940e100d2802e0780b0410800c0c0030307200c018040950b445079071414001e102a6440451000000500264900042d201b049950005403100801000650610503506100c2c0d11180d060350255203404031074002030f074014014040c0c40f034600800060380301203644035250500c1540000e0800ca1341541e0411002000c541032030003400280846d003a4030031003c001d920400003241c14602640c01414104800c03c030401b14030100121320340c0d4081c2080007080401c1d2801d01c48002084040842c8403283c442032080340d0b58010040c6059890341c004075010001e06518000f1011801c43e4029400b110281d0a05000700d01c0702c1d0400d0b0800009400800c418028800241081003414814100d543c049502007003040450348400440c95846591a01c0701e0000010041200c80a0301000e410b02c90701e070300803500b0103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 623432544 1250 623431294 623431301
    0x10606031503060c03200d0e0105042102120f0c1501140d1b03030e100206040203033007020c010210230403020a050303090304030201090b09010921060f020a08010b030f060d06 77
    0x81500344000d880221030211060706c140c1228a500f08914945440050481c8051007154000c0c3d41000004442842040c5024075404000d0b0000f81180038540e580d0485801c90005800c4074013140f10103540b201041260385207403110b14061200f040d0103990040052408c80080344003110001d070780b20b40b100d5903103040060b244c0d43c4110101c01000e40320100081410790062400100b96812565101c092469810490f42c0d07a0066901a5141d001003202070008486044400780d42c0398119076507079144500495140000000311070300360168020704488810ba42c0c3c10311101790314001c615401c1140c2041014210a000e03c02525110a000300e8800b003000d240c0208613500b511548601101d03940c0ca04845030648030380252008034049185080c000c910403009405682c0b0009041e0746100c2c26510f0150080040d8a010014850311030510140303401150160140640b1180d000c44050b0f03030b8142c4801d0003002030005a0010601400903c01d0040e0007400381c00b042d400070b03800c85042848942508028005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 623433794 1250 623432544 623432561
    0xc2803020f030f01030b09070e0a0f0e0a03020f061f14010e090c1e12042d0303020304110109030c0e07090906030b06180c0417030f0f0408010606031503060c03 70
    0x3498004401c00091503411a041d6042c0c0b4406c042ca040d2a0f1965511140d8403007480c080e42c2c100a880400007601c0c080c159109006061b40c041001c07403041d00a55465040c200203040c1640181c02c102c9207103440700d4040020503049a000307070f422164401c0003803849040d01014018106101c0c00444500c2c010b0f881040d8200c0242e40080007040300d0304140300b500c80d80303511014648150f044003101d07010601c00030303105899041107120004961691030703035503a02c0c440d004840450b03000001d03088280da011800c42148a070302442503c1c0140e583c00e06050405840c0f4501c556241000b00c0d02c0e00500010b07100107281411252501010200c64070b40020a90300240c240c0c0000f00c0702450090300100b030207142c810550099100b51a1000c4103045003039a11107040c0112480c05c640941040100700c0303184600303c0343e0009013042054900307000190500c0c1e0304542c062016544c08440c0864284003001c0b0070300c640310003040241800c03c182c080d4800c891481f40014480500750341ea4a02e02542c802c0c1c0070790010040d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 623435044 1250 623433794 623433817
    0x609080301080d020d05040605090f030a060c0e012003070b071403390301120606031b05120a021f02190606061b050715052101030b0c280302 62
    0x200c035030310340703035082da039040721456000051142c103401a1400e4010411601078400c0c9a84041c58210010f061100151600492940501c15a080c030408558103116500c188072513640ca01c134410303e40c1e1000502400d800720050100302c0c600d150742e100302e00000003140c669a5102465030f52683e90308000392000441820407600d5884004200f10741d40c0411560100e48105c100e2450a00c4801125615008112242e180d4142c143c10801408440140890b1100300d0b4466400801c0c0680c1701d940d0781d65045041080000c43d8801c020040c80301e403400d81005815070b03d000c001400c0d8a803031500024100030041c0f0441c84c1105801d4510381c2c02238400c0c400c0340c4060a0580ba5030900d15440d2410f0320003000340b440388500040507940079450900801b8920320401341c004000b055880c2c1442e552201c90300158400a09102e010458506c00d0780800145071014000c00d50842c0c040d40c0366007814004004003c025121004080091101c081d105000003201041465109040e076182c400c002c0c0c000741302c0d9280008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 623436294 1250 623435044 623435047
    0x70e0106030b0310050c031905280b030102041412030304050a112106040c0f050f1c140307050d0c0b1f09090503031803070816060617031b0c030d0507060908 69
    0x242c081c5c6c5500110302440da1203c40390107035007041c04000100d8a00fa0740050030300c0e0500050f50441c9528254008400030100e800040c8815000d00017801ca0781701b5400f64081c0180e100c0c0880840c580440e000b04c04800041c003651a600d49981d8094840c000c0d80e10042118040c80c00700501500c079035181605c1e00c0040c83c50a0190030030f030410300d070b940c8600f00c0703045801240c040000300d00c01d107403c20314104544020300340c0d0034100e181500700300805400160200020b0482c00301440400c0c40211030f98807200c1e04030051561403e007403c2080c01e04075181c118406200e072581664000031050040f45500c41541d420703840750311058030390b44420480d1541c05501550b041004c5c15040c410084015400750b00255080007200d20700380c400e00c2d184c1c01000c1c4054144401030003540c000314210109072881074410304000030318540340e01400a007200c0d60b160341000c0e43d10200f400183c020075013034145405110040104031488190300080d076910710803098201001408030380e05080107907680202c1d2403140e0150505 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 623437544 1250 623436294 623436301
    0x213090c0c06051810020d020909070c05101103010b0306150c0d1b051c0210061403010b0a05060f090609130e0d110601140d0611130503070e0106030b031005 69
    0x1081c80700d0141d019200c0341c0c03812000c00c8020000404030803a82c0c0d0441d02a100240042c4040c8009410030381111005076002c0021520a5030b403500080d1044426880c2c840c400b5035142440f900e0700305a81d5545041c2460414510606480c00c41560b044078191840c1e25603039070745c410108041e048c0e044002180401d011600011409010580d410909100e6541c4001610a82a81d4204203d0440064000e03001400b06581540708801d0f8084110340a00443c1c0700d0404110301b503022100d141d4080480f00030310b5200401240350038051440c2d800d40840354520340134200b1000401501c541035881a44410000d040700307064460000b9912401700c014500310207280c00318001c00281000c0d2640580313a00513001c140180750f000c1c8414030f2406040030014091603082c0300c501c0706145004095141d110303004003600f40c0000c510340030f001c102d5050782042c0ea40300c600240d8512240300150700314520941185409012400c0794101050440e0810f10700441e00360b6404000c01d0800803543d03002e0110074100800c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 623438794 1250 623437544 623437547
    0xb031302010c051b040b09010e040305160503040b0304110904021008070c06050c0403050606120309010c0309120c09050105180f0c0403080a09140d02180604061d04020f01110a03030213090c 83
    0x132809004080e1018811201002e00304810701809000c0c203000f0000c01d80208000c41e03c101c0140203901c04c40040303002e04c84034546440d8610381055100c4403020400004000030000301810b1946085400e80e90940107007080d0380090103210004407464100088e03400042c00c0e592180340301d84843c58001000304040c6c00c210f6442e407001e13481303400240d40c2882103001250702ca0030004074200303c0713030a1040030310300740801341004403401600c5002c180c00f00300090b04089100040c0c091703164100707480340410550803494040e0004c10f03240f05a0200c1c3c440c282d141035514107440102ca0455025407000c00e01e0105a43d0500e00c0e0545003d20380010781005008030366034081603041219241a10304105008502c17001d203404000c0341c00e01401c4000d401035100c4d4003594400024010464010341c00903c00300d41540c580c1d03801c13955103201d4071049109010100a110940c00c00340701e80444040c007840d207844803042d00340d40180d46e65202c00c00241015400102080700d404000d0004003e01883d60f018001c42981a50 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 623440044 1250 623438794 623438833
    0x3070f1e0201151a0f0703050f0d140f131e21023a0c02030607030b0a080a0b19060312051b070501200f1c0909060b031302010c05 57
    0x700e1002c600020f060218064511682d00d02c001c80c1d001280380c0c60328820000c0310b04560000070302241400401d2102c03170824a18040500248600032000291741c0d1700e44024000588030190408035080f00d248180b004500c01c0442d8003509940018074030b0344020f80d10b040d602008500131030140c80d203208401862041480d91882c44202c001c15801c03144690300b015081d80440c04514a1140f9181240d1842140d81c40c4070050350b51004a10305004038140038940221781401c00458202000a640b00441d2865140c80040302d400b03488482d008000ca0b401c655541000c400d8046c01010303454002114070890902d054008030b01940d0300a1483d410050a440c0107029504418944000620101c04029140382c1c0092003400710385050391102449080c2c0101e0301111031551623448614082c100a40481d4041000449188982411800c0420b06040001400e1540c9500314240182c1000030420100a03c041500e4029003040c0c0c03102d5041d6050b10050b01c21201001d001005409541400310484240c0a03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 623441294 1250 623440044 623440061
    0x300a050406021006080d031a1e040c0c0b22170d06050607020a18020f120717042d12030b03160308030109150b0f030403090f05030303070f1e0201 64
    0x20200c0d04619a568606000c0e40c215005448050384890400c0c030601f031082e00686078011850580d11001502c02c0c02003040c02e03030401e54034101041251280c4055040603c01c102044059281c400414041680c0302c0e13000f4007001c4c1c44401d4403210407004501c1e03984801d0200001550000c1e00c1e03a251f0002c4888508030303800902c03904032403529010000616041c500b0440d10401d81c0141300320251401c1c4410f0701f0380d40402c2d1000c013801036801d02440e40220081d2006000d02540789101c1021450501030042c2046205c0c0100c6040c10446802e03c00015082420510030400310304101c41c21030003101c40f6403c031045001e405060814143c071010145505079004400842058041e14010b607022220802c2c0b1040c6480020041901040100428003156025070381c0d040c03010b115803c40550310744100144d900b02034031052030290004140410560044807a10080ca8162520a5110324182c0000c2c1c480c000145118240000c0825040059220340b040122001920603420186180c0131720080c000c01c103d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 623442544 1250 623441294 623441297
    0x1509050f0609060715020c070e190e030f0c010b04050f07080906070e01080603120a020313080601030f12020705040501080703060e03040b1e04050d1401140702300a050406 75
    0x240d85400d15040003030898041c0b04025041c04d28000580c0e41d00d80244100c0941c00351026424402d806810b6070a10000004010741e00c0041c0d120704120100b003006000204210358034a281c000c0f00c113000640032040e01c2c81013801084540d02c175002c00e54454050203110a07500d40c020b18000c2008050061142242e014000541c1c03075000702d40e14610a5a13880000350340040202d04201c5451905600c1a00b41982c005000380c2a150354120003101c50525030080100c520258001241034030105c585030311004002d00c07040d001014103500d9507c0c0c0c1d40d0710004424014140000b0b00030150250b9008108200090001620402c504d69442c144182c860015000890301c241c1006004900488004152000d0381e1084290924014100811142c4222111070b00d0b080c08800f400001055030711606580c010a00400031190001d00c4c80440c0d03400c5031014000c061801000c003040c400f50b2640001c0040142c48030307600e501500c0c4002074295054041042003803a5200c00046c11014080e4020003800840e12a03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 623443794 1250 623442544 623442559
    0x30b1f061d130219020d02100e070902040924050a06050706020c0706020616050757060338060301090902120609031207111912030209010522150905 65
    0x4c81004a0b2540c0321003c00500503440041ca60322216081d83c40f51230314071811000c40d084c4c0c0e80d407000800140d8015a201004640c4e459148003000d28425400c481c5000b003681d807400b404c90074600007540041da03900a5000304900880c42c0400c00104c0d504441c0c401c6920b8049a0180d5a1890000d5403507504840041007a001510580c0405000d082941c0150b684800c944201e0f40fa4803030703e18234019800c1040390a0701c500160b5001c1e88440542420800c0312110280c010035180480b07442d1080d01a64001c800709807505411049814441c2c4240100301e03580301c0c0c0305001c03068105e031488040844070b03441503010342c0000002442c40750300da01019150b84241c817070f0149101c201c0f030301ea91a55011540c0c40e42c0303508100008560201000e4243c0c0e808000c0b814400321131000414903919229400c0070102d44441c40c0581c810030b011440701c500c070b50034149190940c9080c2280c1c0008203140203d550a030400302d120039440c20209110303c08a00075100a26521407018680a8010400d221750b20405004402 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 623445044 1250 623443794 623443837
    0xe07050f0306040803040302010219090501020c151602040f061d0f01030c0b0304080d05010b070b01090c090b0c1207030909060801021806130e090304030b1f061d1302 73
    0xd100d044541a1600280a05403d985a071140c06181e0700c0280300310b086540c200104129949035407000c0c0030a207841e03507a0343c3d030450a11001a04e0400c1c0d41c201188600c208084040400740c045c2c00302d5406030034100b072140d461802440400c01a0041100c052841401d244010030b500b200307041d40e44010120140c4084640d211001c20544442c020701000c1d0003060982024814001c0110084d9000b521070408145044680180780003281c40030f8004200301da9000403400b091050032000d076405420a01020400c00206660151140000b80f0902e240320300049510121947c0a000b2248016610303072400741d817070350103141c0205040900e000340c08405180110100d00d0050510070f03101031000c0c291000f1941601001004186e4000514440e00428614804210341321800e4140380126075034002036071580d046183c03405d89601d008208050980307aa1800315800c0442c6071140040302d00301e0a100e0616008004910302249000680c9900308212680b40047d840710b07a4010180c803110f036414808601c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 623446294 1250 623445044 623445049
    0x20f09190306291e090712140601080a0c0e0d050a0b0a09151802131508060a0c021f0908120c13140a05150408160503010e06010f0b03070903080d0e0705 67
    0x4091101c2c0c0202e02203004c5094298107110184c00e070800424148401c1a83d031140100701554200016004816645d6003807081075600080f10641000d501c04090200b07022500000f860100c04d011030302c6c802d400140c50301041c44001d114281030140c120140c02c00a00d084a0500080c1032004030407266525010402407410007284101c0d17902041c510b01075000c06555408214900c8094100103c255503503541072011010510380d880010300022001e80035a1070040c080b04222608040043c0954010a512401c8903111b29015110180314500020740d40c0da96003450031850140b10f4506100303000400900240c041220050801c8507980000c1d011a1a103400d040540000c40a000941003916544144410301c4c216100c40e80c14035203020141d0400740e9031095503240c901080c00a202c24038850300240300509080c018071244040c940000d01d401c0d450a0725018401045102d86c0d005404007002140032140305445032070096420801d00c3c0e4540702c4e40c9034448000c0541803402807191288c2e03240043c0c03e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 623447544 1250 623446294 623446309
    0x2f0f0a030e30060415090309030605090313030503070b070914010c05010b040f1e09020306040f02150703080a05010e0105100c0c03020a0305030a0f03020f0919030629 73
    0xda25980312064942440c00784040700e4114554031060786110702001107299042c219042524504a00910103400c050070445000e400c1c0c030034504c1c0002d0418000301c001c40d0304249140f007240d80c0032000007015070f5040240d0341580141801a01c00c1e402c2c0d013500006020000028105440c00340c4401c8509850b080b5048c1c1e00d250fa148600900323507900b00202d220340d40c003034040804014090700c000302d0003c55a80c0020308444010304001d201e65610f003c40450b281e00450240807020038003400f0440040aa00000d03603658005100400c00c65820381040c045445051001600045001c0c030b8648a61140c900902400012101d00400301d1819000084c9071480d000b40a04866001d060744a00403d0004101c4007103000e800c090750955490b44e0000010f845100491004601503c003030364868440c03250003864000c004100c1003c00d030042c4654024144000c1c2250101003003102c241c0354070f211010316040c020404c1c0c3c1c00540203500c1d2028035000300f605440a0b2102e4130180340d894000024034410000c08 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 623448794 1250 623447544 623447563
    0xf03050a0c1b050f0319020705040b09060909010f050f06090a060501050d09050c060c0d1106070e040f0b040c0f2601090203070c0501020403030201020a26040308072f0f 74
    0x8110191005084070150302c60100d80303016409a850300301022025900c0c0da4850700c568200600080c44c20004154144960307805010122000c0c0a084044400100340000c054030151040c0d026501007207050200350b01c411035241c07a0000c10700c8a403030500c0402da070514003103e1607030150b102d00000030038115061180380180e80b07050310b813241004040b8a00800a01140c0b070215054407a01c10480c40039030325031000e01940300d0000d00900c40c669924800504280d842c00114402c1d0744204148600290840d140246e801e0090b107001036141c403022000c90140c140702d101d5a030032070300d004005c891541c0c2c0481550700d600055118100c0030000198200074000c0c81300d09441d5589421801400327101013540095401018600c2c02d5200541c06440d11402c9038046d60044025030360000b0003403041c50304403882000c41070108a50201412200056108410b40244003d00b003100c1b8500092115001c2c91051080000c965a104031681c1241038140300b200050031511581d115041c2100700f030060001e00c2010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 623450044 1250 623448794 623448797
    0x40b07090509070212130f0e011a03160f050f0a090302090c0c0615030a0c08070303030501050607020f01030902060409020409150905090a0303051b0f030601090f140123030103030f03050a0c 83
    0x40d4044959901741c00307500504d010005000da0883c0016115024524031000f5010220854245515044407034121090a62a5440203402031040180b81101400c0504142135030381032190320725071024011a00b82c0b14032488980303c0000405c0c40984660301440600c15240700f03540c0560151180401e41209005040d4140340c2680f02e0720008a008900e84012010820302034200d4100100c0c80d524030388110190f420400c2c4a40c070142042041c16071600406004180c1914081d20704019500803c2103a14070382000c42c1410b444075001e00840d143c1d841103070018989000c2c00c5496035111080b110180c110414441d041410780b807004140c0384260700c505d40c00b816000d00180f03405205680d064000c6d000c020400c501c4400d000850403016109203004040302c110ba100100e507a842c0c03440c005045014550030803404540b801d0014442003980300c0354031030248802d00300030701c6403c42c00040280c80c800f20800504155001310002041541200d00c40700c854600f0703202031209030f480355620011558958001e00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 623451294 1250 623450044 623450053
    0x70909111803150711060a090c05240f0903100b061b0a0b0c0306090f28091211060f13030507031e08071709030a0809070e040b070905090702 62
    0x40104144491000304000d0182c10790765250640d01c07a442891004030b0b042c60201d0b602c2c00b400402e54906002c9240c1c0004407031070130481204035840b9402030340c48a000d200e000b01422100641e441201d1414000c01c5440880c40c01d545681680c29004260040d0b0f480310f010f40301d03540d0125200c0c840740c0100c10f1000000b13070171107007005500e0080c00750075210000640c410340290200840440e00382d07004c06110700c0901100503505c0c1042820f000b01041d0040c11104508444018401021710b92810401420010f00304483d408008412960040180c500000c00b550f0306851140d0000c3d0304003004803003074070041094a14659522400c0c1081c0d01080702c0502c0b02c460240300d00d01c002800b50001d0201d85000c0c2c900800c80ca02541d0054685881712400c0c030011032000d2080005140d4001c0d24894001d00f2601200c14a09090001681d21b005101100061040000015207460401c00c5070358020304005a40601c2420542402c04410030300b0b6600c0800607103462000300b05402c0c00456607024000da8ec1c01003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 623452544 1250 623451294 623451307
    0x60c09060f09050907050703050408011109100806010f0509150309010c0305062407110402030f0405010501060216091a0904030e030d110c01030b0f06040b0324011b0c091407090911 79
    0x211b440360302410045003401014000494110400d11800c0200585140a50341d1880000708100004940c0c40328501040090410008903981c44034280802d51a07030b080c415101d0b2000c0380001e072101c1503110340035004800071080118060ac150401c41d111500d5850401854175507800f401300640802410030103011076a43c1200c200c1244c000100401e0340500c0c8243c0e51945101c00050a0364010340e006071500c0b980742c06100a020081c441c40d4010714071170000f819500464401a1080000d07880f41403c15a40c48202d0200c206007090700c080030400081002e00d00d440c0a20b0301401c045c28250404d4001d1045524011a6034021124080d1130114100102010168240114081c10081f50300c241c201d9099142c40010b0307101d400c050302c05015101c10fa982c99103003e0f0903c410706c00c05004d41c0c40d10f100c440002d44165076040700c07422401d181d001980c80e0b0a0715060a01007a489401e130f00c143c0c2607074500003222200c40e801c264242d00600042c1d031400b0440d942c1d16031813400d0b00e08590713001c0c007210404c0020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 623453794 1250 623452544 623452547
    0x70801060f0f031b020f0c09010f09050402060408030316030c0e060d0507020a050304121a0f13051f090312140601050a0c0503030c120906010303020a0b090109060c09060f09050907 79
    0x6040803001c0d41c0380109070b00000071031300b0781c61001c040f0090025a022503031000b4182c900b0301c45408075600c00ea0b01c01481d07600d08610620b090595220b1070040c103a492004c2010754444104032006403500008495803810611100c41d922180c6090003000285080d140303151451040141d2503400000800b50760030881448a02401000c012302804c00f944503001014001507024405030000341510100c0c0311000f0003608094024599004640e4046800c0310704200010a2900190341c0104001c1c000071417584d031600c0c5c1705207410900103c1000000085c0008407003182150000c4007824401c2c0e407a850415006440303682610091700007414403210410004455500c2200034020469951402046e4000ca03070700c81d1801c50b4400d591643c040c0c14000741720b50040c43c280c0d0187e608806040002c119a45c50350314000c1d120402140001e1807582c89001250740d003c0250070034070501c0c1d048242044200040c1c0307006417141d0382030310803003010507401d107001c0c000c0c00c1c05640041c01b15913010b0054507050381c58100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 623455044 1250 623453794 623453807
    0x7140105121503070f180203091c0203070b010902072901090e03160b070305090a0807110103020f120906060409020d08070f1416091a0d1e08090405070801060f 70
    0x641d8441444070044100ca54041000134010180a0248500c090038095840b0942c4150411200428010024001050400101c3ca046132b5660003601040f2221500100e041d44512000600310755605000481c95424940c014011140700c0c011401e51500e00e9400c41c500742e000300c082d034a45201c200b401004185001d400680602034014262442d05075500d164041c0101d1103603064030256000400c1110781505403281941001c5500002e041401e03690352902298802c8020003808440d1303181c0b003400941d01a03015164035050a199041d25411040c01d5098064800c44600015119860129449092a20480d151140c001c3c149801c059000d032903180155224000c120350300f50b50031010360045200490201c00885503800a0091031a02c081015103915160304144051442c00d28111355102c0b0001e24040b051000b03031001c412851940c10151a80b621010700040c4030b01c55032510104006002c030040039005000c0b0390130045511031540440d01c0407000d000d900007060071019901c0c0d016010f046d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 623456294 1250 623455044 623455051
    0x60718151d1f0201140c070213200c03070201020601050103050c04141903030c1515140a030507120309140604120501180311010c0e0a051e0a03140714010512 69
    0xa150340c945001540502480b03100011558006035500c00710341040b10030780300f0119000007030707482c01500f400f1094002410104036446500002c6907070b100703003400c001045800e1208074a4070010450300d030607600c203000d6241d40c091030b03049005009c3c000000c100e640c001c0c8201c601809881a403d400d2500301781450102003c070010503507201d881c10300844907040304400c00c10b0296200755034401001283d882c04490060741c400c410b0140700c0c01d04088d0b07103d100508049400b1034a003210140791004804000c22016034040e000501a0f004d401404240305823900e42c0741242d6486950b5182c40d5681d81d900400c1400603808900d5407106003040208440401540c00c5214603004400014020b112120b40000c2a240d5483c101d000c03484800c107140c9814020f01c00d4903442191424a08128122080060503600300e03070190b103125001c4013401404032a000104005101c10181101d6469604da0400c4880854283e100003030714800c1800100d040b0881d0460760718240380c180c56060920640f10903c84c011500103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 623457544 1250 623456294 623456299
    0x61503031209050a02060f0406020f06090a0f02120a03030e120f09220513021f020717120f041e060e090a0209030a150c0f02190c0503060718151d 64
    0x101e640130141c1d54030b000070b02c84451502892980d480c83e041020b42004841038402c1e1035900040104281c1a20128240d000c01d40d00c0607429842142d24800514890041c0809542c81d100c1c2c8640c082c105a0142d010540301c980307080445140300400303141c41e0700501c541c240404914800744070444039400c203642e140c80034081c02d1000545607a6806003c00031070308101d40700a0074070701d007007100d40a42c10036542010380d0300d141658101d0701c021046400703940c421240c46941528001900c0e20307100d0050038002c8078080c80a03540400d030340302c03c0314200204a030042d00074440700a00d051203101c103070921222110b044400540701c80791805805400c01005000040c01c400480b0703000c015103001c5070307018802220f9582c4a070b080179070800916110b403400c680d00422120184000d40c000c6401158000401c1003542b02d01c2c0103020303000300342481d2042d810742030b90340260380621401081c04440e03500901c4886101d120070080b190390a903661000c0d001100d2490000d404150006880d10507601006590200010007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 623458794 1250 623457544 623457553
    0xb06010309081c050c0313030f02010e10060302030f010207171c06090c1112091903020909031b01021812010608070b2106030c0108090114011206150303120905 70
    0x4980b00c44140e03501459071440c0d428401c00401108083d1403203940c0d0014003000d030040c158a41225042c1c1003101e1240048c051000560103456840e200350401070307407203843c0801d850021102c646880060941400100e2103405009a043c035691014400e80d2012500640084c40070b00c5030f4451807110707502c0290b0003a41100060f50307540d14942e9034001c0400134440000001031340070008a0040c00d80c000300c1064200c07074100c83c0c0c1c3c0d1800d05103082e060f500c90240031210591800e90700000304c1c0c2600240c0e40004e40150418040154207170000c800350800110003c040392545002c0c103145401c034272a000d0801c28181401d032034a13229082c81c2640e00d81640c0180c0001a0f4140c41b1030045180403869485515891400550210114400700311091222201b1084014030304200d8002a1610610764407241040500300c0001e20b8008250010003075007800810360a001d5031140800400c05003030381000d41c0d00604007a5002e8850718a50386010071680c1580e0ba000081a030300c0303800d0700a010b44007020f40f1148607 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 623460044 1250 623458794 623458811
    0x90f0105122d0c0f060301150309140618010e070e0402040924110c060f040503070b040609060e060714030705120c090f0d1a060a0b18010810030507030b060103 70
    0x1185602d200c480703044012040b001a8806510309421264094041c10340c08800e0602500c501c01601d05484000d980d150112201d150118018003501001800c101035411340901d4100300400c0b500d01580c00c26140c00740070028103c00d1030994010f0b40301c0314955401108204101030303d00405540092008001159030241d0343c039402d402c0ca00780d0f000801c01c01c002c620034444840382c0d4450380102d410b03000201e03410055010105621840020004511a4114000035003003000c144200d4404613800302c000c40c82c2e4203060403c000200900e00c0225080c41c941021809000d600042d014800c500c00e5640410100a03a10301c240c0d507400150081c424000d061007a4030b0101c01c0003100e280304039000c0c4070b52038881080d00100300c0d00e04c005d4403003140246001a214008039540a040715010000d130344805189803a40d20100c2c800312411341c8181c00c00700c800304207010719603054001558101c0c801d981e0a5200c1d180e5104190101c0b14030300c0001c1090740110800c00029511030041a0b0161050400060016 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 623461294 1250 623460044 623460073
    0x60f1320030a05073b090f03030f06011704020603060f010306090c0e150f041202150d1b111504140303010e070207080303060127031e060b090f010512 66
    0x91218802c94458000300700a022405481080d001d0110b02c96100c03100c199a6a0300d1180b4411703445050400e50241840010600c240401c800d08941240d041225902c0c689291801d17032604c4141c450600107414800c0c03091a080ca5071110b64022900101050316580fa41d408018101e42040318980c1172540341c490008100080d0321030392101860946807510030b8900c0c802048041c4850040309101d03004180407840d49a202502a02c0564100e0350781220798000d18000203010690918411100000000d04101001c009030807004590741508031340002c0b07a44102040d640354582c00c09421899001120310581001060740040c2c00a000d550141c0c42d0000d17860f06039042d036100340c102001c0821410b00f032200c42c40e41000710000070f100700c2003d1421800d0501c0002e242068100106c0c0f114482000d0071200881c841e03003508000c1d503000540b5008481113100f410b4003c64030120076222140381500780940c2e42045c103a400e11549400e600011641c1c01c0074100911075008090030400c500c1400740722112070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 623462544 1250 623461294 623461303
    0x1030518030d0906050c130b0c1c11010f06031e02040906061509060c051903020f1b03011103060a1a0f030907140d020901060806030a060609020408060f132003 70
    0x142c0c0c000042414500360a2000c1615000b5003011501c0384204040c400b44006a08001c0c1a50340341c01d8040c1e500c600280106160407070100304018404040c042407d00c0940040606100c00031810090203076070302e20081c550455225100c00f40c2004078042400c6801001c00007a00b0103144024000201f07096183c5031501110303a01c1e008209110041c290180190350441d24401c02000546003180000040d5916191a810010000c029141c0004070380030403d030080c4003480c2541c0e0700004440e6070f0741c6046110440581c03101c41d0326029500c0c1100940c00724655108403880380300041c0500704842e00e0420000142d40d2400c3c804146103406102620b0a4040c0e500114001c1c40c82c0c50040107540d0814118505e010314485006220390348403010500182c4070041a40d04440250401001d42c3d542c1d640480e040640d0750030020841450198042002283c5a004e041540c4da404103c420343d65803c0d400130314600066481c42c503150542d400e0000003071107a0b4000c0c1c4442c000e08203200240c8090b1b00100780391 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 623463794 1250 623462544 623462557
    0x8060a0203040318080a030f09081501090c03060b04051e0306040f0b0703020715200705010213060f0c111c05100b010e101b0807081201090c05090103051803 69
    0x55400005210a1540c05124040c1202111203010091340c5003210752135031060110b10080900035103003440380100d801114075400510188040da410f05100b41c000c405008000d00032111100c1c504030140880c14464403490341503480000c13050b031404c1d0429080004401840c1104003124101d108480d04070703102409940d01a510400d1030a00d040c0c51868040041e1000501040401d48144005004240303802042e29640e112014005002c5030074084001402107181000c8100e00000a010340c200801580244036072071003403100c40c6001c0d0b1112011a00712004030071a40001d18447da0030320101d15941c501c00c0c88548001c0006a02c1d2290302445035050145080030b8816400002001030001b1280c01511003083c024648442e00c2d0368000c0000308040ca20340b402d101000f00030001180d40907600300c8090102a040300c0f02d80e407120740da46400007990340221001040c404501c00001620740c07140c0516405880191121404d00002000440003130100801c54454000c0700206160329142c01d0008004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 623465044 1250 623463794 623463811
    0xd06032f090601120203060d1416050901050303071b09110d0f061a0a02010f05040b04020109080607171504110406090e0405070504020c030d020a0c0b0106110d180806 73
    0x1980002094508840310011a926008035410000c00c01c0030fa0340003956021000b825900140c4030348402001c511404800d10004001100d600c1788100207460000310780380d8184498600b444515103c405001419400780704581c0c00d51710600c05c0c1070008080008070044100742a00000f64035035144421410365402540caa604101c00081100319000603001d2095046a500f100340310a500d4035204c018200d02480f940d80c0703164401300b04440342a10070742064800c200100000c1c806414181062140c0c650151001ca0205500042c00503080704003207582445250140c40f58174001d14407004000303420030020075100300e0122128091801c0da403503108260054810024031902c2c1c50420b1000f170180210b60b002000001440d00421002604c00174404042e074105603030140e1180b0182d03285030724601600721502100350021510400a41d4400c6110a01601403030343c01002c2d907039400080d2904410050840e100e0741055401c4032005002d80000e04c1c048401d50a490f0002d9a02c04140c0d080040944035a00c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 623466294 1250 623465044 623465093
    0x705210d062313060b1c0606020a0b040b0411030d20070f05060a03090c090504051c0509100e040c050c0105150d030e04020706060803030402210a080d0603 68
    0x140302504034070980d00079010384119010a40880c40480c0381e80140c59910601c111015041d5280d42e000c180c0054008159a00c58191290100d01502030b00903440e0484a54251070441c0c00554940700080303210b461038000b913140b6950349a5841341a40f11000500c182c82406141403032000700d8401b00422160441700360303610303101000411031f003100760400c0c0710745035580b548407003810300c00304042c89403000444401301c400507039070141101d0a4024081406000d0160004100009802400c0742c002a1181d0b00c41d00c00c2e40c413120400020600d6142a40d103401c0001201807000d104c03d82003000d90b0180703014007800c3c032100003801440020180c5021088241c0080c20214249044010900840f50400301c403200000b81c013481000400c0f01c4201c4c105016003001b80348640c130740785500c466046034140b94014030203002007034941e074459989a00507a400ca010b1000e0003407103603410001490500006941b54041d2030b440031241c4038461950054016140e015035074100010004000c00c03c0711303d04811660005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 623467544 1250 623466294 623466307
    0x606021c090b040b030915040f03090807180f2d36170a030204060207050607260f0706090201020607082206110304050a02010909020301151409190f080109080708070521 74
    0x81030709010f41c0c050304158ac001c040c02d011aa2072030180ec080101c13005c000281c44d4108813240d0300035001034500d00420041d0103050308451203e1851048500c40844018444010170411007034030020540302c00ca100500c980c1d20000507060052400300e01c14024400d07060398500781d40814546034270600c0d0403004a50300050421485070144105801040c080381c131142400e090340c90384074880f0f2043c440c450000100055070030748100b4503400c1d60000c84a42d04141e8442d049440d00d28002c1031a043c0c00e0b030251040e440000c0d005441130015a01c111040084848000ba145018818841000030102e420b203848900800d00354070043e02030751041e40034000400c2541c0b094000508402c40940082c04c1c030038010001030149035036903140c2c0f0580c2005482c00500c2005070f591520802c6c01054003a9030303c9920b4422802521054071140410b50b24048800303c14103a03144440703422155410300080144505224046c041461000500603e074001c1064590355010484c500c400c0041184903244040e0010650 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 623468794 1250 623467544 623467547
    0x2070602070c17210f22030c140f030d080c040306090615050907021b01050705032209090b06060a09080f0a0b070314190608010606021c090b040b030915040f03 70
    0x45a02c4268540c4e140e070741140500010b00c0e05114200420305c000000140b001002e502c036011417408840e82d004a40d0100b5120300c0c125103903000a1050050070042c83c03106c602d0b14030300310006014a02008004001d00704e42c024003074a080304000c00b2134218041c180000404542603000703641c0010312a2000247c50b0410381041705020303610f81c10203030007916110104008140c001400c80301d803c03061030402c6031080f00f07600100ca0501c985903004000e0300001c2403810f4800201410301460880020000303140c0c039162071200c012201040805081c2040c03071408103055003807030b500030281c41e040b81c0340010000f6240d0030302c3c5103007400600e540405684104a028180203054110079049005441c007440309143c40801140b000c1006080c42e00c102c0c0303254111003800c1d4007aa110100500781c0c1b6000f4007219130b841c038019403100001c01c02040c601000c03081509940f407041e0a54010b0340d034130070300d03090605003000038402e050340000b030403c04580309464003040740340542c0740124840cae442682c8600041009240 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 623470044 1250 623468794 623468803
    0x1908250507150801120206090409030302130812040b0f191112090a030206211003050c1005040e0702010906150302040b1002061302210c01140315010302070602070c17 73
    0x1802c80a0308000c03030408503540461054110748000d201c00404410a00009035a8407032070031381070790083c07030030300300108040e095005007800791103c0302e019601c85e903a091000e44610300005a80c1200c01c003003100340620b14540340500b030b000328003001560400c501c150459480c1201001404042101c9280404541c00200102c2c44451140c40c05036082c244400040365607040c03030b070000078807504000c19400340101050808000f907450300d0302c03c0e444a0500c5a01070244051501054900d4024410090802e050194002061200350750f00c0038507203441c01011556100026065000319501d600c00d51000c10902e008900b1819a1075100d00d0301c240ca980304010440341c00c04c4a040c046e505c82c0c1c180c0700b2190740100384203a200498050446034001c01e80300142a0045d0340d08903001c00c9082000c40c00c00c501c000600d240c20964280c840981d0080d0000d514002800110b450340010700c0034045101e450b500c41d80113000c43e24030810004d0700340801940d41c0308030a04aa00304d0307400091030510968000d0310401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 623471294 1250 623470044 623470049
    0xa0c0c0305031b01150605210411011b0b04140a0501020706020a030f0e0a0210053c160f0602070b0901050405210301051c02090106020c09010f081908250507 69
    0x8005c000549003818101036689041c03160074240000441d40045072501c120520b081b020004948185a20741407a00c110076264090049000501d248400703110006a01020354102d44c211300c1c1440d07240c0c9d4035502c000f4221401c00c0b20300c600d03005580460b00001d0090015100a41c4180c01c00350711065085401011a203c048501c0d179002c0c108054041c0e84503011510894003a01074070b01030325000903100196030901c9550102904044e801040035030601100410703615000410905a2403d28400c80c1100b050080b9023010781116003807581e40000503881c11144c10603e12800000d400c103607142c1c40b0844200707422654031200c0c0e51504100410080f062101d00fa801242c11540300001108951071486808140141401040c0f40048440c039080749030021504c29a00810840541d85c50f44030086d1182100740c80031b401085030f10000700d0301105070480e00b0261103024004000c11105010350840c6107580310400c0c1e0380c440040203049520300506401d181c0407000d002500440c000130385001e40c600700390343d03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 623472544 1250 623471294 623471347
    0x16082b050705031e06030106051507020f0118140d0b0106020c010801050907021f0f06081b100806040b0a1a0c061510110c060d0e0606040915020a0c0c030503 69
    0x1041001311074400b1081e9500c01e0301031580c1d10350080e944c441c00309004021641005070b0101e0090814400c8405001c010000ca92003940e0801c1d5202420005540403115210044540981c9034010b2091100107442c41e01101d100030460125031310142c9480341c2e00b0310203030041801a04800e903104002d58100d504c06005080640e0210518603001a000391960300e81000d4107040402c40c2a11100e9507070301c1d0000608950f282c0c00c1080480d03914000c0e02d640e04141d8400707816559403c0310708101460100c0b81c40896042545503180c0a41d945800c10004180c44042d955020701070345004940c8070300c029101d04041c40459559036032140c1c040303901031600400600403610501c440740000550f89501c07400700700c07004d4541820b6401164400701076061960790801c8603004500480d43d441c1c0e110087d003103140102e60b01c030252981e680b0340300c0130722003514290700d409041c03002c5960380358001c0d117247c2d401012644220b1801d800523221964421441080035803054580c0c0d807020844c2e0502c040c0300d4070081020f0b00c11 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 623473794 1250 623472544 623472547
    0x120204120605070e032805030301090c12090f0b19110406020c0a150804031707230901020c0112090f06090b101203030504081b1c02030a0516082b050705 67
    0x15813000a54400b201032141072040f140d80300c6903906402c0d040602e0b08060380402580d40765070f1a04900e000608005206800040c0000d502c500248450b104020750240c03c441503940300d02440e1611000c000e005090182c91b99103c40808401d0303013080c4581c0d802100c288800e40c0d07035549000c000a2a00c00e544604c0ca110b40da407120300704100481c8204103141e034413140c10700090a030745901301581d205441e070130768010f00185072003040000ca500142108810140303155140907182c070240c030181079005046100d80964840d90b82c00e40c040d03028404442078011812000300b4011240c0d80c6d83d85410f08890b40844045032180902e01c100615a15426401050301845840c40c03031800c50754440803509070b1005014595544003080501c0b403601c08036044138005580c8400e11403940d042e00e0f55260115126080900444c0326055091403000c4101c840582d120340e21141019440b5402000c0c0d01e400300411070303880804002c00c05140b005c0208034540700c081003c040b030400c04424000d0f0141c0304003d00c03500801c2030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 623475044 1250 623473794 623473817
    0x3020607030e130608030d0b0607210207060903110405041103070b04051c02061c06120b0412020303150613080607050706050a050c07030f0e091006110616050a12020412060507 77
    0xd0000c2552211101030387c0100e0701080030404a0500d118205018100074880c4040c001c2000040060300107218442c0e0803185031aa0315581254008040d00001344070640d005490030441c034140c0c00c1706070028002d034480c090000c12400043c1c6404a168460382c1d41c1400410200840c0c075003081581401a4950782c0300e04e111000d5800640c00307100d0010f24203c95400001045103044503544008041c1030a5401080c04080c282401d601340070040702c00301d5050034811010b0280a01c040b007920b004402942c0b80110003800001048045c0c1c00c9101c400c1c0358100f20400004d19280100100c6005038003640315203a0b1b4105504110301034410090400d40240e061005101240d0300c6031302141c0300a5010300c3c01800c17806100000700c5840d0040e552403544501442c09100c0d001001f9880c1004882007511070700b4205010880040e282c400844698140b05c100041e1503024a000707000074080c01c0110f103050704994480008900032a00310b40c002c05d420614412101082148038481c42c1c0d040062030511881101 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 623476294 1250 623475044 623475059
    0x1030510150c0c08072304060501080c07080d1418031305010327080a0207060c0203030304170f221202130e0703060e0105100b040b2203020607030e1306 67
    0x945903080716041041180c2e14100744518600030b50701a000b1038045d40e460360f40d18411300d1801401c81a070407074455209850034415250501c220801c8a038180c4404200340d8580d449011701c1c0d0028001076581110810000d00030184505c1800279001051510720700c541451504403401c6811082d040c551a40108408090403400e01c0c41c030303405c94400b441c01240000714000a4040d540814a4100b400e10410f0620b90130003110360093f15035040941d089600207580c3c3c00b000c5603003010071000a90160030400104010900b24840c801200c141c06200500c4c00c0c00a2040c89540e510030584914900000480c170b118180c0024000401807600950406030b0380c1e806c0c0c00080b404c03110b50004d00603041d6100181d0810101c10300c41c0c1d40086801881c10040b0320000700c1c0c2140a4101103a07000d02410450380049030414442041d40d040c4c03101c200a0500382501c500e040c02040c0c07200441040f0078082e044000005075141d900400301d4070711940d1031125803c20784090180600c441c14244032040c0c1424801d11040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 623477544 1250 623476294 623476319
    0x9040503120a0209030109051b06040b0d0f02120708013f02031921050715090201090b0a020d030c020c010c02040218270105060304020108010312181401030510 70
    0x10700c49102501003035221440396900901c1201d02894041d42041d001105202c0c020800b0a550100e4000c01d421001011003008017510807401900c030f00d00300501a000e070104884d40950403908410000500c0c0c46610114005800021580803002507030f040300622041c081103049844401e8112011070180d61055500d00361214415021841c02c804008c600082d9a020491102c403202c00d445801142045410b000751416031248000350000b0700d000c0e4004120703109200329050f694001400b8021100c104149802801c19124240d0411040305808102c07111540300604107101d498000704031190940030042c0036582c000d204c4100359008540b0340c02031030343c01ca00103560450303044400590b64805000b039034100c0c864681281e60010f6407500e1805107421581c146017001301d00d00080000e107a80e500100b28840c070003250000d000540d403400401c0000d52002c4002c40242d00c508145c03817841e4006000340c500b072419501c100c0c0c0e15003100000c02c040b540c0600c111904510014020b010707190903c0e00b0746040d07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 623478794 1250 623477544 623477557
    0x41509030308130317010602010f110708070803100302101d0d0803010b130b040803070b100b1602010509090a060504060605070c03170706020a08041101030504050705090c0f0c1b09040503 82
    0x1a92204040c10f41014807544100c08001c0c0442d41d21070880d6110480207000340f000d620300d00380b16403070094418030902d002c00c00c2e900ca82d940159414a0700e80aa95682c00c02c0d0400b60490100f181420340c0400107030f03a030f80c0c0d024000c145213a540d400d418401c2e2500040c04940c040f602401410b4201e013041c0891246030841c1d06640c2000072040c4d48504070010100c481c4030650000034003100c00715010844900210080c60b03158051140e610403603c43d1556408040a00c0c4100ca116150801241d041070a46508040005005041050401c031403000450034000084946007040d80d40d84505101c5842d1a1042102810180ca8190304001856540d104041030707500001d07240c0c0300d2600a52200080c0e500c122403034035038800001d64491340c3c5210b0141110f48191022681c40d40b01b030020141c2c41d4820703c50f4600ca5a000700040003420714001c1070113501540588514181030041100e00480d54405008241c840e10080c028000034003009246007942040324400c0e48a40701c92014400490b0307000094030320 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 623480044 1250 623478794 623478811
    0xa09021e0a12090b04021f390b180c01020c040e190f05100903051c020d0908071202010516081e0403112e0515090c041509030308 57
    0x361401035003010389502010442403042c103410b000004040003500022503010314820ba4041400440c40e24144008035030f0442e8000000740c080406203000540c1e400d480c541145100149440e010740d030505001c2d008405142a41d07001c8403442400f400366a10a40b04048003148000f41a1600082000035101e40d0200e004d18421601d845818140e6001031013014400700c0c803c420308641c80c0340351900c843c074840c00c4c8505584034094400f035804140d10500413070584a906644007031505042031810300d60784400307100205c1d00d030b5400d0140c0c1c411125244602c41c051809400070680303a42451414500b15079040241a0031a4101030902129003038160780c5040d001280c3c1404138841d600d299265075000b10764a281147c00a440c3c05100602d0f42091881c2401400031098610b05460350072030600b95000043e80590b00070724045a80c0540c1919030102e034005038220303c1060310b0040c003000503121000650f00b00010702c000180800401d080b01180b803007010602e0921001c40d600d551000b411005000b0440d00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 623481294 1250 623480044 623480047
    0xb0403060e030d090b070e0406050619021e072405030c0f070f0b0426030a0b03010207020402040e10270903020c040c030c201002250503090a09021e 65
    0x40d0200610680f0200303410244200054041414003000706041514080c0200e81c0e03442c00e0419504180c05080f09440018041e103103813060181038034030342400c403c100c1c000314003844201c0e9040d80030400c05454081307001c8000300812403c06803c8000144040301c10311000d1120810464895000f1040d40d60100d0b255107015281c0c07296a042882d03c0c0300700b4500408e1444030f039a08500b041142c440c01400349020704450f5521b416806001e03198481007440803403500c003041c4002101080c0c250004c0c4024031002d4005400c000c616408035080c1c0c3c01640040c00103a81120411081c007001010f03190007820b6900c600b0440300c0910035417078a0150f2840300c0881c81520f13251042c0c207260003080b01c1c5540c858090010001c0c0e40042000900030300407004004001100c150b40d59144251250805d864034082c14081c141c006c80c2104c0820080d4001013441c000c81030380d40000d40e192000b628143d900303075016801842e035404200041100c0d440b01c81c0c0140c1500c41c1f05000c00c51141c211782648500030317107041c4e0485 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 623482544 1250 623481294 623481311
    0x10e191803180e04080d060605031308030702120d020a080601080c07060b0f120604050f031821120c010b01030603031707090f03290f040f0c0312081f0b040306 70
    0xc10080350b0541100350301e84400000e0000700719070b903001004844000001008034a0b1103180448562109507002181502098000310100d9008001581c0040d0765004031032a0400064a0400c160000403d2280e00c0741c0c0400c0c544110b41d04105050340c0294246000c180d2072404001c008050b000c2c188020701840d90350940341030292615000e00c20280c030000c0c0703c009a0011803000350741e10751040f01c1c2200c0c07a0003140049402050004142c400802c3e0022107545a480140c040c0050418410780d064158035072542c510f802e0b540180008007465048106990b910410f84909909699502004504161410f402000440d5020203600301641c80821100c0054403000000c44203414203411004110758400000010058488240c00c2040312007100e010f0a4921141c04003040401124811642000074000400203120104108685131142109604040d141e460391030707a5650303000c002d40200b0026000d0048142021b806210740b180d011031031070112400c0c08030700081c81c0907910006140640300e1440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 623483794 1250 623482544 623482577
    0x1080f07080a150801020903010e030406051b031b060114030a0b010b0901210b13110a0c060f050406060e09120406031508060709061806020712020d0506010e191803 72
    0x1c4a4a02d68641c044102d13480d002a24002e40c800780040744a0f62034030666a84580380071040c0d40458103a81c490a040c500e24980241d16000e02e00717801c140a000420051201300c0c01c10000d041c500b4442001081c0390341c1040d1240c1c402d0007000d982c50f8801d51101c400351001442909100c2c0c1075414555a160f1903424000060715044004100490407125140e440c110000c4c09074041d0004000031901000b0100c2c00b22207200444100c140b2000104104000058805014030b030700c1b1501c1c40c42090000340c0800d014200d10102c50341502c0441d20b003511480c00f0444115148110380d00103071040080d0100310112104004580700350312511003859292083c4d940c4c40c2ca0018103803001002c1e4001070751524640060002c011160a00404002c42c3e10841101421804650800250342c901c0e0000c00c01a42480400c1260301800303c3d040341e1240782010200d0003d00301748400c500800340c00081040034104409048101444130841d16141450840c2000640f516542242940c076054201300311017003079150a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 623485044 1250 623483794 623483801
    0x206190f1409010c020106060810030314040e150a06032f07061a010206011d04200d060605100c0506010308031f1e090e030d0e1c030207050c01080f07080a 68
    0x2100c0907035244020440781c0c0c41d040d0089680103005500030000380c2e40300d003000c0e10f00d49010786188600284400050000a00405584070380c500d86034074072820155503000170300c80c0180032107903502440f95a0000304640d0924042440103040c503400d080c03101005003e8400500d122800c104d00c0c0c030380b80d124200c00c0050166811100415001041800740d2601114001d180604c50340d210f500501c100f80002803441c00d03000c120080c00e2982c14480b03401e603e031502c8001d0011200206c00c1402c0300e0001c250907007581c4003c1c030354050501c140c40128510386010200651250802035001c00c0c4a000ca10f0305000450108455065903400210551a9180e4019058030b182ca001c2d00b1f0040394070b08178000300f030a50354040380026105080c0c00c2c900d113080c0c6401182c2c00781c1d10103d45000c1d46a1040c0201140040142c10842156240310126032f0b203e00390200c0b02113219400034600003c42d5000506000344901808906034001d001c0c01d01c0e41240c00d2184c1013580044008010300100441d41000c203100612a41 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 623486294 1250 623485044 623485061
    0x504080d090606080f010509070e040f030806131d010c03060807060c170a020a0b07090308042303010c090314010b09070f180e0f090601050303030613020c0a06020310060206190f 78
    0x498089160361754046009003001e540d42c440700d10400314001054805503450754862a0304c15816000c2100769a010b480540c00902117680c0070b6004a281c4241620500c1510f81c4000500c0300c240544002101d92401c442c0740900d040205030070060280015240041c1d05800c40700103103015003101c0680c0c2000b44481141d600b03880c240803400140b403500c15600060b071811a500502407000c468591a00c00d403a04c984603c07004065200c24407082000760560364642d03100100d0560320500c100e007200c0009084070091048940070540c460303000d00034401c0603000102052042d4000f003000b044c0107000117600c014000c10020030400d00403031104d071061183c2c584108040e081481d6501558a4a20707000383c0c4c84040740c0000c209001000042c003251000100c0c03604039480500034500e551282424409001c00301e054580c8655001c100c141c8220f13108000c02c5103d94061a40180c03282490b0780b61441c128001e40c49541103600079000d01c260409007401040303903000c5401000808000031041200900401d5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 623487544 1250 623486294 623486309
    0x30910020115080606030708030901020606090c07060f02031b1303020d02120f060103031e0c03050f040320040e0a110f130f050f061806060f0f030412120504080d090606 74
    0x3020001d001d4400042145c0950000c07410303664441d499482943c2d0303d0280210150050f4004c3d000718030241040c00e2019000454141c0c1c0924241203621400c091750b1080c0d0b11125210750000801000b81245940c4d02c1d201c480064030360b450103100119452900d00b0500010b44998204c80850046540e4449070b880c0700a1540c05444051400124aa0304e5400910041e0301141c0b00300c0700f01c01d1100400c42102c031440d0003921a8004c0340c250b40c804441030740100903010b044280401012001c20915002044000c110172004041c0550450501003590b441c081400c505522504007203000820154403500e84034010b881e5140c1850030b0b030f400503402240b50200c1c4000203240c030310700740c400c0c0c88a40c0120340325408810f600d0350a0780394402440109525040000f050b034400501050040c0b602400034525040c1220101c0c2c200b0f01e2000c1c81c940e4580c41039030101c2d07086513a00c540080785500440c1300c00620403420020821898030b44c644010300d1152052072051182d803024071208024450340448003800300da = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 623488794 1250 623487544 623487581
    0xd26040611072405060105070f1103010f06080f19050d0305070201061802031005060415080c070506180609010b010c0609030306210c09050717070e1302070b090d020309100201 77
    0x70f0b41c0640c8a54080030784044142e509003000103c56500807000c60b600e817070b405030381034164510944494900f9060340c0b6465901d035407641c1c035802d4402c010340030b48005420000080d080d1800b0b9404110b01c4c004110280409201034040360b1030105001249140100c8100e05000c21959680d01089004000a801494000c40c002080c41d02030603107980614400c850030b001a41c3c00b10748030b4040000302d00aa02c0390b0803403c280100b00d441c0f0a44110b408940107080c56144500f030005565800c1d040003405c54440c041c4004440801c0c800a03001c106081c1c110344c200000300700f07034030107c0e0001b48402d411000107440035458080241c1054465400341c0024040405c5403c0f481d943c0183d4691000b510f00400c0e2074400f00740c136000c01c2d981207a05c079640c060b11440c1ca90078034043d42c120064070680c000400707070000d00c06041c1d0072254a0725000c0c0c03181a02010580010b81d036103503d1400d80007582014100d40007542c071880780321110756000021a52909000c88050000d04041ca004901628864244a003406007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 623490044 1250 623488794 623488823
    0x16092706020306033c0109440c0f07080d0e01030b06032805041101050c0a06050a0506192d0e0c030708090a0c0306240b0406030b061e1305060304050d2604061107 71
    0x1100001d4a0b8070f0542038292505806452b040d1640c1b51580d01a200f0140c00c0301403201600da00510050414040605000c10030703803200c40020300310350001c80310806000c01100000018581c040c9501411901c480402c0201b802c1c00e842c1d064100c03000c1c40321541403010004048500c1d01040001541c0789a1004091095181c90790703c00014080a6071114000c09450010390400312007010181d01381c0b444d1517065185000c00141030b40d08407403d08040000f500b800344000c240030b11a1742001c2c2c0b00340360a000307107a581d0521220042503404014076490464204081050024001901200880b50000408603100700f03503a0a118140c00c02c00801580040070110019130f41d0181d9000e882100e80c1520200100c05059051000300e1055081c5449a2100c00486942504001c8007900c1083c0f000c08100303c0890700c510100d27000707a1054800ba81e42d54020343c0c0c090310040d84508000c00c0d04a541131401c10b008003000444039500070140c0014451600c4a0140509841c1c180a03101800d8100000403580d83c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 623491294 1250 623490044 623490173
    0x7030b030d030e0601050a0614071a0109020702090f15040504141f1a01090314120f03040c060201021804051816092706020306033c0109 60
    0x9000314583d885000e43c8000045a00c0d00c4a040c000312440f0341c58240a00c141144026480e13405010100c41204d504010900a00e003911301d028060040040b00584d1002a4010000c034802c0c01014410107003a11000c22649000c400d4441c0511070b415200071580c4e40359131800c41240c030455081525984070700794600c171f03003422440032621142860303e50401c80c001d0540c003040785c100b01c04550396001c154134010400c0000c406850071076445010030240c3c1c81030009031a18900b0f0340d001d13856070701d21110040244000e1000050182e0001e007250300086142030640c22003840700849985203280700f00d44d1003000801d4402c1c448031010078040c0c1e000c103450303408250300380341c5100811501031140d0041c90a28140841d03480100003504550701c088102e21200103d80d03d05001c0e600041c81960103004440c11040b01814480b0007013440c082011400503400382d2019082001c4031751031b0341c05034103030306001d100000300e0316044ca00301449401c000344040c80c07000440400c440700b0740b0b8400854610880e014000020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 623492544 1250 623491294 623491301
    0xc031612150c0e121c0f0210060902030412020d0f030207020307030209070c2d06090302010b031c0f08040209010504020f040e0c040f14010f0806010306051206041719030507030b030d03 81
    0x8080b141440c2c243c80c0c00c09130540d80c2940c1c12144120082000300c1d04c0c0e450b40540ba20b05200c04491044600c0c80321f40c00c6122003580c2469101c0302d030951700401030004111017400c10345d030210454070083c000c03801c943c3c200030051080c440d4028140348d8000f0b00141551000e0000c50055034001d400240103003402480181000104881694003916482c110b5181c0424000c55001511180680034040101503da407401042140002c4040d5980da08444800d07407030a00401c048104108007180c50b2a010341d0303010300444036091040c0100507003401044010703a510061309054500542d801030700c90f08081c4000c50940320303079006040da40815a0801007a1b04090009000f541e4810551240d0741d51341e010608030560b2503582c0540401c4080c10302000b0540700f0840b01e1350240c3e05260101c0c0240c0e0301c0300841c8402c402071601d009140c2010042005010310505241420440042454581410f200c0e11410300151202c440303007010345800210302c038144640c0000115200060a580d81c032800c000d0081e004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 623493794 1250 623492544 623492567
    0xb15061215040615091517070207050909010606090b09030304030f0c08010c09050303090904020a05060c030d0c0f480b0a0b0a03060b1206040c080c031612150c 70
    0x8900f03096000c50442c607502e0a0b841c1941c01c035202c8602035402c04482c414145429003654080006d0500c81e5141018540020b07401024250080c0880f1070810003401001d0780010100c219580c1400400c01c0015444443d0104861440d04030903110150b000c00217055100b990300107031a0201150410007803000041c0c0345400c850b46c5000030000e649104000769201800c2d07200c3c1d168503070000d2000c0d1043d4103110506580c414801020310752440c2d1284000785954000711800c6540b580017042404940001e8401d24020000c0c2d400c004800040c807800c02044a04442c0d481e0a403d044000024002001140715900b16407008101c14900c8082c0b4866904409003440140d075240081c0011a44154052140c01080741011303001d440460700319161200944120716420340c101c004000038514005040c003880c0d00551080280d25040c0d0b180541481c0b52100e0898441c0c441d4210410b0100d1402908203807802b151800c2030449030b075240380d0420030101d07404400c4c10410181840110b40d8056070144c0d20070074 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 623495044 1250 623493794 623493799
    0xc0e2403062808190803010603150902030a1d01051302130209040513030e010c0b161b06020307270311060c34031205090d0c08010605010f0302070b15061215 69
    0x40b940300842d048406082c138018082c1515008000500170180b086d0800811f550210700d0111000d960351044030100e078401c55512400c107586041c1d0130104107a90407006203110022000b4049801c0c8800c45001214105400a2080c1c0c81c0e54011441d506264054403c06640140100100d00e0126611070250a07105400c400040d4400d030746094940c080c9074003422150300301151030300c0396a40408050004150409601c140140c0c48088a54400d2004407400200c1c41a07002684a041180d4080c01500d40d0070b040040080e0140400001001800d041008882e000320f0948603104442001c9851886010360b8003000d802903c0b541300764038203070840030181942700b0025202030f8400030002039503810050200420404c50118803a00c4035105401400d00b03018000e010006030245a500c41400c0e18095201000b565142c83c800c00240d0780000000c8105961420158a440d02c2036a4480c40258021b161000300300440008403032070b8842c0000d80c0c40881180280d12141c1c144a188030001c00403224921b071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 623496294 1250 623495044 623495053
    0x806010b09190f05130536030f07050c030d0f20030c160603020a021908120a0f1a0102190323040509060301060e07030504060b090a0c0e2403062808 65
    0x111400700a1280c0f03880b501349415809003039840c1030010880380c40741c00c11580e03031f405040ba04510303001400d10080029400d00d0707940c565214450700d4014100350310b1040c002d2098008400c08681503411174206104283c96150043d503c0c80d1070040038403056030902002105200100b030340005008001179581d1f180404480500300b850341e9a20880c242ccc415041d403c001a00f02400900c3c010594640381020148161407040c2000400303561007011160440742c42185540f141c480d20040e12261145900c4180c0110001ca181111180040c0d0f443c01c0e400181c803990091040c1c04400d051044070309020540c3d041d0502c0f100030700c07020040b40b12034100e03014161050b0941c0300425414070301445440203c40034106062a9952200400d400502006005852854071400d0741e43c450781c2c564940504c154100b00c0d0004a6000680703000f0301c40d0001c000c0580c02201003142070081030b030300d60b12055610315451350802e641340e0342d10010072901c084060300310015420703014000c08505100b40d14141580c0300e800442c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 623497544 1250 623496294 623496319
    0x3150504020420040302241315090f03080d0908030a020a1e080720030f04090b0f220e0312010810091703060121021803070806010b09190f05 62
    0x540040d900710f08606103081007040100018201405005d20010501840c141e0750307522103016207496408102c82c424149078074072081c840c88101c1504102c09600f146403002545081030010101490b9900003e0a05040414030000c158440d810002d81c1c0d644c490192030300c90800e168150080d400c41049070001c21000150140c040c802c40002080309205035560846607141c46000f521005400220000010b40751220341e55480030400061114100780707200700e551145071001c40000c42d010032070078a22a4659807107080c1c603030341c488002e2030400503c024171604000b02052020700408000415080d94000810f03425031548031481d00d10304a0301c0480c2903d042d000c0c113107401c030221510110010f1611548000c02600c03038840c54003a50340b2410604110400b69010901030301c07000581c8081c0c942c0140c00081c10131440b501c20400051250b801d138000d10b02203081c1608580c41d1201405407820381c140105041c0c0f050354030800500c4418000c6030907203802c5601d42c00c1900d00800c23a401598000c40000648 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 623498794 1250 623497544 623497571
    0x204061e0603050919020d0b01061806021606050c1f0209010f0203190c03200c01090f080c0d0602090a030f03020c06030708070e010203130f1502030304080a030203060a031505040204 80
    0x30980300b0342d07520001e0305032921402000070101d41c111170207a07004810545000300054101c04018042c0040c3e46501c40d600756198548036030803400d60081011500700d440c5402030141243d2014003541c45070b0600c2622142039110191516404040b00e180801181c00d0410f02c02080e036008110400b001e0303840000c0a0419841170303980e44070362038040808051402c42607410a200b0211006003610914180041c0c40501c68440f100710411001d001a1350408082d00c9001c1d07030042007600080c4610729070428024640264691a07008203a110b900030017141c00c6103020416654121b03240d9200040001106da51213040100310340303291039811005403155403101c0002d03140401c140c2c5e01c0b406459503100a5030391000421079601c01d1000303400d07041d48020b00c5241080340d120781c851809024040c0c0b541e0320701071810000c00e1440304041100c10030b5400030414840440d9202c0120b5007010924200984c5c0d036180c5002040c01101c04c0d17070000d844030106000a400d42d07403580e00312502550003221b0610070424545e20 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 623500044 1250 623498794 623498801
    0x30e040c0c021e010527061803010b010e03210d1515090e0a1a062d0a23070519060509060609070311071a0f0709050303031902070204061e0603 63
    0x40060200d0000c0c003030b402000341031144a10b01c0c58101b21700b07182051411800720714642c1190050b041c6540c102182090030381000d00c21150601c100346031150b41c650800c8042130320b81f1100100440c40b0301c0d6440006d0708041d6142e080380e90010080d00701b000740c2c00d0715054200c800c424038044c2407a80c003100c4030140c0c000c901c40c90003007003900d1100b000120079440341c441c0000180840030344202c0d0807aa0b16845c0103d90345501c00780c0704180c4055036034052140c12050406801e081040d03000c0c403000050101e26034040e40448410981790641c05d41740030424810781840014001e1020050241c414501c070b110365813002103880c0398031910030841482143c92710084903071101400c40c0c11540189160b030000360000d209401c048044d0440031842468400b05407101218003116072200e000e0035002c0c038148030303600790b10040c503075400a0170740380041c9101e003000700003a00c034840a4418440e0002000b43c115080c9200d81c125281c1c69802041081650f40d11030500040000510a001e281035048900103190f500a00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 623501294 1250 623500044 623500099
    0x1c02030a0504050405071b080901030e0f0d0c0c0b0c2a030a32030301030b091615052b1803020604060905160b0913090b070c030e040c0c02 61
    0xc86080c24a0300b41800c4c00000d04006201104205100c101074200901101d407080d04180110034481d40d5056590001d0240c81c800802a401d82c0d1100780c1908640c1d4010a050010940d82c1c034088001d4121414000ca42c0c040c181c100036000c601c00901c160012038000f49003c98950b2100340f00501c041200306001150009060b040c0d003580004030a80c0c0028000420700b80741c030160403601202c1102e0b801d0041410b00c030755844140c80d40c1c0000700510a100321140600d500201e0200140702d104003210326204073b00d0603071080d00c0743c0c0315000c2001c4114a000328152108420302c0c2c40c0294425104841d043c00400c000207062909030714041400d40700307000281c1143c0c1180d401d5002861213032110ba581c0d400410303840100340d41038010707a040440b1518185004030b00030114036100c40d40f9800c2c1e07a0200103650f1180d00750b180d0264a0082140000f0391034245603540305900781048210103000b41800c3c0c1d620400801500d61003803071b007810070420507049202106054003d48054580c004206010181070300d214 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 623502544 1250 623501294 623501297
    0x906010e2508071b0c080106050604080d110325021f0e06030901090f0804030b1012020607020f10020f010e0f280204051e0f0c030a0b0103090c06021c02030a 69
    0xc2996000c52800b410003607801a425107444201c0200700688400e00850b400713011241c04540d08401c121840003400b034000605800c0701d00c145414a8101c100366513030200e6002d00103100074802c80205000090040d02c040d10041d40c00b102548450000200c456010044101d1040302150b0302d600c40340d0100c401d845285c2e40710741c80c0c900e0032801c04420094075420040172400259201c1c19403000140c0004640c50500b48141d450710b444a0440c075150306100c100402c0c0300b401c6500810104040c4005054020130b490b01964201d658001c81e00204c1c2c0681d050201c1150800407400403400900d40c002a110501704805000300000b080d4003070b00303e89652b01074907070482c151b0001c0c0c41004543c1c840c00b501c443c44101050344200020855000c14140c0b50129052100e030b0a107840c502a030a003d45000640c4444e00e0712400703400f842c00070407c500d030380006400d03442801c0e510780791100c00340d01a60000c4c000c95044264225a66035503240203503900c0310138802c00100b901100c00b089020307000005507910880c1c207 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 623503794 1250 623502544 623502601
    0xf06050907020129130204140307060203091e0f03070b090f01030605090105061c1107020a08010513030e15040b250f081e0a030e0d05070804050d1403030906010e 71
    0x440024040700320050781d29070f5010000451320317441480540700400c01081112541ea003204040020142040502e60220f025504104070580b51962422240004629401d2031000c6140b8070902080101a01c25809605031081410205401601c41c014059400b400c40f40c542703450100c10011425141cac0e5200c0d440d005100d0380010f00007450400060721440004695031a440300020042109581c25103520001c1c1ca1800a00c000035030030101e01c50805404000c00900050500800004002c40001c00c09400c010320340102d00c5107a611020f05443c82003580880c40c1c1c4907500d80c951000194000c80010f6a65006019002a08107103080061113482e004000844065000c0e20b448180341c0c00104940000c40e80501038034000103100b000340042e440d00d0b5030000340c8502203072080e03440e0224480c0e4101c14014144611000501b03403030125001d0300c00c00c0c0d030b28550f0000340e03240040f101c016003c10b41400340008004c01c285a000003c0c820304941c20000300762804d80b58040b15444111400c000210401c10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 623505044 1250 623503794 623503841
    0x2a0620040b0d110703030e0601170c0d03121103180109020102120c01061203020c0a060201200d110f18010905090705031018020705281b090f060509070201 68
    0x14800d01502c1a030989040c081140c0809500b0341c0d81c2d130360001008402280e920081402602020000030303016005076002015607035804c90300749544500d00c00321315120703011090545080610411010019108652051101d070b810b00650800d1500200d400300740700851040042140c40c0c0501919041c4d980680203400c034014910140c81d0603900030282c2c5100382d07484400000b0301000800e1400021070180e03001d090b010101c9003c100b20041c0700e620040840e030401e044c3c24400c49204000000c0c1662200502c0d030b5074080d82a4030009001d14502d103000010004c42e242c9060b41d40400203181c000d4810f003a030105007403c0001074840e12618040e09811a045000290200c3d0040c001160000720341825810400d550383c544c2c485841d48088550011600407402204106013081124601850006091000185488045e03140307200c10b2409802e480a006603054865002038000010380500c01c2d007840708880344801030014024922940d030040c91010f002800c518418442e00603804111415100c034450b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 623506294 1250 623505044 623505059
    0x181410050a111c020c030d0507082422050109020903070602060106020a14150702010f0b030123250309020906040207020109050f0a0e160201050108070e070f2a062004 73
    0x8500c140a000300136030800c41e420207144200050140428200c0002c01c0034030340048002c00c21100502081c2c4960040806085550711011500a0242040d180c50300840785400f0812203401307144203c179002754a05000810b4000ba250000c0c009000141c2c22661041d50b5090101c1ea114001d02ca214010b800690700c1c0d00015680f010a158026920000c070b60b0080c414401d01c0350040d4080d03d403480540c0d0741d00ba4800301c6403007901440d40b030007001310000c001171000036002c4091160060380c21045010071100041450401c43c0e54140724a40d240407207050980c80141c041c0080800307900607441001c0c103100190844c5002d000701c1e1681c942c1a50b8100e0958034000600441006610031254071107511200455100d181c50401c5115681410213180c0c222402440a421075006030003156040d0030005003030010301d1495000f250810f40a06d41042c0355204c2c82811648a603415008811f000b014008060068121004000c45640034490800100081e82c01c00038840c481c82c0c90540d126075091004000c0007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 623507544 1250 623506294 623506327
    0x513061a1c1e0c05031b0a09060317090102190f05100204061e12092906031906060324060906080a020111030702190612020906070204181410050a11 65
    0x1203100d43c400d0a141610360380040d00b4003440703a100c500042e00300c40c02c5440920f0658901401050f0f040401c20400342907454080d40c45880544140e1001c40c00502c0012591080207603940040140004038000c000c81d25004901d2140001d0030b0320140b003440c41000d1510f200b4821a4220b0b8050780f14012442c1507400ea0380c01440303002701c000040c0700340d0342e4210686810b41d006405240f4030480342103402e600e071000403441348410364292980c016240d01c10000162000200d04102095015040400a0803460302070b01600302ca030801030900c2c6010401d041d14182009021200d41c0302c1410070722a5584554121003101e54612074540a640320751240c1016500079000048803941278010340b403a00f4150740104100064050069001d00d82e200740c1000260b500c510088031441c0d0b070301029846c010041e40011201c2c01002c00191050f50380752500003c1d40c0d00c4000001c5040c1d84049028071003000041881d4480e03c1c41c0c01c05c0034401781408005549240c1e10710801d0543c540700d400b00d5050400c502405401d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 623508794 1250 623507544 623507603
    0x901060e0d020d0b070e01021b0108010e041103010f1a01020d0212070c0f06050717030601050d0506030c0904050c0f0a0f091e0e07210507090513061a1c 67
    0x5510f10780603004541c140500611980c001e880701035612550000084c5400d015001010300039192180342d044507a40000320740d0450b4040b40e840d032140d44031401d08500300c03643c001c10140c1c95882c00105407a900d6244d0000c2c00c140010b034450400040380c40005a84030021441e6180040c0c0050f0f03902d50758400c980000d001c805003d6400040503640312200700e482e1000c0d980095000c00d00210701740c13040200104034166a580c00d90325442c25410184006042c03801088034802c0b1131500c0d08000b07011520100004a800341000701642100d00307090604e561540c00e2203400501404500300c0c1082030303090440f4010301700c0d42d500c000b03c00058030b0034840320001c203015659184407003a601d8045034005101d01a51800170005000b03802800e00d4003040c0300c20490174128183c0d29600d07010b6450701091021588100300e808c041070105d1141d407284c3d40310129111003031005010381e19046010200030240d0508010304142901c0d402e01d42e0201950001207034171380b810000c1c0b454106c1c0b002ca0f50550101d40c0c0c0401c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 623510044 1250 623508794 623508799
    0x41704090509031e0f0a1b05030307030501030c050a080c1009030807120f0323060a120c081e030a0e01020c09070305060312041508180102070302060103060b0901060e0d02 75
    0x5080d00d030400c0400780c0d070302038540c000d59a00c04034101c4c00600c1c130340103204528010201514540510904007010394095000074100381701280500303058405402c104c200800d43d0107420340340c0c0c91518440250003050280002d8640d1301c060040850182000c0c4051400e864100b4010400e0706000010445020018682c080030000170010000004040f24041d24107640306200440d1b16102c0c681b0001c0000600d0141d420416081125491800b101c0c1524101c001c800512204540d5440c1030106540d84420381c8280e180001801c246420f0040c100c0d500c0d0103462411040d5068000441020901003000f801e4540c40782d0000c0107010340300c5000385040101000c0600550340c007a01200700240598004407051000b190711142088850b1405100f02c144030021005041d05050500526103840244004030310705100d900d40229000e545051030910f03100c00804002c3d5030303c50091400a4540e402031004580060401140ea11a4a0014180f5040c0e400c15503c8403841689441000707100606601c00f0707038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 623511294 1250 623510044 623510047
    0x2070513050604140435031906050a060e0a08070501081815070f020c030a03050415030f020703020c01090e04150525090609060c110103020c0f010e0106060e0f03060417 74
    0x44d104011501c0d2521450044280d4401c40b01d21004a603140d64240c5490031100c4864180941e03103c0d007a1041d80d8000c00300740d640c00c001c10f405102c100000c080c140c0206d0703801030740a070001407410381c0801988800d000565206182e290780d2500b03640d0724102805810b0100d22148002000f007844001510010703401007003166000c201201507099801819150718001442424241070302c4c036010028800c03124010303002005054103a4034014064041c9001c2d03d540c8800244104500900c06e401060701c030075010340210b603104186d103400303075541e03010360074003804901c0c100d9000070060080505e09200b45d4212031300708200c4901d6010403000300341c0208000003200c0d4000071585030702a41c2081a170751102c69250804424104403003d800015564400000c014082e21400d00043c1c041e40b0b03500d003c4200b030a0258480c06895042070030311b00c8000c2c52140540c84d0504090081c401500005d00b00c8485407141d1080d0302188060240c1203203250541034141d0b110b0302c0450f001441d00c008003912100c9040005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 623512544 1250 623511294 623511311
    0x90c060a0216320f0103180203060a090c0806160e06251103010903120b010207080a0605060112020c03120a021909080d0203040503121c0216030207050102070513050604 74
    0x1140e90881c1030f0000b9071500850743e28500894468081c800c880a81c98400c451440c3e07615002807030308031040c0500d6040507220308580c80c506800f503044044140c2c0c01400d854041ca03040c100000101207014050315200b0b51680d0029400f01c010600500a203000380700c0f04d0315025040c105030340075881d905200307400800c2000201c0310328880000307e2200310981350341b6003145261414032064602c8040c0106100c1d074075160f07500c2d0010b508419408684003180c03d01180c4a03600c0e10044c0c3c07c00e01258480c0f0094040c0034650402c010b25540450b02c215000d0f00c1f26006405151f50a00c103e000303036074031245a580100b05940302035590b40d61980d48816410f001600d001d81d84402c040c01d03590780c24007180115807403000c140320a03041804000070401c200e10045037001c0c40d207000030f9690007041480458203e8005501c41c01184c00c0720140080b14403001055503150805103800076880c0da40303442900140513500d400714080d80b0105031281100c80c000c0031401145801c04c0e40c0340080c54080c1039a54826610242c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 623513794 1250 623512544 623512573
    0x9030314030c090a090902191211040b0603071101050c0301050603041e0203030d06030c1e0303050703020c0319020f0103050702030418091e022103070303110c0601030b07030f0203090c060a02 84
    0x600b011701007204010448104520600402c480b24000042580045140c18443c03000c48a03062005a40c00510044110664502050007800c0414000303411483c0042000041c5404c80e00d103c0c03132515601300070000ca6440450f06e100c0e070b02080c016154089400c00124000c1214805105680b0034014984c17064035041f58002861507200321a01104039481c0d141c20402e0191070f1481000a01e00c10103400003a040412100300c034070070306000003000d0203030108075030f42418820080002c010501504581c3c5040c1c40d9010424079140100c012031050a01e01c0c500001d03035109004244c01071455400031400e00b81840c0080c4588680d003c40104803607965a19000031a03109100e5900d000c01e4900802d610401c24018094820322251041810f0300d018200380070f0410000007100d400319014a000201c3d0714030450066507034864103615010302d200d100e001005111300d82504500031314031910100300c59014030480030280e0200b2a84126580c0092286000030b081100c01085442e0143c81520b5006150807038 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 623515044 1250 623513794 623513809
    0x603041211100522111c0f05070905070c0b010504051902040b090901060c030f12090b0a0515041a0603070314090d09050409020319050102190216050109030314030c09 73
    0x1146280341e031540b051080340b60711001340440035103a081185688154917100d80c40c2c982c450480181c081c0c3c0d1040c00341000d0040120030900310650183c5401d00030901400d02030399400e0740b03000c0d42070706500e0200420707015401b411a1000e01c40d48640c841c54070f80c4ca4401000300603c1c0040401401e440c0e0041d094035401c0542c4000d10107080e40c20b481c40c0c1c07189101024000c0d6000160016014001012000b1010035000301e01c400d81d040c803e1800d1400c050340b003c05907000d00038441d0010041c40070343c0280010001660083c6101d0f5260030383e90264103c0c1182008291120f400c590790070003003401c0105105007000801980d21414038100860390707201c15280403441540440d60701d1581c0d04403004200803242c0c401d01c0840284002c580c01d2210b1030990700065210344401c04280141c842c0c060030078042040a405840180711580313a00f000e00310070b4610280d103411441e4a48015001d0340e81c80811558050300255041d2038069640411001c0e41d541c540402da800901000d000c0b803400d02c40d454143d9039814 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 623516294 1250 623515044 623515063
    0xa120b010207091d01150501021209031905030a14030610030f181202070503120405010c0201030b060f0405090903040b070b0c0c060c0c010e0d0f0509060d091412090603041211 77
    0x81381420443c08610b40f02c5c01c660b1035400700140003254100030815aa0f001544100c0d060541a503203540340c001c280000c2c503100c00030503612080708086156005010001c4094103402515843e0044242100d1101c0c03881c0340700c203d507000e034008200509444194480c1d400a080015450030015172050440e42d01d481050800d0011954410310351140400c03582d0600c0b404c0010181034000f080361b001d40b4144110a0700540c000e9904100215050030250f83c03094000c1c50503d0380180c80756030b9501d005192419203902a0085500980348038000c522100000811a0b0440d903141c030346141059150f5859035950706c40a040e01c0c0d288003040c40340781d402e07035010322005000d103c801c12002e03034459102d20070a080d611404503004154003c00d000f802480e4101c0306d90001c1c1000f91032704a03900c5110780d00140d1a406507a021070700301480d144000e4100030f00c0b802190407200b009411584034444121048201d4490a400c55410000c10701c040750000301071400001c2c51440e682082203070212000360291278140600d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 623517544 1250 623516294 623516321
    0x10031e0207110310090809010c1a0c0a0e01020c0607061e050a0501170c0108010510110f0303010f1a22030b07120b01030b01080c0703090b0403050d0806060a120b01020709 75
    0x2e42d120741c82e529003040021090503061009110108907601c4007001c0b8052020700a06010483c40c82e030080100c086000600e42114000050702c0b03090144a4260942042425070041800e1204d4040d41d50b00005003030b011458014011840d0150b150749030805004a09020700d443e26401c000310b5125000c40c0070315442a80e070703940001969803601003e069140e03440c0c03d8800d1290082c00b107a09403641e0202840d07040d02c400342d402d14003001c214142154210410232082c9100c0c06559102d1361440d201000450484641000341042e0907281c030020400200e04d5007075031201c400b003045402c42c3c0c0c01041c0300201200c8000009800c0302c40d80c85e101c440d40740000300c178098009441e188001491402501c501c150000f401e10f0100f04c2d041c42c69002a00810000e0320745040c115011901e030042501ca04100d00180c041c40c1007040d01c69699140055035405a810900c0210381960f000440500308003060b03800c40441903840210310001c04148100505200300c030303513046002c0c0340c01c0403400034401d000d01030460044 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 623518794 1250 623517544 623517563
    0xb2203060902010807050c0a060b060c01020a0309021212040e0a06030c093806090307051503070f4506050d06050901060c080a09052101150510031e0207 67
    0x242c8001804514010700c0c450a101c400d000e2924105e500050080c03115900c14800106030005000080f00c9001c0c00152040560001517038650783c0382d054100c090107074800e03a00e004020f8805108140c0399203900003c0540b46c003040c0020000c0600002409410200c401400514652a42c0b00d0042508440d00001030070383e20f0f1100d0120b02d1078061101080c02d00760300800d0a03103090241001004445c0500c200d40300d5000440c001146640500c00c0c01c000700801001c03403004680c114058070790f5803c111201c03000301d2501104d04070301c4c0340140c001031004400c020b00002911401110b407041d1241c009403e210b0200c1c04004000420030400400010709265140c031921b4a010420328030030740d4030765000307240184010030042000c0c0e600044016040d0380e000c41f0041c0c4a00c2c40d114211695055036208590050700c03c0004a0010101d0200c10f6064000200910140200d401d40c000a101d0b140305186e00014942046c00c00c0c107201c1d034442c04c2c111082c690b031015202983c4100105a802265094407003080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 623520044 1250 623518794 623518811
    0x12182109031e0609010b09060402090105090907030504031101020c0d12020c01060e060a170607050f07051f2405040f0605030a11030d09060905060304030e090405060906100f0b220306 80
    0x400c1250b034130400400081c40f240f64a4008114282c1c80500814011307038000c00c00d007506a006000391400c4c40c3d00903100340d1007843c16200c011f010340f5050302e0650103d0b170340700c03102a50540c06008840f031503001a0020300141040f24001c80b0418100301c0c5039000942e083c03100105580003805884000c012028140400b0b0400004110707000c401d603444624440d0250705400c4ca02c91020900c15481134150801ca52144403200e41184248100c02c40180240070f010517210b0224442c0001e200c010218180c03c01075154490404c089288498043c9842e9281d104810000e61505800c030342c041200704040802c156603130b4004039203042c0604400301c45410411008680d0f0b170500700101c02610415140c03c0700c04500e404d0028020310030a0040e02c1c0140030010028091602954040c82c24842c044e003140300c80e15113814590b885950603202d00c01c9900456000c038130b451000608100c10717103101003840040b05240041904590748800760030140701c2e481c182d6651000c0e0700c848400000f180600030104a040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 623521294 1250 623520044 623520103
    0x60a02010e0c1210050406060f0303180504050108061501020f0a151a100f261b0a051c090203030f1e03040c05040f0f050c1218210903 59
    0x40b9074402203000d5241e002c00c4600c2d2043c0020b50340720a521500001405442d01d081c69406000c107500080e00710032045200000b003680c842050140e42c3d142c10308611100303441d07504000641d00213205040443e84654042150075021003e0610307030b01c90500440700079248031181c09081c0104001c05842c1c1710710a2500130b901403404c0c0a0340c0341728a41d00d0071407800e2241840019075803260020803402048050111462002e0141800f90f504402a100c10700f5080c0450783c04800905040300d21001e442d0a1111021119a6032000e4400494003038403443d0400000080100c0518095032011080b19101c000c001c0240e2014401011403184421607135640b02c9500c1c06800e442ca2203202e515121847c20403c01c804112425420000d44004a07000b2814092070010f00028020000b040c4904a00d84420b1140c4140150014a200c15441082c03040340d0741c1d850a136201040e1950381107400d940100c02c071032104a4601c10740290240c0c03442c21103400d001104000c80d191094012880c28164008050404910f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 623522544 1250 623521294 623521303
    0xc17091f0234151b090e0106111203090609070e0106050f0a02011b0216060507380406050618040309140109090906090201031104030b24060a02010e 65
    0x84001000c0d80380035030701c2080712084a040308421842e011801d5040381c81c220040046404650801c1d0514480d4908400c400024007500c15a4150303140c00e60b045440707803402078405404844134118001e40c3c44c0e2925070156a080449440c0590078001c6a0004290001d0036028501800f0810b00a00c01450040202d501e03011030740d044494140d014000401c420b40d40030080b1048502d00402e5541c541c4a001010390142080c000001b000e015090035000003550b0001d001510504152501c3e55055a9010207a07113074400c0c084003030b084a00c0054550b1850031000011113843c0030102c0c1d0850f0b00c000584922040c65000d690440b40c164464080c4030061402415008200c51840c0224100d420300d554050500030f414407454460140400080c05942e0090b802c40d8020a0a46003d001210840c5401e90003400b2548049010038502200800e48002c400186c0781030301c5c0e006c50320380c00c10f0304c81c841c46841c0b510910680c81d0280007c0312004900341c850b04c000e080e14064940005c10540007040302542070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 623523794 1250 623522544 623522593
    0x4020d0204260f0a060c0507050a0332090d03051c0501030c0f080c040522030809010606020a0210030209040b0d0f0311010b060403030309021504060f18060806040c1709 74
    0xd0740001e00b80a043d03400070a15030002d0390710841c000303001685c0d160107842c140640310000e449409144041018181c005001501501610b442c0b447c81c54200d04070720218000e0701803102d1188905000a640740d080405512076020702a041503414210540b8030409000034101072601100d4072400100104201101154040d010b04501d1694160901462580d6800c100b08240e1090f41c0320b4002c0760314020741290008030902c607101c041300d240d005410042e104607400d5558440d25803a0a01c0000d44510104554400070350080014042034a42402140a0b412600d0003552080c0d541585118035034502000120b80c601c288460100b1400504000d8030404400010940b00d9043c2080c140b06584c2d0441150107803a80340c140010f200301d5500201c3c43c40c69038440401c840d520001008507a8903000013000c80d19100d00c0d52070b1044a2007200641e10341968511410f4080307101c0001261042c40e09400036109401240b03010111049088a110360f4690103880f94025a003042c14011120820311810508 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 623525044 1250 623523794 623523869
    0xa0b01080f0d03200d0e0f0d0219020f01120204080303180607092904052707020a0f030e0d020a0b0a031815050415092009090d050904020d0204 63
    0x45200c40340100c90b4070080650329140c101200017000c400c1d42c4141d074400781d0709241560840304652846181c0340d6494500c0c994902c0540f280c0f1401255240084000c416005d5000d0f03d608240507100c8010356682c44a0341180041940a00002c14540810409140b08280c030028001900f40c01c02d00060503d5006841c95003045140801441483c03004124100c05007151400510707690740640402c60640201d0300100d6000c101e089143c1001a42c4c0c4201c014003003080280d00e110f54a504c0c40030b0b82d9032800030303100601402aa40310440480e02070b0544d1001500c1c0031f8005044034401e540001c43c401c690380c0140710300300004a0000c0e10300c0ea1510641d00c0d448410440021108466105c03400134107190311032110010745507800070b410850070400d04810009a50340034854120246025200800c114042ca10340545440c049440c0385010500b1600506c911005004000420709045400e54000c0c0107103600140c0030080c9003035036400c5100500042084012120f005a03031440b000220f407810280207074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 623526294 1250 623525044 623525051
    0x6020312010b0f04091401030501050f010311040213031401060306050604060803041e0b0d0519112712010501090c030b010504090c031806051b0c07060503090a0b01080f0d03 76
    0x8100014041005056444245020b501e039015a15100702c50704c160341001101c1c60900d01c0c4900e10358821450941641d2040000b0f101a030b4604001d0b00c0083e40034800a04a40e038190061b48442c00c01d81e00401100401c456034a0800303031a61102c50050400c0d0f02d13100c0050f03558541c20400e00c0b04034824540c201004550a1043c0d03880c00c82001c3c0e907409a030007000d120442450070041c240c80002c64003002840028082a2502104050720700105811510318618401d45841209010000e12454000c0c241c0d20840c1c0c3d003001d042c2c2845c0c47d560300c040c88421144c02000300342340f0415900c2512022102030010004240341d81014030300d4042d2141404038105060074034111009980e004401c0c6c60035501a2000020021080e841c03c50190511419040d907583d0b1490082050040c41c1c0c000c1407140c900900042d0748500340b06d100158078411500000499041200c0612000b4850001190040c081d0b004440c40a080c6449401d1000000e9103c1c000f16413265a10100001062100308410041d07400c042 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 623527544 1250 623526294 623526307
    0xf030f070210111b01061a070c080d0518210c120c06030103140c0604090e1b100e06372f01090b070203031905150d050a050d021006060203 61
    0x886040c050100c0400d0044e810141c190f8502c1000d40c0420000c04284580b54180030446081421355846180142c03106040010003141d52b00000030b111803014030f282d81e014039015a01d85400d48010b213200c1c82c158007030030711840c080301c510201c41446080408000603040c02a001010821580c0600c07405070312903003042800242c19681d6070290307411641c0150912038554801c040480c102a84407950300d911070000b04000c6856416948121240740c1e040d030032180c1c4019403040280d41000c0041d2020b030311a09096207480c00d24858515a6000680903001c6411701c40b40403840354241c840b03010081d10742001c43c10340c0c036000340304001c0c2c013010701c0c0e0b41c0d08200928516240c2100300502540c10710b280d198003950b450301d4100e0025805140c00c1030b0043c06000d15030500703aa0003512984180d9556040740c8001503007061001e102d00c81c00b40113450b42c80d03500848102d013a090041c01440b4031003c2c0c0e00c074060304904102154052000400402c1154041c0403440348440041d030449149420050441d401031245 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 623528794 1250 623527544 623527571
    0x7260d09051c0519140609060403090b1602150f19030c050a2304090c090e06010908061f08060903040914010530030f07050708060c04090b060f030f070210 68
    0x31044c0c03c0c0300c070b08402d503081c0300381d41071400d5000001d1980e201144600020440d0300f07640480c4050080d482940d070b42031020396510800100340900c096403018034a82c1c02d001030040c40c0080030820540403240d5014202140140d141c04541c2000525012284070003ca01c007040790b061140e40742820140c100345080c138990060042c010244161034150074003241008152071105542030b1002803110075030910001c10b0744100200303100003034440c2024841042010031410b6002d89400003d9940c0d0600800b041c0d0758420584440f80d80107225070403202003506000c00c0002040c400c2610030322103040215034891802da174901c1120003085100b003911142d18014881a60b03440c240b00013840525032580300211054054800c1200e00440a40051000003401160f41d0017003005001454000d606030f841103991540804e844810480700742802190802c400d200c2d444d12a400820300140190980d030820440c0402c400c5a5401503810b94000070b56041080459039041158a0344022004d41c24407101803032111 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 623530044 1250 623528794 623528803
    0x306070c0b04050717030a0e15120c040302180919080d05091218012c1311031023011e1704080705100c0207260d09051c05 54
    0x1c115103414408079051007010400d500103004907120603443c80b4a640e140030364960041400a001c03c84501c4407402d0352511003100c2010030720a1080e246460142007449503001c500904242880c9418400030001d41c40e500f405031103070102c441c1c54440e5410a450f140b440c040c090a40300405a07443c500c004002035481040e54002d41d46c00741c0200f0789441d0040c085042c0200c450203007501d0600812034982a11450100b6041c011081c5c03170f800d58a642045001f11910003058840c90001100302c54466030341045440203110410740c00b800203100401d4008c00701e190340300307035180039080000140a11005003683d80c802658000d205140c0c505071810300000e00200c0c0c40c1c1441d00c0250000640b0461181d01600c9070004140301c001c1c91151601d8646042205c2e50091401555280300f004e5034000f40c0303002d601c54507024451580052402e1885e00c440c1007480f1310110510328000c4070141c0031580f610000c01484540300c48030b072521441181440c06200d100c000d80548610121640c00510300498030101c0c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 623531294 1250 623530044 623530067
    0x303021c020d110a1a0a1103040206040e1906090c08220803150307090e2505130207081207030b030a080f18090a020c0606090906161202040902040302040b030607 71
    0x300b0810883e82c600c0c8031030604044040180c50401030407500d4246081d480320940c03180c05e51440406c030a541c014900d01e4640001c660080d08100104006e10403005084605a80100c0c90003002d040c09403c0452041503416a600c803041c469207680302a1851a04102d071036a0112940d80480d40440703e80c02c0001030401c40401c09486200008089007520b9a0070100403407640300641141c074016900c0c85280c0051050003000201c42c050b80340742038107039000700b02c0346405c16803650140520710b400d02c010440146141d00c0c42e000d103a5401c2141a00140c8101c0103800d2018101c3e4480720b4a20741482c011301a42e00e404400740c0300350050381c40c8000040c4418262813803034949604c1030340c40350019440d0140712b1151420241c0d01c020b101e4100107a9250361703001840030740501010341e007681d1110024852800c0040d181015240c000034001204144d451001f00c1003407005203401e00e065040180311000703d0b0300a4100c002c0c00c580020b82801941054094440041070540c01040da500e880040241400c000c035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 623532544 1250 623531294 623531297
    0x60708040503071101020309040608030d0c03180809030c0a061806030c02250b030c0307120c0f2f030405150a020c011404081603021e01050a030905070e100303021c020d 74
    0x113100040c0d9200704203480b001000a0410064203848464041d0303241c02210321000d50505041c1d821408500c2801810035203844060483c00c8040300c0e40e200d40c0300f904425221601807148055088043d0341d1140d0003402407600b9140c0c3c20002d1400c509444d00381005809c00c43c141410b0030801505258001102601106414030350500d21005003840e241e080302c254003050f0f444001200744038480b0850300040d40510b0443c0c03200c048200c01602100191801c10f4080000b05440a11110803e03024a001a0a819203c0000c00c020103011000d2445088240c1070010b035030380081414452401c0401c6000d461101c01c410380741c2800c5009500a54454032544040d0400c83d003541349148800f400030650300079140038826203002c40c1802c0a070503003000b154401030344511009004038480340e070742440a022605041c2c0d5907500d000c15841040d000751030390090844492040c03400001b100400200c0309030180b01c1100004542500c1d50600900e850f00100d000302ca210158040c0c07250154000500a4a52409 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 623533794 1250 623532544 623532563
    0x105180709150e0a082a010507030806040b030a050d02010b0108010f0317071a1506030708060105160602120402101107090f0e25090908120c040305030c0604020306070804050307 78
    0x160314203d9a400d82012003540000c9840004640400017041c800c070320362000e09843c200170300380012080813031500154040c0400c0c010400e850210388580150350344510007800c0420040c08590200f80307403c0c20b00e1820703580c0750800c443d10070350240d0a016010345403009181511255040c2881403854910602c40100300b01d103907040046003040c00d40140c076602c9802c814013140390110101c1c0c00c0c41e002d5048501600030100d4940004041c0380c4802030381c0c001c4520790342d440071a6684900544444e8841d4040344c050144404643c2d0000b551400204660054201e4580d0942002c2c03051209103002c0581b441d00784800790380f0b508901c400000754001110349101c00840e80e040d604d80800010f01c0300d844000701c580111501810758030612404103440d01d0144010340341c2c040e6601d2005c412aa003032080141001c0b0101f04007410f01ca40343c035450341c10080203c1c2c0c80780f400e031f07595036910324551001c1070142058104100300001d5160a00c480755010001d410300032154a8645e42d6291288200c281c01480c2040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 623535044 1250 623533794 623533829
    0x30f25140d03051b1b0c0a0914010f0e070e0a0b070302161a071502070c080a0b090105010b1e0405090124050f0a08040624090e010608150405030d050f0105180709 71
    0x20058003241b004040c00400c030407134859050401512000100d41f003c058088000920901803464000440754500121810368841e004102c540d03034060032131141c0c0500500c03004a003e48441d8004d05140344660028890f884043d00c0140c0c0c01042136100d4191020a20740c480c4026000c48100d82180380d008040213050b9091660060007801031440c050706010381d00a021800001c000740000701c00e4020310030b050300303942d45490240c00c2c0c44090250030780d40c540620030354620607074840344844004024000907042c84d480741e011409001d800d90101d6442c814079844040280340103c0281000d84c00e6142181c5010450b4040f0912445620382c0f660400107084002014441113074408041c0049002022041c040c080b698030307000300c06500898007240d140c5403178031540140500c9002e0444d003620001d8150110740b0184580e455070018010f94450200b041b01c0851445203100c4d0300d2150403004010b14065052005000e0954260018080c41c056004240a20660040080001c0301c141c040c45802c40ca8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 623536294 1250 623535044 623535097
    0x121002180901080c0d0213090b040b041a071e050f0a2c0f0d11030609010510090b1c0318060203190201090c0b0d0b0418020102010e030f25140d03051b 66
    0x2111082c0540343c9e401d83d80c144070800000b200c54500442c090944074030000240c0203ea128890250303140000303d01044403105811081c030601001009080c01d101c6d0806d810341e140610258402d01c40131300012510b540001c0c5822000300c18407040300c500b030503580300c62a42002240003030400744149031148000751928002c2280760803846440301805410358500f402c014154601802041e186c42c051101280300c04601030361540700385107240318000c019030714000103601414034900d10010300394200521920a5000d103070f420710400f00207004540c010350355007944000c0c8140d4019600ca2071300459041c88400b40104900f0101e040699503141402644c600d04902580000d040c4500500e0300a418190810360009480320704100850003a0000c1c09140c402d101e50648901c107540c0c41509111041c041c124020600d14140100d201031070100031040041500d4020045114504108095000440d142c18055143c02990b421008584401c00c24105040c0210501c2c09003014010141c0d094410020264 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 623537544 1250 623536294 623536301
    0x3090d050d020c0a0303050402010e0d05071206020702150d110f030402040f06180509070f1d060f150c0c04060807060513030803090d0801060509060306121002180901080c0d0213 78
    0x180c000f0001c43c0c02d03a403101d20700500a020215001c1e404620f40101c528014144140c00050b05079100e40a06141407d001c440003081c40086429242d2942c244110700050f1130f161503008486034140040c1c1c1c0c4416030700d070301d0300182c403412140004001800c1c44401400c01e072000a598001d54110b50102d00450001305400050003d0f0340072408403040c880e80340c40c1881c0c9030352000b40598000411703150842c0c0c4482680000364103074414405040000b812800020b510104a1504550010114240380140c04000380746803c4505c003d06003a90002008040c07a94104060744001400740e40a200c2c451030807001c00c0d2241e90340d100f05028800b000684e6010360202c42c0445002d50343c891146034807400d06002055a0340702c60791f030304000704d1881030010844500980640307000c2c240c01040280340d0f5569406201403000e0100c1c45520b640706001c1c2c0300086030120700150a24151014101002c0841c07141040f164400680c07114440b03400041031401a6150f0b407141200064040c1c034209002d180c030740000c0004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 623538794 1250 623537544 623537557
    0x901140a0605010314070c0f0602070524060d0b0601030e1f0207031b0b040f020d0221213108061605030f06010e032503050d0503090d050d02 62
    0x100580002085041040381d441a4103540080c1e07000c02034010050b4a210614070142c504a0100d00c50080701d40000310a500e01d40081c92141d2809400c105159a07107500d05004c13983e50a803d510048c103a002d40c06010400e190f48070408a4a18615036419116081200c402408190402d038031640350a420710010000740c21551603610a44444018a121743c1c00250042d180c01ca000520201086d01249840a080242d0743d0f00141c26035030076260340e0791f00200c11480c0708049800800c20403080c00941e95020799520102002c5007090400b58107082446e060110840850003e1402c481040b01003480c0352082c1e80d0301201c070488460a40014000e408900c00c1d0201d81c0600700c00c90341c50003052102010405a008440d540c09410381d281c990001568240001c44240b40850700042c00161198441c1c00209900c10028081c1c031500c0580300c09a5071410310307083d80780203140d20382c40080080010800c50380b049041c0f42e1800c1404c500b0694200e50b101c1012043d08030800c50b0104000300c1c10407003039048805 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 623540044 1250 623538794 623538821
    0x801090b0102240921040b090414190501151d150706061508130f030311160b010801020f12071716020f0c01090504020711030a05070e09240901 63
    0x20300c40f02d2250f1401541a0444543d011381c000c3c405207034001e0341c84601d40e0308250a02c14445003002d0401e001d8140e00d411101e00117520031b84501305210840344050308640034003d801c900b8003001c3c00c1e420030402a01e80c1030703021192110400004618482e0f0004005200d44510514110540b18010002e40000d028844004948900041402c20480d0a41c8401c08580b160f200c11310780c0c41c4c4c560500351034a0008030351100410755a2014100084c8000f0710b280c2e6080d210342400284159044c13008103598120070f4008003181074500e144401d21518010032401801080000d5207020f1310448011154015004022060001d09001c1000d4600400c1742c0818207102440d0089145800b031007684040d41401c4514016008108070709007403031000f080340b0354a410181c4595480e00d2609046c0002540300081c1584c4403000c40c00c00010543d0180f00401c4802d015000034105142030a940240d00700c0081c05100325940004803501509044030a071200409072241c05518590302c094506001d070441040100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 623541294 1250 623540044 623540083
    0x9110909151807120606150c080a020f01020d02070201030605030c150706140403090302040506090403050a0f032309060a060806040b06190611101a090402190b03040b06100801090b0102 81
    0x2419040540a040391a4003c1c00d05021b42ca5a4042040e409810440f4004c0003941164000020400c01401008103a1080c41140c0c098032001500a089800c01c10000c1800c035000a180004d560307260148a024090881c00f802c1400c001100088880c4840c9441c5080148046115000c4c000180c1c000030f142d032590011020107141c5854003c05c10509800101d200718940000314444d800c003404903c1c45075034540c850a1614904800c103442c122143c4119074109510f4060b08000c4131207010190b1040480c910001040c0d0829240440c14510010140d085c0b0b02d2400900700030004002900765001038101e0f031075400c103807100b9010500d0504030700102040d80c45804000165282d000101094869003141915a500b0140218401b503800e001c009001d56078084a081c0315a18cc00c4542c1604107100401114000300f141c4810065055564403411300c508007c001c100a00003c8406541e00c000c046807098210810600d0241c0980320602a03594020340d92403014086900800000c403c6803250003814 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 623542544 1250 623541294 623541299
    0x130e0c03060411160b0103200312031b0c010903031d0309010c020d020405100e06010f021c09030218070905040e06130206040506070c15020102030907031403040b040909110909151807 80
    0x1700c90545080c4021504190742034501e21a100e0780981401403170f5402405080b9242c819041c101c2290009411821003024004118181c04858130081001d00107070000030454200c181000380444e021100103405a48120303c620310060f038040125100c0f03034800d00704003210391414008504e4050600c0e42c001d4102d0301e01010700034500c001c0d103240b1049038111495040307d6540d0100444a9913180322110015070301c0340360000c015a203690900c01d55120907141160440d507581c0c0000b40d032103110140010034100d0000500130203d50001480d40600404d031414020340800c43c007450307907440f07008040d0307032028415400b2941196200800c81d4000c1000034040c64580c1441d062241024109101d00000511014440c03144c050040c02071301e124100240103010070600c0c2d80c03907005c03c241600c06604141d0200b0000825489105c90150029041071100015844120303c1c20010950005a00b14480c140410800c4012000010b640401004214041c0032540700c00401a0341424002c0d0500058051254007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 623543794 1250 623542544 623542553
    0xa0b0d02010203030112083105030c0604090b18071715060403081c060b04050319120f02011506080601020607140405011b02040612020a090c05030c03041401050c130e0c0306041116 79
    0x6205c4c1c1c00700e040e03208e500b050703980c0d90805903240040e50406402c07140c10b0104000a140c40d40c002c0010070704c0074040840602c0c803180d0013015038108441c000045008082208000000503180c0c0ba8000011101c100c0c1074600000000d0050283c1d1000603c005400a034146000c051001c0764456058a4041070255681350b0301c582c4025003003400384c40d009103d10625203807441e03914482030020f603030080c004148280c3c0c6c580045030b514450030288404c0d9921680314003402c14008a010008080d02c0c0d5880300d903420400002410400c02810b0b02040100d103e01000c0e410803640c00319030485000342014900c9c084046401110009082000b035402860308034001440304007840303a071000b81d01c02c03540c500003683c0f509291001c5822210040c0b0020341c0920010340341c075a00c140155009070068848010484a628005094078000c4503846101000440c030842680c510494102c0907000c002082215440c115000c10801e0100800b01031140b41c851030307010b0741d290021003240c1e20055100640b8114003108e041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 623545044 1250 623543794 623543857
    0xc01090c080f0c01051809060114031302040c08191e02030103050d0207050a030302070b07020f10030f11071703040303061802040602070e09030d090c080709050a0b0d0201020303011208 81
    0x8295949008480103011290301c607104480c0c1d40d02da07000e42d801b40d0304051000d10112810040440d4140301808440d0a64100c101014502c2a10b5088045a43c400d140c0f0500064070605450082400181c4050040b906c0b403500c1030b900808605500000c00312000550004003c40404900905507c000004418003201280003c02c1c1c0a0b50b80803180c04542c0d91007400b0f5000310340d12010307005030800102444403070032080052441a0004042c280c03223100c040c0005520a070a9070300d40c0d01003540c502940081d240a03001e80c0c0ca0018035407880701e050008649451040840d00f005140700100d001000904141c000d5000c0c0001d420b60b52080b82240046200e060000d6205000d1100540318130100041c0c49281001403a02c201107000c00795040c00003003607000c40502001c000031100140e00a501281c110f104210007401022502000301e100c2c03c081c40d01c1000c41e440b40085902a80040030402c0160b40c0010403241160610b0705c0e40714103905035062500e5940216a0b0200c440413240c104160071240b40782 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 623546294 1250 623545044 623545063
    0x50f0705071403030403020907121b05030412030b130b0d060905060106120911010c0c170a0b0a0504080a120609090b010e070306050f010e010201060b130f08070e04080c01090c08 78
    0x50b41c00e44041d800700405a0724000c500c0000d512240c1200001e04540c816a40558165400603000c13178803100e1603a0201c05440c0400368800046c10120410081c80b041d450492042812402e0801003161100041641010440c465896440d00e0300c41c90410f540300c0001540c01150015010409040703540f9001c0e0b1582400c1c4140000208603002c2001c10b03541602c41d1540060303200110301000110038005540840c0f02c035806649a59039400300141c1038803002d21508140f900342010307041d80b090514005019410140052a14625060420002451110131201100301d6424011007028061000c4001b51980741c000d00e108500381465081008625014a03058400c003106607542646d4400b001c50840d40280305455005150301c41220480d406040c45610001061002090a41d20303800740714007541c0700108240071501401d00c200003105c003517400c61020300510000b41107400e2507c006816440340140c00038025150005a010014000354407045600741e0041e40302c01a142d54426264940f805070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 623547544 1250 623546294 623546309
    0x501090b0705130905090c090a021317100216050106080c090601021506130213080a02210601030314040e04050d090602150f091513060b011b12050f070507 68
    0xe401259819000c0e10594002d0507a0410b1a03507054500b8030b019000d00300c00703010084680180034006159803900b070001da1145110b241d000d6a11000d4003074202940704c09510a400d141c000400040d131943c030204074041c6035880c00e03102503107032040c00d01c401447c2d55140780010040d6180c400001912400400ca0f1101d1000451321240d155440307000690f1985070030804034901c010f8131800a016407030151503410804001c1300005083c050342215544c1d541040341c00405c901d41c0b00c210004110f103400c0c2400541310980000e030041c03035001491515030701d42060000809001e0100f19041811035030b001610001c2a5034480404a8246401c0c1181c0391941c80c1c03000070001e4007920300800c0b0140001400811052141c3c0004025036070701d580c3e8100320201412042700d81c05031401c1000041e07901c00d1658043d15903246510581116440c00c901141c840d407039403605120388280e000003042c0a40550291140c0c00c0000d0601c00c0603480310407034052040d60101d50701d8650105000c000d000d0001501c0c026035452 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 623548794 1250 623547544 623547563
    0x30a020a06061a070308070203220e010b0c0709090303090f0303020306010905040612030e060904050421081627090902091e0711011b051914092209050109 68
    0x1240f00d0714050540c0c00f0300076520103108111a0b40064030564000c0d501c4022481602d08000740002501300d4903030042410119101d00790001d006040c041e18031b003801082d1050546103000c0309000201e441e10344074443c480a8640c0c9070985c0013454002d030030102d070f00e541c4518100d09440790b501d0b000e0003d400513035041c0d00250b000f2002080500b400c2c819801a180090141c0d03289c1400d80c7c2c0c08582c1d46040e600c41030b400107001d00043d140c5071101e0042c2401035200c0c1c02e00c00b8008103d14006407004214685410800c9061001d02a6012200301406100305180c40d288901014400c080c6206194004085080e2044444001540c0c0907942c060f409840c421a5001c40545461122008541410f2214800383c054034010440c02c0d4001c100e113140202c4c1c40400850300c100d0074034507200c25440034a404030100301c0c000741e205014903115142315040d80890414440e10303800c81000729518040c6218040c01203502d444502150010b0203980045284108000d011070001440d00302d02900200d41c0c2203412100c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 623550044 1250 623548794 623548799
    0xc03050901150b1e040b030708011a03040b0c0d021308061501020102070809060c070306020d09060f05090a06110f13030317010308070b0c09210c0609030307080318030a020a0606 78
    0x200c8030b01032070881d41e40200d5942040e403013410310020809400c491000c180700c02c000008203030900e00090b40c82000e10791568559503240040800e03019081041c000401c0200b0810840083c0000e10356a0f00304604003401074480c0700d040b00b036900030701c80d040c400300c00840c030510006140b6600007042c80c0318010000302c0000d840003202c0168280d01035400b00a1060005120003012800c1a001078002c07210b8203412151300c0c5a890310765008992040c3c84600c191520b4001c0c0c0b60500110380106440307041c28001c00c0107a403270040c03030781500c032030380008000c0c181c584801d442c1d40d1126040c400d44000c901658855030380c98400028006800040d032008401107846200010040007030965050b048075045854107140c0207095603100002d040080c04482c1640c070078001c2501d240ca98462400b02b54042c1c134002500001011555840d001111041c544560800c01100f650340e00c01000340c83c0c1895101141c981c50f0f03121101d1460351811284140e140a01c0082034245205d80d000450702c0d55035004003030401501c1e8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 623551294 1250 623550044 623550071
    0x10f05060703020c0402090613080120040b0703030e21030103051b0105040b0d110406030e0c0a12150e0a1515150807200705040518060412020c040c03050901 69
    0x345241c0900903811808003642c41e0304264009000c1031034000d180c24a069540220644004030f96041041d16a54480b90480d80e84207810403040d07410328110a0608103450080007200350310a00600a0406480d002c00b500e400d0f00801113040e002d4009141900d980559006001d5030350030074413040e140d40c814030b4103840c100cec020191100c0b40300b0380c107030340c0c842c41c00d824144010076540c00100c00e44071480c0d9844208900c424480c0243c0040d00c1c40e41e8001c81c50368400900289081c04218059200d4600c9010421804814000c845000ea61040070510509200c500c02e41c000c0000c01403104e142e02907486110104040700c0c2c80300000c1503041d9400c024001e00c040d010104681d45004548110101941924519005500d210b034004110300d0b210342c00c5841c6130058070b103040f6030864081003039110300b03024841441d050007415400314044c0c81c081000c42c4040c0ca05c5944440c0648003070844100c01e2010130b1128800d204900400802604c2400f0250710391400800a0400f100c41c1c4c89594030344580c404214 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 623552544 1250 623551294 623551297
    0xc1707020102011413020607080d0213090b090910090203030903060124020604020105030a050c16060b181302040c11030f03181903140c01090503030105010921060b010c020303070b010f0506 83
    0x215010b05c8050540d088070340c05d0040607480076100381c1d0006001e004640b40b0546a000400b42a9040000c2c0490540750a5000c019070741c035015580c1c1710b01c1c42c0c2d004220b032076600015408016007000002050402841c00400d040d07200791001039406018400011800407100e01601244156420341c1030000c0901d014100c0c0c03a840c0a480090024130100086446524137801c2103801003940e021440c0f50901c18510201101580c0c031080318a50340742c50402d815803030403a0780c0c0e003440007240707101d00f105140c000191180c160320001300034400c55035450a203200c0c500c9400d801021407000c8084a80c3c54918083c2422581c000700d07100070010f2041100060015400310f48900303040b180804400d01030314140d07000c0c0c038022004126078034082014800101000700c2406212805e6000320040c42d5294103010004041c114250400428084044072400c284030f41d503c01559a80c0e08800000364582d02d2200407280c6811754040a0340c140300101d1401c0c18000302416240c100c0e684850185581a82c80050107810f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 623553794 1250 623552544 623552551
    0xc0f0d021e1201180f0504030e090c0a050d150305031b010b0409030806211608070e0112030309030210050103051006090b030c010c02030a020303030c03090124150c17070201020114 79
    0x40c0c4407908010000d0103510344240380348034820040450007507011400300c5d040340d104880641c0003c116038400a05800d11442c4076070001c1d801c244082c0f0b05000d40d84054058821502602c1d800c6554080048044e04010387c00d102070340c2c1c010203407070f5a4500d0302000f603c200c03c19491484254a06440054246024403407401c2d07659264446008540e00c41d01001400c02408510181110316100d9010f00160240806604260f000319010801801c042800c0c0c030f4000560041c1c8940a0b40c00c2c0144107550b5071907021651981e040c54003160111561030102d04080a001301d10b004203007010001300401c0380128240c80c2c9615610000c00000355124490741c10b403003402c682e107130f010b80110300d20917000d511a00e1580c2c0420300280454141c6403641c0c0c0824030b0b50b4021038000100b140080280545d002c0280281c454040000220307000c070720754000e000703c1c508800e81305030101c40144c116081035040c001e840422003d5002109102130030003c401c2c000c000da0088008034015460000e0b84617044000d039042c03500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 623555044 1250 623553794 623553817
    0x40f0e1f020405092824051207030f08040801050a020c16060801120519030305040b070f080106200706030209010e040e122101060207032f090c0f0d021e 67
    0x12030740c44503680d400c3c10303a048000107000c44d001d81c407030405e21107824003548008a0b03c0b45003421030303030318216841c8201c00410340000d48549084041c9041020000071a1000d4a03002003130001008c00351300d085c00481c4902d0388421015401d0108001c040c0490344d014000c4080806e05690030b5981e0243d000000300300034042c10700455240001031120040d1880e802040c04e03c00c1d01150110500414400c0f1041d44030130703084002a488008010400411054081c1c000030181885044520f200c000078114410500501040100c001030130350b170300980450102c80050f20f40d000c1d2428541c03941b000401a40c8840c006a01148039010a00c0b003500b40780c4209080e4001c0340014141d80640c55038950500d5011603220610100850000c0484880d4028802c2c0203105a4008001d003d28500c2c00d03000c3e01c80701501d20070201e0261038126181e01441d54071000654000c660500717580e911840b00b54454000c120034071168003004100c0302a00e040d164018149081d0f007194142d6118400381c4180e5040c4140d094540 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 623556294 1250 623555044 623555059
    0x10207090b0406050402030c0301050316031e2d03031d03073e0102070e06010e01180b07030e090a060803040b03070e090a09140f07050609040f0e1f020405 68
    0x440241d6000203000070004101040031680c6100080698105842005c001d001c0040104040d190402400703c5a204889062051510b0f41d140d84a0600b1042d90750010706200a0115040098505a2054128a9203554000c045070b9003c901240c90107030408401080c0b40560140d0080785ca0000382002d410944021351070304019940d0310409811074202520320380405600000700241084500150241e840005005041440002854001c0e2a403103072581001a00c01d03c005660302c03200300c0c5070990742801c08918084000103204501c070142d80c03015080c050701041580405a000b009000e40010450740714105031203501c03041c801c8500600c02c88803245e0081004101d2460344d0009594400380c0c3d828034000f45405a0089111a5811110040c000350f0b11040d1501b0410100c400700e01c0340354420014402800c061100f16504d0341c00740255442264003244011a9603601d030846080c8603440e442c00d20540303000b1840d10384c1d9000c644500100c0344000039400e120600c40c602c295002c0b230302e0051486 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 623557544 1250 623556294 623556299
    0x608091614040515211002030138090609030c030102030705070605010f24030204030c0b0403060c08010b04090f0e0a03091a0a050a1b0c030b100b070b2707061205090c010207 76
    0x407528418403281145d1075014208170032030140c8092010b14000e000200201007213501c60a122940304012041c010105061f4648110381034441701d0503243c200f20141d9545980c2c001d1880064602065264050341c90b40c0000304000500d0791000252585500c15039040c0a181d0b01c9468000b140900340c09244400203071100140e10b46201c2d100151008501420300524198883e110429159020780100344455000182082000214820640340c0051072610142a505100e07604035207204510a080340346032106c12008050a299001c4c801303494000085404040c401d10b0054803140141c40381c440b82c0c403100c504140328448020b08840f440c28a9580381458002c4005050f54012203055800c0d20401400705154009170080c10084043c500440307800110346403e55400307100c00740c241c200102d0280103025500c00601d078480542e8000c9200300b0201c00580c0d44490300c0c1441c580340302018400788681c6800041040e080600c000c1e501c002100309014680e46c4511701c0d0303601c2038841c00c01401a840300c0c504 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 623558794 1250 623557544 623557579
    0x3090f04200304030903030e0f0d0201030507021608060403170c04122a050906010302040e0a050a02070b0112020103050a2903030417030301170d090608091614040515 73
    0x18290680c1d41050300e01907080722080c034000d402c01c83d01100032031540c803410f106040d00f00f1150306d404c00c0c0440d103862182240d440400d1198100304070090625495002060300c0701d0003407050301c000c0f04450100520242d5680c8165560303045c252420741c085120354104058040c0b82c401168801ca042007041854249400d0281039038610a00c4160341c12413074100400750f1b14855042c0c40c1c1203010040c0f06016000e040500b040b442e036801400e2141814410031003044601d9004218983c80604100009065550703c0002c401900c103a1000802c2c142c0007600114407010741c5400d40c01114001c0e83c081125170f46140440088030700300c903045241c03080840d000303843d0b4805d00d1a1581c40b5010203003d490505594040802e10301186c8140804c0302d400210041c81480005c00700c54080e08180d2004140d0441c401402500d09072490051000304034074030b80000c03c01c3c003040101d02c00c07002e00c2c980142d4207550340c0d0802c0e280112a00484602c40e03810030002c14041c1101444030380b41440000c0000a0f0502400740 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 623560044 1250 623558794 623558801
    0x70e01031101090b030901090b090d0c1704080d05180603040804120311010216030210110f1e070b04060f1a060a03060306060b0306010909151203021c031d03090f04 72
    0xc50341044000c203400b10b11380c00c4401c06503016180800c000304202d10070b071410702034240c0002e0071100968468400380011f19031008103549525040400906200740c980040f888038800d981021307a10348501c07031003e2502e50f03202000f4216041011403e441021000d420070079144405c0e07801401000b401d00040c0f0982050800228803284241450322030300004100e01d5003aa08500d00e440f1024084e5004003040c141c06122025440c02c82c48410003c0c00100b00304c0c0d1101d0300481038002503c0e0404a800c8080c20710f40c960f4400014810720340300362100490302c2d1080449108650845205007048109d40001c850f5001d0894400600030000181184e81024400310b0b42124050004145e00d4080020114000d8402c107006040ca0708005503036480c00d84005841210b50fa8845d16250745401c003103c108012161110080d11003841001c02007404a0400b01d1500d603403030a103410310001d803550f105902a016030141d074140c44003000c0c4030400c49516104a840c1c1c05845c01d204d0b04000c61407019912840c1550 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 623561151 1107 623560044 623560073
    0x204090b0a0c050903031b07080106080706200601061803170c061008070b130e07090602010c18050625141b030c0d03090b0f0417070e0103 61
    0x1002c03075070b0703032141c0c10011100c441a807c0c00c412503002804100300812180b8002c1c025a5213a25500d40c9440c0d540c49080c02044888144442c600740480e00301c2106002d032000b0301203581c60007800360f4030a01000b050070700c2c070f804100000c00040c019a40c0207100c4090b03098016154105450200d00e460806017405540038a0046d08024002c000510700703060390f05d95180715490740c00800d260f0025000355004041c00e10314000c20130070200d6000d024203048841c2d55009010780b0365141c1c416145420248845602c1c80c403000c0381446641454002801014901e1004226510031003d0064019101d9581110f101401e200c07200b0078000d040180c0701400c100c1c0460540490b01a82c0025903034004208480d00440d561004802890700880f02d120090100707001469031001000e00f0100303154464000d603140e1a000c00b07120758542000294444c203542e020150400700e6401d5481c0c0d0722081d020314 = true := by decide +kernel

theorem cover : BRFrame.Cov 623381294 623561151 := by
  have h0 := BRFrame.cov_init 623381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 623381294 ≤ n) (h2 : n < 623561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
