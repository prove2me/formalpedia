-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3932
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:05:37.571088+00:00
-- url     : https://prove2.me/submissions/371d49ca-79a7-4062-8fb0-ff51bba5ea98

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 707014388 ≤ n < 707194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 707015638 1250 707014388 707014397
    0xd0b0a09020901051f0c0f0506010f17070b0d09140d0e120c091602010b030706111504021c050c0907020102071b06020a02010309060b040509010b040608060c07060b0d050d 75
    0x9106006204840b0416080300b801102400c5950700c0c4200e00100c000540da0203880c205100c002c1a29040249000c0440000c0207407043d24000320704a0341400348035054400425a03909444925594035030340b5078a0344240041e092040003965504409500b0201b071440c010503058500720641d820075032508411000590000b00e1070010004503141005903e1a141d5090005001200d01040054070200c0f0240c464200d1411500c1d045400364001e40210030b0140b00101a14a400c2d43c0f0f9a000e080144908281181402014140803805000c0306a180c02241c02900110032600304070740000300301c00d01c0c50007680c3d684a103c481000c699100d90015108001d1a400540c40740041d1501680101705d0000312070141801000504c025540042d43d000d226070240380101d00d0704007604150006103006a00c261b0407501304010400d04102c150030015800070191003c102c071913500d8401c01d80350031003519050143e5004000c043c0100e031494100c545c20010080051210f102c140d910710345000d501454150118 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 707016888 1250 707015638 707015651
    0x10e07030b0901060f0c02121c0237150506180906040813030b2410051e091207031401060b030f0726100e0402030d18170604050706050c0703110d0b0a 66
    0xb4460840301041c65070700041c100100b1515680200a40640c40c000502401040400307202007030980cbc04c2001d03500a120801d5408503e00c000025060032030300d00c1d0065444c82d2520150300320b0f080c0602c0c0700d07090344000f030082c90316243d0300c0c1d03503d5900403480c0c50016118050040007260030305220301e0082e4030240b00c000100c8030f28040030095048808000d0710a0751091140100207401a045440c0701d0303e07556550b0312046d071928292859026000d203194100c00d209034100786074600000d44000303590180b15461601c982081100f401c3c0c650b02e001d00030b803100c028004070303074002c007084d0403c1e40005841c20300010b002e244003031001014411000c2c859012200c0d5083c00320b500742c5001d201000d40324040065840f85403613000310b0341c1ca5445104440401480c1c3d20408034020418440c000a0091904440000c92046582595503601640d040d070326402031260000718a4000c4046406820151000e00720662035501c03229080407000054a800c40c601803051000500050703042d40c450603a000000030030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 707018138 1250 707016888 707016913
    0x330e0310061e0f06051204020103060906183b070914040b090703080f070f020a0617010f0602070512030f280f230403080c0303010e07030b0901060f0c0212 68
    0x20001c45500007490f60701994410700855074803404581003001c54086032003840d1101c0c80124002d216a62221004620f001c3c404030740c00218094418003a803445809124607801d228007882c40260000030144100f0b100000c15041a17260140e592038803030f210b000d079019a40c0d280ca0341c0061706c140d0194a1030001045080004025401000e590041d10b4640208031060540c0d85d40300641c854203482a55103a00407070b112003042000e04c0c2480b94103a000c0c0001c030806a85640140c4540b042109100c003612004001240f030310484014001296034a40c002c5c0140d524000c00d200c4101840c203007040302404104842c0c521174980c04020031000041860342901e6511140000790145001103c540810200c10080e4541c1035002c400141c044c10340e0003480120000d01c26040c1882d1040398001094038401103450f45042102102944c1200d8144044075050764030321204604a40e42080b030164071810320360050040500c039480305084446107051001c0c020ba25a00040c0c2d0111010062500766801031806041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 707019388 1250 707018138 707018189
    0x5070e1c12270b030612010b0d05011a0d0f0b0c1210060305010b090a15020a020904050a11060a020303011a0c0118060c181811070c330e031006 63
    0x180101c2d08411a10402c0c10030111000501c806001103209001d2a01071741040c003020f51246441c2400100f9032003083d1a2441d2007406480c040c2e48100400c40c035000503001c641850b01c21070b82a5a400380711140880390513500e13020b800304045c050f08824407050189070380310104152114020315170054615201d0f85000e40003415658146c010f200040c000303115801603501c40000c12070540c1e210a424140301c0f00301c104103c1c036100c03103000060752080307c2c0300034042440300204000c1e00b83c500030210b00e01c0e66200081400742c50300c51040620010307403080004201c0d00000c641040801c06000b42c0385803601200c10001420b580c6a1049040c0607070402c091304040042521990801d8007040c1054803c0100c40701014040c1c090500c50807850190110320004081840d62000c11981a01c1c00c046031280d415045c03100400e1110302a68a84c0c10000d81020b000700762010384454241c0b502140042d0b800c3c44502c04451102d402c4490303a805203d200054003222200740a4080a80f00503042200c0c4d550f00c60a183c1d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 707020638 1250 707019388 707019437
    0x150e090703060e060d0809030102040e0a110301120803061804151a0604031104090618030e1504120c03061d07050a0501051204110d11010305060405070e1c12 69
    0x1400d1500d00001041150003c1c000315034031000494144035041d6103070414000758802d02c0b00d00382c2d141d44002000320b0301c0340d0000c1c8010b010300f00044081241000e0101000c14500c400e00408140355520214000016031081c0103581c03080700030700100000015958006840281582d00303c0e101066681c070401c0c182c680c0d06c1880c0181d6544c140115140300d104021898030310542c04013411034a071400014450f41c5498000071061136102c0010420829020740841c0e00005580017140000c07400a0307039070076a01d000c041240c002100c44410a1505280c0949810400d1010078110341d03110790210700002059030f501c030303240d0026030580322070b8200400c40c20210300380407140e0465881110340003403e202c01c0e41d10209803101c000c03286001c0d0445031501d003850440c0d40390f40740000e644042900c4040e820044003001c0b4840c1100281c07810b2105442d2601000151541141c4010003c0ea1410880c80c0626001c0c00701d00c420a034808244a04400e2529a01d0048600045500210748051119541178041c044ea45 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 707021888 1250 707020638 707020651
    0x4080c19050606091012060b03070902040e090703170d0e1608120c1b032802010e0609030d0318410d0305070924180608040605040309150e09 62
    0x20402803421714106294a14140580f5001c2c6401907400c0c020400141c0c00ba201f0214000d0841d0f00071a40d840c040b8001e0f50003402840d8090400a000ca60a5071000446000f90b907403004e4482c0388200c3c2c50100d4190707904483d001070456615148a480c0405051200171640c90b0980006010a0304000c290340c905201d92a4910140781e00300b024900501e40441d10344803101c24403039030f00c1c9230605040000c1d25080e20f9261000c441c07614054000c40d620305070075101e02a28800e803030300b00c45107440e0320800a05000e10718140750181c2003440d03004c04c1d5a10942c0405d180741d88010b04070715030003900d1701c552100202090f21084645600615111040080084621102d00b040c644220003000c0380c442544542c4e800e0400c409040c0c445000c551618080ca945c0d0b00503111076816610600344181714440d101c0328038016000850400a03648002164415580c000c2d15096203410340141c03501c0e61003100500c0d00800c2502002103802d40440c0c0701903408820034408409a4a4150284541d020081521000742c100c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 707023138 1250 707021888 707021899
    0x40509070e0a020901020c15030106080105010c080706150914041a0621120316120b031506150a020604052a120703080328020403020f0904080c19050606 67
    0x20084020501c119070391000480c040580c070f8041c0800142e14168009a02c0380d0303c1000100c0d040c2902c608580035504985c901d40d0b0b07904582e40c0c0c40c401545d00c1c0411800c0540302010410585c0b001c0742042e00700f030716803002201840000039a03a500b00821540a0380c0d00007001c41086003800306206a005022003c3c8000192250030b5003000d4000401301c20001c03051800e8040300181f07220740940c0a00c81e100c200c2c0603019209a591070b208a5007200501c0000d080340108107400c10003450000315200f01e0040c248060001e10300c2603420382ca80c0070100303c000d005960200013000410380480c552406400d42070b000ea002030000703041c03501d019030400010f0b0402c00320341c8210030b002006141400c080ca455140c004d0f110301c0310400095580700d041a007650030282c80c20200205100c4c4000d4091b5603121441c0d040340c190000b00c41c442840b8000d9205502c0065444002031164446a1414801c480e410910650a20f858441201c81c2d20707041010350700b603a1212141c4109440103000b400d01629070b014404544 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 707024388 1250 707023138 707023153
    0x14030705030d1e02100f270c0b0f0f070309060215100b1810021e01060f1413050412031410060f0201180b01031b080a060209060d0218040509 62
    0x2c010083d501c0c0058a0529811503640354098500a00400d4135940400c1810f01c010f1940309001d00103000360071145401404202e4803d055500c000340b0803d051540300f00100c86891920035905000e030054402d44008200811520260a00c91001810742a00c2170315143c070b07034518084019081c007441c40305841916608038200700701d0582d0713640302106603010389a0403610390418500a10240300d0042c0040d1b041211903603600c2c2282c0e000034150b242c2400000c409460710304407203034190a0321001c0c410640000382e80241800115200c10810000280140c0403122152001d12150241c032000e40d011364508100c031a034000002d9050080381c040c810b003640c24055500300041440c2e4852a980315000410940010302c0380014801e42204030902e01c80852181d0b00300d014100601780f94030070300c0111500c85840000074200761001e41140200d40b403c06c050034000c0484d03119800694820041ca59201c0020014000d4a1810344040c10a280f045020020381c030102400340003c075000604503080b60f511940 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 707025638 1250 707024388 707024413
    0xd14060303030907060c15090c0305010b0111071715010e0a050a0603020105070b04061b02010e0d03050405060103031809140403170118020f04030602070f0516120b1f1403070503 78
    0x16070801200c5140c600300d0420146400c7c080c4011041e50641d0b138801381007414200520500d0111903040d45c0c00f40000b0032100d12248015600242c0c4806070084d81d8028803401c01000035000f003110f0b41e082c180c00c10303514481d00418903602030010903049000509441814004240000d100d45070f0300802c0d55408000c1c560558002804a00480d40c00600d00380000d000030301005030f01c1d0000c414180c4040b04040318955080b9011380a0215030300c07840e0080c400d940050020a20134009c1501560300500039043c07690954500302c1d02c0d040c000c001244031189001c000a0102401d114201e010400e007940c41441d420903103402464411b89410210101e210523005104120b920308500d880341100202c0142c0e207041101d034000c4503000381e5001410311403000c00c0b94410701c117504103510780700c0d4402c5003510141d0442410072a0b00030158040c209456045041042c0090b017503910003608648044107080600e50201003007030483c84903401615141c00703200a040003a047c1007180341d01514088000d41003803108513 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 707026888 1250 707025638 707025643
    0x101e2007060203060a0302040612060b24070302010209031009210e010c0f06020a0c0b0a0608030406030e19050c31090f0506040b04111f050306040b060d140603030309 73
    0x1403409448594004042040c580d240d254100082d94060030520025640d448114035481c080001640c0d0b031410705850350303194940201c68003c0b00e09082c1441d448181291440e05454100c810107c2c02d540d420000030f4500c2d54100000150150a542c004c00d050241c2d24001898000c3c085100442c00b49164400c5c10702070300510742d121011800c1c40d0802041d0030791b003401a0b603281c001801801c05840054215034a650201d03070301a000b40146c140300625250040e013142200e0b15445411b043d60014001441803511a1700844d06010b810800c0303600b143c0c1400c442d10003403e15841c0460355980101341159031420021002d03030840c051070207450750340310007420118a43c02c2074400b100050341e902c800290400c0b140741c0074113109981200459440b40303480d1030b080003000c405030341c155a41d400c000e403410034900e000d28000c5031100c1002d103601d2032040400030580703050f0400b0b000254010b49038581da5002c1d803100750282071403000011307010591a00e800207000e00d0b20f00160140d0300a4008004005601200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 707028138 1250 707026888 707026897
    0x100e01020606040507020a150204060e0109030302060403030f0609052503020909010506030601020a0813091a011722030509100201110328020c030903010c0305100e09101e20 76
    0x40d1404213480d0340f2420100d041182801000b086501c0300985036030f191181e40d002d88103503241c0341c58031520141d4510041d54180c0c89803000034016840413002400080c400d80101d0b02c008010000851007545405007201030702c2041307810b2162480030740c1d00c280300d04003003c1043c0001c48607400c0443c035001480000c01d1388035030140983e0340142000004680d6507442000760325500d5410182907900e035181105209003056461241d10030341e504002811007001020701c0485003000c016114030714150541c00c00440c43c83c1e00201201d00c0c0a03000b40500f12004d07036030155515168440c5d5905c55552541c10f041013013210030110128116898459020f01000c4100100c90b04402d00010600b10560f0380d04200411446030321030104140c0c0003190304148150000044d007040b0300110004e00540a038008202c0450358102d5031190a2000480c041011502d62058a50001003030300503154490f103500c003043c043d01c06038a6001407210b810804007038808002e118070745c04060f100206068411002c42c241805014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 707029388 1250 707028138 707028151
    0x1403030a0c11040203040b070e060426012007030912020306040f060906230a0c0f0f03060504020a0c021903080a050306010c020a0608150105072006070804090902100e010206 76
    0x80701e540300307000d01201540703007070703085000a1007555240f8007450320368070b0408280e64001c0400e00340c101000040c900b03030054901752840d28010804070408140c199402d80342d0801e02c98442c0d5078512007002d101141c2812101e0f104540d495943d07698000b4680104203981c90380c0031103074090240204600503900030a80941184d042281d04407001c06134103004004008159000740305c80d00c0c2001110365007840b0303003030400c40520740d207011091943c2d501403030429201d0320407503c0e000a0300001c11002d800d010380700d4629615103c0c034000171615180c0012a0490388403c0e400d00201700540000c104514008400c00e80d54000c14014041286c91982c0300d07203c0e0300a00c2d488a080c8100800056211b9110388212005660010b00d803803401e680c0c034031002c2c101000c185c40228407089890000005940100e007150080c5610203000c0080c80f103084a43c19940d40302c624119031000040001c40301040159004e8070191441400005000c061441041866a0380c45103010911000d020002616a004aa25030380f016 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 707030638 1250 707029388 707029397
    0xf0c010507150204030c06031d1c09030503040e040c080304080a06020d1103190506010908030d1a030f0114070c0206160309051207030b060a052b020d03020114011403030a 75
    0x10182c68805a0540e1610502076214800b20300002440200d4680e00226034154a04002c0d205012003544004450b4013003041290348482418402d004000a0050414800d882c0c42c81e0580c1d01c83c0d4a541c10342d07000313900c4062000c031000e0920044c0005003250b080100454401036103081d00c1c040806440e658910b20261005038041070b2070070420320355040141541d01c00601541d40786010403c203207041d0110b41c0f40f109594603180c00075541e94000d6a00ca020344d49240000e6040c24110801c03480030344042d03007203118140841174a2000c9514200410b84a9040c82000070810100c04499544581402011001007086840700003015880c1c2c641100e000342c0b20001058003044850074142c2d07e890082c1e00c80340d0008141351130040c00d41c1d000b1808800780c0f403180fa04690551620410804102018040c4507404000600c0a03030381d2545200c1c06105003c514250304103443c6003074001407082c019100c8140c000d40d45030301046c58088c6548003010302601028059010b0080b040c0046aaa030040175030150600 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 707031888 1250 707030638 707030647
    0x321022508090d050a21200a060504030302031f0f052209030f1d06040b090103141009050105040501030206030f0403030603080a030516020f0c10092301020607020105040206160f0b040818030f0c0105 87
    0x3041c090249034449600048280401d0610384cd00030001c4d0700c02c81d6031603600c074401c00c81c800414036441d1740401100c00c01c10f1540c0a103070070f217010448491420400140da40701e00002c050700014131801074140340c3d40262100100d41746214000342c1180b004004480c60301d0449001000b107907a85000703503025070302d039220301c44d840300d4003e00107070020041e00414a6164400310100040461450b01800c103450940700144020b0360f80d8002d00003a10000e0100035404041032000800c4400800e080c13981c001e000b4500401c02fa50340342c5a8541e15442100b100c0002a121010420f01000400800d02c00702001d20041545446207400c40391941d400701d0240348a01c0b0301c1c040c8031031021300c030300d80d0900640b01544601c8401d40001c00c4103000d2441402c1c01787c0c09405080300080740d2034010700c20184180d8000d07082c0c6140c21000130000c1d02100b280c2c0d13801ca905009200720030010803d0096002d200e40e10404c142907880030110b042d9100038640c0c48200b0f10070b40c0401ca2049441c0408146c540c0d1140c820f003030103030300c6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 707033138 1250 707031888 707031947
    0x13201908220311070e06150310060c150c0509181b0c15090106080d08010f12060207050109050f0c0a0605071104180321022508090d050a21 61
    0x5501120b14140f00510034800e01042c1c1d10342808000e4000d441c1144c160421001d00811010603006c02c039500031a8081d12481006a03170f02912006440c1441001500308140a14446070121034805403001d00250001c51800b480d42850ba4008030746107201d03c3c030148140741451024420544126120412600c04280d50300400d2007000015404007503c8403a4421340340080000d402401030340708503400e40c8074802c0a1022113000e0460b4a040e00c89442c0c50741000c030b00b0b2620b00d282c0c0715104007088428581c05c001c0140416400e1162442030391041d40904842c1c0442c2c40444d2421401c2865a8032900f10041c0820001c1d4120088900c0d86600c441e00500078401000060b0060484800112900507080030020030150720461603401741000b14004154a001190342c00c0490040406440c51502ca413210707102d90800012072944203502c07981d241c0f86444090310200d0300746001c107207045429a000103060800c00c04140c45404485003040310760110740002990003003402e1440100c411004440c0780b040001d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 707034388 1250 707033138 707033147
    0x160b070b0c0f090f01091d0910141602030724050a0c0f110705031203100801020906070f0213060b040303080906100e0c0d110c0c0f0906132019082203 66
    0x4205c1c1c7d0388201e02003000380310708064080b802c8840302e2542c0190b00c0c0d4441300c91820f104110000d410f00010317000c0c40d07541c0114100c01e401542181002d502c42440003a00007100c05d01b2001c0c1420404101101c0101c80c929403505950001c0d10210209013890741c10a80c0551110001920501070300d0400074245818030b1729418100d0f9074010395054020720710410442c14403a002140039041005d04805500c2e903d10840e800c074018101d00c1c9038010320422090303010030680b0890003441c1d80004c00c1c8200c1d06281c0cdd0360123030460380143c0c029070700440003180400038150071803940e561080318a0301a01c4075141030b031308500041c040e9000b20f40c10442208003241c040441d00096400e41044024200103440e060241102030750440b001d4480c040c0f10b12003c048240c1004180c80301014030203052240a5251501005101c0f00985024181550f030361401c001001c082010342e0000550001c031451750740484c00c0740713030001c0310780290200103003c00c036000d2142c15025001b0398140403124014851030b030181460100d9 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 707035638 1250 707034388 707034407
    0x302070f050a0308061e030c01032c071712090613120b060901061e03022508070c1710020304080c150f1806010b0705160b070b0c0f090f01 61
    0x14094402c40080c0001c260300702c062540580c1d02262034140c2122104145801c2d03040340d0301b01c250560000f421502d402e5010790412a4510031009225068400c120500d4600a52220b441c104580c84070030204035404200030080942280400130780680943c070b00a408107449040790881c09014001022150101d0080104e0003500442400e0b5400d0b00041c1001e5207076000945a1900c600c161400000f2551b015041401c54001c070294840300802244505400941010380035612841848085409800540b20b50b40c940501c074030444c030345a02c85401c1c00c0750381c200250000c05007082c2c8000700e010700b407400207160840a4000c440140c4e40b40d0300c0786400303041801000c9907242d1500c00c4102a18020121040b40d0784070310000b1100500c00d94400c200100100300e60700f840c12040c2c01c05801030040010513802845020300820840780310420200351111030442c01d1b4444490382c480440c008041008842e00142c00ca003501d01d00340d080010582c01c0d0744584c441c071684988141401d84051410341d01030007400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 707036888 1250 707035638 707035643
    0xd080a031407111608100b030115081f0c14030601020304050616060c0e0a091d0307031d0307060e040203060d0516210f020d0302030f040b09030c040e0d0302070f 71
    0x40258101190060140c100e4001012420b0013049602144240386000e05011101040d0041902521310712458005100709000240c055403520800268102c03100d4805004140c002c2c000c0c000c3c642c040d502c0c00f4000c1c2c11405048540c0f404c00030118202544540005aa115480c180d603a4075141c100050740385101e00da000c0c0380c1240c4040743e04c0d41220f4001d01c95251050249c1002d210040741d40700c0440d6070400d0702c0350480d4070120030807081c016503006600c80d04022001040403c00c49034056003c1e071850704440d10440c001149446640c024510000030300460420507001050000d061803405096a824540703903500966000c00040c00c20355940c03088002244c0c00030260740383c29040040f041d008050380c1c05808500c615506030550f60ba159031420054450b08410071011031040341d42001003400d80402d041d021448288600c00c0003000d03140c014402840c000004c00d40d608044824581842100c0c0e40c1d16114510b084400b04550301b0105000c2d07440821442c0043c0c3e90003403031521880003001880c01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 707038138 1250 707036888 707036921
    0x703081c200702091f1404140a1b02060412050307030f0c180b07020603060108041502130e0c0a0f0e0402071403070318030807030309111c120e0d080a03 67
    0x212011080c01d54000c1503a0750082d68500728580c1d403034130170b0740d1010860540d04801c0c81604004100e668034840c403501003c10014408a441c8500910441c903003541900c004c0607c82d601c03e0002e404034144c00e03014004080c240094015031415844680110300207000c0c860500c1000000291294072a50004070140016201000001c8100c00c0042064401e0080c001540185d954040740d5010040240c1e40d65990081c0f0b01e40c40c5903600001141d114070043c1040f00c1804140c501d01349190399500180c103500c880b20340c04c400710a00d4107584000c07000026000700d600300c1c41049410480da07030040441c1c50514143c28503019020f8980007040c002c0c4150309000e40744200c3d2100d240c0580401100920280c1e00a0765a07146d00300d841d50310300c1441281848000c0105a08000180000c0c0c001d1b0062819a0300505d04a01007411036008110040c4c07104000500e03042079010030804203d900d000e0488a00001d20b400d548080640010480801864801401c12280400c0c2e0400152007030f0807241013840f00c8100c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 707039388 1250 707038138 707038181
    0x1d070e06281d0301110417190501050609060d20060d0f0515040204060f0f050d020408150f090c150c030c030d0c0c020105030f0411090c0c0f0703081c 66
    0x50041400707010b00c80c112044070758011616558541406107038202607803444554905440d044440d1029809169100307001d0051840c1e10380702c0d0b840e04110f40070080c010b4001041e189000c0d000c220741414000c02d650303c01e032070429150f00421075001c507005000d80d40440c0e03588000bc03013000041150185e1060103402034107002c03c10410451941040d80903040020303803181040ca00340100000da00441c0200000a48005102c0603141e2050140d070301c060711141030a030310f03148015220109a13805500601495030242072040c9402c081408100d51014aa0720030001c20b040003050389032509002c00d4501d100303001c206180d140300c1e5440d0701110403445d0342004407582c4042202c507a5869400050180d442140f4054500054034050351405594550507035546140d0750755005607030090a000350081e60308407040c0300d001c0c2c020f4990000d1703180104808031240ba120030414540600d000700700c00941550b41c2100c0d00400c001080001520b052244104541c03030550200401d003c02040c20401c1c280c011014101e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 707040638 1250 707039388 707039467
    0x1805060a180218181605040902161203050c3004031707030c020309010f020a020a03030917031c09050313121a06090a2003040c1d070e06 60
    0x600601c0700c40500d4a0300f0a008a0520420103e0203040f01c0320f241048020000600d45890300c49920905645410154246600c4402c014201d0704135441c035400010000c0c5503a001d000c2d82074030098120b40315103400d00003450001d44211260054850030315000079003800044070880100c41b1200c03200c8a640b40c0710514030b414207008100480d046030b038031980d8402d1408aa02a8464040d8441000080d0004e40c501000c3c0b000443c0c00507000404241140642d40940340140d883e85141f000841c0640d951100c0181400500d82c42c0940317910381780307445600400c040c00c40d85840340120311092014420018012129003801425441081d400c50440c40700f4220205020104075640b1103224041d954088440c01c0d5480c1d400c1ca001c5040d100c2075441414900003c1c40700794940c00120800030300c1e80c04100b041c1c001045030381c11500241d9007240d00860640090182403e41c03204071008800c625164105070030002d801a0448105054040c0505000501c0c03548190025802001a020591802c188070071003a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 707041888 1250 707040638 707040641
    0x1003090f0501020a0915080708040c08060f0f0703060e060f04020c1207060b060723160b0918040b130501151202010906031a0112060f1508060a1805060a18 68
    0x800181c0045202060046445110540c00d06c405804588403200d051715501415075260030000d108031000e07215203601046050003070102c0e5000e500004102101820240200ba00305000100101c0c00c0624000b020069038030400c1c0c601342c00c01c1c01607070101c1e1a280c5c1000807901a101f541220341c0c26100ba20450314400c035060300100302e03a601130001000410148400c000b014441c02402401c0c142000101094136842d80c8481450742d001c000459842005410301006003550302d40c0b0244194602050021b01c50804413000075000100d2014800a403030940d80b441d05400000d0102e03041c0120b07000d00740d020000e007580300368101940098018103403907403840f448103000e0000d001240042c2c02d1800015a56000f4060051031588400d90071140b04c0b25240115240250490413084030f6456080005410703044021840140a5002c0c0d181400ea5240e074010380103410192100d4084c0304544000c0120301c000c0344050042c3e2007000d0340400c4940303800001a0f90f40103103401c07203425042030b07003130031700d001e1205 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 707043138 1250 707041888 707041897
    0xe0d0b0c070227130b0105060307020109050d030b090a09121b05010911011101110d150f06050417030a140a03151410020f15090708030d140a0209010e1003090f050102 73
    0x11280402c0c0d2036503109259849881c03513004c02000c4854000041c00217103000d10203142c0c040742c5440001503032070290310f0f610300d8000b0320b45240d0042039442c0840d00e0142030140ea02940039024000c10b00105003140e440d1844907030b000310f001c010000e0840000501100e24100811071a42100c0284166461410b061400340b400071111408110002d984107405041806403003103001d910380e800340c141500060200050310300051600d01291071010003244600300302040402030540381d0b842030380751400c120000030144e00400810403961300500c48001003d6012030b0b00e0003950204c04038180c5030360740c80e902a0058107941e0203019000401a6002c11104c0500c4900e00d05140100e50b40d8504042018080e07885004040000940f504000c60142048040400c070a030490368807021204172558903908182140c03c441540200d0359290295804c0c40183c0d120132581240c1000011031030b040c070280004e030640e140c4507070480c041c400c1359520654841c069401019080d8110000c03101e00c031407500d00f85000303500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 707044388 1250 707043138 707043199
    0x12609011e09050d0e060c010513021c0b01150c0b0702101d10110f0705060a3b010e011a031501034704050d0e0d0b0c0702 54
    0x3410207240e00051a030041c40030040d006000340c048002207000c1107440d85070744100b960b08410300300303c588803545003441003030b00c1070b1960781d80b1582410540c410000b4003080c190480c0c041281000b82c19010404501820341180c07002d84032100c58040c1050207440110135003034094010401c840402165a4010031081480c900c413442c2000054060517041c240031007410040140d59101c03815448902c0855030025500d000011030241c00c0c0180f0303c41b455501d51144c40216480d0304502e0500c030207040680a2450512140b480c605001c0120b10000806407a1507003407100c120b080c500500401d050203600021811454070001d00840d0003043d050300511080214040c002d11402800c1e052011404d480203050706c1d03101d021000b280f2010b42422400c0704600102f60802c80c41444107041d05980c0701c0310310410860402030520149401e0412074100a42600400103228000c2490315951b681c0014000309203a0000c00142d20ba190851900040d00503040025001588031814034030500d01c000469002c0303c0c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 707045638 1250 707044388 707044421
    0x90e06010608100501030b040216080a0306080c09070806191203080f1003173a11090d140303070216060c02010c030e010e09010b0a090506030c0901260901 68
    0x980c1c841040302d200e2421580e40303854810640050000d0342c8260440c540400d00140050700300280e4012201c0c00300e504600c00c9412a900140720382005416004103401030144074080c00c281c0307040801027100c140c0024807483c1080304a0b40011255030b00d1000d101d00e071016080f42c200c3c8180e10340405941c15003d100c001e0b0702061010000814811080e21020b100340c080d10301c4403000d02d01d55901ca001140960007400c40204040c0005040054400c800a06015454071142410880c81c107800b010300781c1684e213240e40a41801c9420b01d10482c007130221480d8942c03da030742d17443c032103405d044c1a80b028070040039940d00d900000050040c0c0c6a400528032141070b6615076803158071071340c0703840c1510020030300d040c0203020642c07102c00400880e014040c100c0c440001170504031500d01041000a00c03642d0260801480c00c400400d03000e1050f42c1c00049500681f0007929918a181801140b804c581e01030261100d04000c0d810102c4d0748480701a011201e00b03405245007104035410401c10480c064551041c0c41010301 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 707046888 1250 707045638 707045641
    0x1020a151803050d11130b0306150309010f06090c0c0809030106050d120e011704020427050a12141606060506070c03020102120a0819151d0f011a0a02010b0a090e06 72
    0x243c408806c031802c02201da4104004036140000c200300a0300000c2150703a02060409000220300d401c0030055100340d01010001902c161041e090108441041d0400070600f0f02e4030500783c0d01c450300841442c010741d07000840703281c841c60f84400080c050f0a150b004a600105200045810050350842d80c0403031040649940f048020740d41d004540800c030608880c80c070b055440000c58007501301980a81880b00c02100490140c0c035021040c00c4003260002422202640b000c4400014803049008010540c0f5a62810600d8505118941c0b0142d004500300c10040106805205081040c15804140240030261200e40c8a800501b03080c0c0a592151200f41c2c00740c012030a00c10300315101703c0119001904903444050b9107407240070015104030119609018590740e1030500000400c07140e0204001030280342e43c00c00c80c001080c0642c801c00c202c0a013181840300c190f0401031000f50100070080c0c5085807100e502a0300c2d070074103180c101c2c050310102c1091a00302d4800701d0041020840f6401107260082e6000031034450f07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 707048138 1250 707046888 707046911
    0xf121d010e01050f0604020c100f060914070201060608060303090f0d02030d0801090b0f060f030a0b420a050d2702040b0d111507080f030906100501020a151803050d 72
    0x1e0f0308c01c40681745800d030003605031851009003d03440303c44200b542000001d075050300d61010718111150724203901078080100303081240280c2e0902541020341090316208055051131408690b8902178580d807180706440089020080f03032101e115205005400900300d4410510360b00001d4031100007801074004060500e0903c83c3d560030000101108042c0103440140b911045501072500381d040581556441c5490b462880d545680b20b4941d50600c0c4a80303510458800c01c8041409050f00f840040f2845c01002c4126080c82442601d0075501440c1c0203040840d0394003010100c16008004840c850341c142c20308010842d600c41c1401c40107002891080c1da0810010070300d0810001d2072909010f008102d60b161884041e55070600030300000c4a09514071003a030405c13902d0b27541c041d4942c119031030001500a02104000e416001080110340000e09116025500d60810340000d40710302c41c203907001c0c0c665450491600d03241e400c0383e806000740c3d010048020100c6645407500426690110b824408000c0c18030080848 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 707049388 1250 707048138 707048141
    0x61b020f0f070e040813030303052a030103020603070212190801122109170f15010b0708250308010302191412030c030310080d0f121d010e01050f0604 66
    0x5101c0d0307808000340007140c50800008010034000700210f881040901c20381c03860140511700b40c0e014612030f850114192030200414042000781c0c0540000400360751002e44000300c1c1e02003c0300c2c19030341c066910581c1c0b656000400d80c0344c010b00f400c07140d0310f820000460348840716410180f1000c04800340d0354044103990700c1b405181c2e0740e00b002e400503100b85440680045d820400b90060303c2d45810506021003019554817540616860400890002d034210000400061005106008807030003096624407044d410040700070130502480c00000c00d41c023000108038403c0800c0d00202110a40e0301c03561140350444c1481d0003001c11000784802c80c041c018414007440c10025005528083d80c02c41c58030314008101020030001c00c1c210780b001c0e00340c1c02d000c01c0001032032130704060008500c0f8000840c1460141c40c07812451f00c0ca23040301034408504005c2203481ea03a07207455000000050000c01d5410105d00304041549055001c82d1242c2241850762810600d45050041900081d20443e6840c004400340e070380e400305000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 707050638 1250 707049388 707049403
    0x30501051503190201030b212e180c0602010207050601090501050d0602030a090602040e07020c010203190e0a080f01240308040509150d0b060f010905030d110a061b020f 74
    0xd40c903401800c040081c40344250b503c0e000241c014980410400325010204040c3e403071403000340344c465403071005800d6201020030000165080b1410440307401400d081d01081116560340c40210429150140a0480034020714010b01403a0008182d40c041955110b0180c000c0d880b494049805020300000001c0135007a9101d4203040703030400341c00a24200d2440d40d801009500081c54075541c5a40c540d683c0b070110b400c0d440070b403002d08100b04000820b8280010040e10340030084001034110f6108114800a1a86c03030500035000420760306018040c3d100c0c410010f1400c20284e00b210f030b01403081e4243c0900340f1301d054002c01002c66038421594929292070500d44805100c0c5c6c00041e100d2642004104428109084503d5004025000d0100c6142c84040081e40714028203070282d0300710350410140304482c6440c915031a505a800d08008038191314020100762204c48451850050101d141310303c4101100c14000c078a40c981d0301c1f000c204000f14400d0f554507000b6944020321401807051940c2512109000203948 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 707051888 1250 707050638 707050681
    0x506090a0201050d020a090e0108210a0504141210050a110403201c1a18210d0906060e0606031012030507020303030703050105360c1207050403050105 66
    0x40749081912444e0001a51105107000204180201c00154280d6540ca542d80070306904000b50126005100190702c40401d0300410702000c041c108042080d00750450215400c4a48503101d442100038841c0004910740301d00c0c0c43c401c601d400b665007080300b0301c0d2440e44400d11035480c0c02e80401011580c011814058001c0340001012601800c84003416581c0a1250740402c40c0010800d41485502d0000a98000048141100d503150000a8011083c011060480d8000320280300d205d110320700c450a840c0d680c44000d0021075420b1503c04103c851103158000c40e04108009081030150102d07a20305403000300818801c0b260124890800b04d8181e1074040e085038060b000c1e0f402c42c40201420a2141c0404e07070607a4030100c1c1404002c210b150010386051024500c1148583c80c0044c0320b6141c141804054100548540c5444851512401c0d40c1c2e024400c0261800a0324540c4a41c56a60320b640800140310310300e0000c3c42c25020310308200269610400a1055a05c00c00007440a82c54600e850080750740d003030001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 707053138 1250 707051888 707051897
    0x306041a1917191e141605010e0609040509010b04060e04050106060806031b03070512010507080c04061b111816020102040f14130e070305120304030503011e0302090f040506090a0201 80
    0x41c84041943c64a40d940303100160303201286016145e94589448031540700304045150801103220618264108141c40100303001e08121640c2032a000000b00c140c800c105150380318650380c03008242401d00942c4641d03104100a0810400d10740c0742c81020007845005c890444417903090040c04035007503200d04a40c034000c00d0b018006010a2804403a5100e8040503027070a00e40502c11300380005056918110b074070082d0401e450000889060400c2c0c0140070000081c18010307001420003040121680c070092a040c40c60001500f1f07065401145010b00d00403403502d44495000220041c44110f22180d004194018180c0302030030b519040301000141d0a074052032042420194940360100703e0a0034078800c034040420010320a0302040c060040e114100c840e002805852a400407034107004020040103c1c030030408550b80103a0441c9000c0e80c00400602c8140203c40e80007800043c107034200d02c9091074182c040c56008206554502c0d010b1450800400300b203905640030720501012450b0401d02003030074844113406035035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 707054388 1250 707053138 707053183
    0xf170c0a0b030703020d0203070905013c18030501020a0917060c0702030a020901080615060f030a0b0607120507021503160813021207090e0d050306041a1917 69
    0x7444030482c1c0000b8481d50925808022203039500c40c0910055100304299201c2400c035504040006010040f00200641078801c04100406002c051348403540c0343e46a5021841b010081000c0101d6030781d040366048070f40a03105040040708100064025250701401c5940710815103580303044a4528080328010000c143e0450004603c0e81d01d0101c00615985001408862030b040131a804180c0c004401d038400042500a507090000f60b4615000843c1c0704541100c03024204080c02d140d00805200140150328001d580e400008031a884d80d4095a190b10340101e11803100200c01d2401408903801100d0480c42a410101c1d4880c1100590040c1c90150180c442180701c0c0c583e07481000d6660b90406003907c500c0f40b401440240059403000a810007464091b00589949442c1000d10810342d03a8203650405150401a8088011640001070300d910407022140881d00c60080920980c00761001003000740c00000904e000751000c0542e0911030200c03440b82c6400074000b02444d40058541402a8200f00c0b049804007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 707055638 1250 707054388 707054399
    0x30b03070614130e0f0105010e01051804050912040f060909060e1f18140c0a081f1a0304151107030503040804050402031f05040c12020705010e03040f170c0a 69
    0x90080b4030001c5010260240d2a0034401c0c0c130140c0304039982071101d03410000610140d64400074000e420074007030804909005900c0b138510000c01a00700c802e4000c680e40d1001881d0104100f206100007030481202c0c80d03450351a0b003024265030520380250b4002c100131190016480c1654842c5100310354010b607040107140c8a4070360350101d03260b20030390468180518a101191b040703031381400f1404440112800150b41e100001c3d00309100c03680180920a40388050102e5030603a50040c01c196032205a107030407101e217810040040d14041205420a00d01248a42403910741002c0210056000340e00909800d04103840e1482264261000042d00221005081c843c0310002405100a180c029100e00305590801e6101c801003012600100d80c0720360702c1d4035901520007240c1044505500681400e440500000e4032051015107450405072450200c1a40020100d007404001e41c80301032440c5d15081941e035119591601c03560510058020029944000707281d00f003101c3e0300002d080366034642c0030308820907451612 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 707056888 1250 707055638 707055677
    0x17030114180a0f09060f020405041d0c0603090312040b070e0d260c03070302070302090112020a0e0601050922360f0803130c1d0a200408010c030b030706 67
    0xd1a07488046034840f010300c0002080c1b03001c4c1c0540302002c0321005844d68506000c02c420340d003550166520b1120140004c02d103108022400103858034080d1851036807030b00c0762510a45140300b03501d1540340754240c030b40c14001048400c103022400ba16843d034403415622002802c10444843c0c038040100100b202005500f04000b55003042c0c2e08510f4501401400c100d00b002040c2c0c01c1d90f04c03145007100103810030b0006104510380200c062340540b2010070340150218041e80411319407401d50207964224900e1200184030b6030b01c101d0840e480303400064a200000800045207000c1c01a4240c405a0a2814110903204c1030b5402c00c0000c1144948802e40d00201a041403170120488500205440701c09841c09104c0115031404011405040c2d0041c4c0a880c1243c14100340508040c00e810540c3d40c3c0083c00e8104518103810b46a8613001441c01c41d0014900340d40b000020300390381c0c0102450103110404100002c2c0060107500640c080301c0ca90301c0500c8aa21183d080540b514028001c110110321503c40780c1c83d402c1c001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 707058138 1250 707056888 707056901
    0x1120905071706131e021f03060b13120804051003050411010c030e090402150c0321041a06040b0d05010b0a0e011d0417070503090429060f040317030114180a 69
    0x804241d041176017082c4d0081003076032641c00c0b1540d8195046510070b0802c1c3c0d0781344c803440e0020a02008000c2c10104200b0000445011030300c00c408002d44164800c500f8801c00340200c81c001c1c0001009030b444c01c501e002015010b80340c121800d548000c41184d00760069400703050344409040c0c0c9a914090513200880403c4012000a0000e03600070344507420103aa200703030440042c20412240d40045132200d0b4207401e0000a513105034070382036028801100f8000001e02041c03d8005030121000308007d5a40d030340c400700300107013585107400381d10a100b250003009200040d4403c441c040405d48900142ca41c49040759120010288600399050200d03d13041c41d00c40051495242c1c0181c03003102c3d00c00c284030714882c4059994000d101d00f61140e41000446034035502d4140308040e000f0101807980c1c19080039141c00d2040d22078402d2001c40c000e000014250350110100c104540255500c6243311801004180380100b83d030f0002d000301e61103840300074020115807070121201d40c450004038054940c6d5640f2600f000000d0b160 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 707059388 1250 707058138 707058173
    0x61a0d02071a01060908120a210905011b03060b030f040f060603020d230606151305030105070302030f180604150b100f021b0d03030504020112090507170613 69
    0x80d01c0181c03442c0e00c10400003507402800d140e501c1d420704a00340400141070108220752844001d504001c40c07905250000790b140688075010202501402041240c000a4420044001d04075440d0030400f4000801540707125080510f1a901000350302d481d059515040d10098610700d40b0002d00000081c0042e4104ea250481c452164070040742c1c0a42c1c03640030074120b00003404201d544580d083c2028000560802000402e0300300c03000104a10f00f042004581c0009030b08940d0381d80400c000031300755000c1c04034400843c0145400340082059107400c1500500942003616803107000d0801c640402ca4280300204000303010814070024014589443d80c50200340400d00d1010a125612012442031560365140f40484c210360540358941c480380514002801c1c500d00100c518010b2244041130344090700e507400400401541800c00084545a40c001601d80600e02c1200c124840e0800c6020002c02c40041020000c661481103942032600c014820951144000c596188211a0707100004011541080d1519100c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 707060638 1250 707059388 707059403
    0x140d051e07080712062309010212090105100506030604090b010b09030d0c080a0e0409061b0e010906051c060b0f070b0705120f1005040e070f080708070b090a05120c010201061a0d0207 80
    0x200d0841080c0003c00c0f04887c141842e0750301095a400080c00705152a511045800080000d490040b0301082c01e11401d0180d035000d0b0318044005001515540c0c03104101c0d5401c0340c1c81c0031496944185c00c0b0520b6004504150190103a0042c0c510164002c0721340841060380008100d0030301002c0780b0100d0701814030b01a010f900036210041030b800f04080b846500000711810313000001c800780b9180064121300c0b111032910b0410094200400c1a140d01c0010381e512001000020141104051a494080d040320b4001c4480188005804607500103060010540c0a208817150320443c3e5943c1c8081c2c40902030810704a480a85030000900810001054103500c00b0010f400201c100c0e4450b0089022a49035002102e03103603000c1c0c8018031000c1c0c5000c50850041038040010003043d4208139209071902901d20800b4140e003c0031507401e0065541c1110b26001c0c02c4044c010801d44d0038811000c41e0745104010109001d940ba048000c1400140c1440002108a00e040034030b240200710080000298415441659042e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 707061888 1250 707060638 707060681
    0x312070c060e1b0306010b07080918010e04031215030f060e070f03060513050307030c060b0d060f0c0207150f020c060d021b0a020a140d051e0708071206 67
    0xc00502c1841c00c00b6400038001e100700060118000320910141600c64804c0c2c1c4110010421a000a030441c1c00c0c0c5503000781082d440d00b0388400400d00c032080161020390144801000454402c2c1940441440345001c0c2e0ba504544c40300c03a81300d0070200d074981221400c0c80003030450709101140115522034060761190b88002200c0f070482d01c0603400c00c00305800c0011107a501d2401003007407003440d00680c1c1d040700026000700b1100100e6038030542e582c41a01002010702124200483c103000d281e41c02605801c402a0290101c00c48a00c2d1a4000b0f1904440c1020001e140140c4180382c0d920004100040d075071703280c0308000b00300300c80701c01070b00c00b8140030304203104500c40c515000300549c4401028128080002c1c802589a4681c1390480400e415864002445644410848805a6a00450b02007124001da0001b17205001010200c1d4000c808000c000e000792043c074200d0810300940764085002064180140c0d101692158019629400d00344508094009580891008655280c0c00005040c2c503215a05088 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 707063138 1250 707061888 707061893
    0x60d050d0809070f050a29030403030b040f05060102071e1a040f05060322080c01091b080d02030301090b0103060f060201060810020c06180f1510060507050312070c 72
    0x14800c003845190009154181070003074180d010444103000e0a50801074440c501c0c10070f00031130a03094041c440d0003040d0078000341813546c031110015502c400c3d50202c0c401039981c3c07406042c0940600540c2218038051450010502d1204140384152405524141c1c050160a440d0210001900c289102205800d4030484000242208906101003448030b20342c03000b545a9180213a07545092050340e100d0b50040c40c04008000040101c46900d40904500d000b0501c0c0400f07032030a14415501a6004c41c80f455840c0c80a25400e0110003010250107160030072001d00102d459200090321101d42c01510700c05680b05000512560742d91b50490401c6e00010b00d0006141e0b039503090f180c40c42488640c44980580d549420a011010090240340c10385070f0302e900207614001c0c685440a9490700300030965402c404074600c04161801050100f8030000861000701d8001c010007a50a00c40d201045e80c0300344c00000c45620000307825001c0c405443c41950407601460178044a000c0302e1402d2640140010104000c19002000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 707064388 1250 707063138 707063143
    0x3070906120c06050f0714032a0f1b040515060703050a0207050303130302010e01030f06090b0a08010b0109030f15090b09010c18150c050609030c060f071403060d05 72
    0x4205540c2040c04034461402c00300341e00765003604202c007040341c100100d111104c0458215015194401b40ca0707613103840403e0302a07045000700c0c03210740304544c2c0004180152340c0c0496483d90340010100143c9a0919200c1c104560303828103036215440b890f0b10050400300d603150a9114550101c1c0544d041c054803408a00082c44c582e0000408801241d00800c01c4000641e041103a1400350000b0b400843c5484c0c1c03406001308294141e440020704001c4903000010040c6d100303400021800340b02e8a8140440d60315403480c0380c0070304548400342c1d0161030513010000d840701c030500404500a5041e1554a80c10f8203640b96152100c4403d00151350752650480b4909840056205262100d802104c00c40021304242018a09503017800c0c2e4030b10200074003024544075201650405e18201c400d803801000c1818103d1000340e81c90318081001030185c1c01110200040254040010000d03640c0110a540c0195100c6007032166000742964010001030300c4d48094200c5100510003180c001a005050f80600c4003160340d91413 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 707065638 1250 707064388 707064401
    0x120b01081506040e130312050906010504090819020c0f01020106120b0702190c0302010815031c022803020c0d110f15031006020d0c0b0a05040807080c010902090604022502030709 78
    0x312110f031845520011b06500c51000c9100503208803050003981030001030559507400601650388100d41d165288010080e500c0125001854011002414144600f01c042e407a510446080b42c020401c07841c909001e50300c10b101d808295548030303c0014110502c1e031641520104003d1001040d8800c00301c402c2840424010504c04507403080d0744035201581035200060081102a0441100407a6802e01c101c0c250360106505648907654801500441e0f04041e04034900700041d410f1092a06c0000c510030840700c41c3e071040c40d00d154000d400b100c100c0320401044c05001816080040d100351103204445045292080b003514030391000400011800b0000203205803298003c1e101c410594001c1d03841040010f0b010310140000004504241c0050704980d202d082c2c0942c001040b815200340e40e40d0014041000c1001610b401c9500015015190f24420001d507000303080d0184d0591041c805140015480d1a289c02191140b1290203006030b4182c15050010040502c100f40c00c0380c0c103020f004800300c6da100d050f100e030381c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 707066888 1250 707065638 707065651
    0x2a0f090e07030f110406061119031809150803130317040e01080102190503060a050d080426060108190f020406080f0705010e0301020c0c0607050f0105010b0a120b01081506040e 77
    0x95070041d00c44c02c110496415600034000e000150340001ca85a83c0800c80c081140340d1800e1550881083d4981110811140010349070305280b000000b14521020303510242d01c0c95030303160620b0b1003181c030355120f169680903241541c0d224400e100424000203400c0903000110301c40c081245828291120a42d03000301c00700342c07c01041e1f82e50100701c114880614a844608078407607410075524506150003c0b035840c40c040d0141c14010112015990100410714084800030150112802c503481400020320781e0400340418155164820703c40003041442003c01c9043c0d91503144420f91007902d103265980d20081402450a9078010344e40c1c07000003120038041c81450440400035001d0a04641010005856071140c1c45945001c0c0e0705c1840400c80d54000018400a80c000c00c40b4600e03111461850f000e0701c3c0034144c3c4200c1045500340070000400c0e041a1000c2c02800b6640c0e01c40710308201c2c9036500142114440241140041e100314089200c500000c2e141c680d0b40c90002d8401c600d090313120507070031a446000341c510 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 707068138 1250 707066888 707066903
    0x14030a17120406090203010b0d02090a0902031f092607030e0f040606110d0e060d1e14040b060103020c10020d06090203041a0603070303050306100302040504092a0f090e07030f 77
    0x650f01181ba0038401e002d98440c3c02c0340c3c8404400380c19004221940b500511600d40703e6601da0003203042d981c040182840010440203001c0411b000c089032240036041a0b0030403a4490a01b1180c1d10000c0c821040e6440108402c418890030900e0b00d880c200e42e031541001c800e58010380700c0100c6140d1031b00d4600851b00a42400e8848500300500200c0081c68900c1200c441400c10012032440c82040e0345041c12a20444100303200804c643d014800d40c4401c11441842c1c8148040c078081d1456603081c00349940a20541c00b405104d0155540c21005405920941c0d240406640215202206810203039011b00011000c0031070001c0c0c52615100c0c1345003260b00a40e0b0940d0703562406046050580c44c213081a6900401c02c0d805005580c0c61070364041c0441c00701400047c45400d282c01550000b40c401d5064030000c0c10010000c0c0620483c3d41481003000200f40301e007050440b110240210302805a90201c42101c00b4040403000507490120342e03000070704216501c03250900402c207000000c9055a00d000341101d0003440d9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 707069388 1250 707068138 707068151
    0x303020615040e100e0d050c03070210140d090c1202030303070c03050f070309090e012009010519080f0f060d020d0c030803010e011d100e1b030c1314030a17120406 72
    0x1400c602e000e01d1b0f121001d04002c1d041005560b0242c01000703071500b041d41540d221800030701400d01610080401a58082c0849010804e10207001c0141c02011907070b8001d0a840d1811902c07103680c00c040d4a040100690035030320030000f15856520407182808018040d10380941000d16014180a541e4000704050300010b24a500c00e0010058510411039100600c8000304004114085014000340703003c20180d8207800003154802e22640590111402003149221b9005483c0140710094000f15054400da2586155000091240880700304404d010300b400400300244500681d007002600c0703c2482c0100c0e1000c040c031070300100068134a40a94080c01020091403050342c1080b913998417200d4200c2078120000d54400034040004048540e00065640c4540f0144003541c4040b0040010442c0003041c00800310f0000c02c10134515003080c01381214002c46040365180c05d9850514110700f91010081640c142c0102500c00d0006181d00c41c10320020403041165070514946c403141112202c0125000e451044c3c4480 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 707070638 1250 707069388 707069411
    0x10c080a0c051905071a0f07032628090b0f1b040303050405060306010e0d0b1009110417071d0601030c210b0111072402070303020615040e10 62
    0x400304514141c100d0403c89180c0380c803a142d440615210710010911141003c146015032542140c00d4840d808103c15945c400524000b0040c264640802481d544840b0200c600b042e074086030580200724001003000c0c1c0c9804d03100c0404051502606210b82c141ea02e2812a00240509003102d22601c0c00c41245920780c50074003600b19981c122000c000900c248100b09c2400000d4014003075400f40c0318151415501c0380e42da40016141001f5000c88240d104c006103145400300039460741d01c40e100d51001c0590311a00b40c1d840900070240c2d1070800f03c3c2c3c0c3c0222010301040c456501100508222035008800303c500056135030500300d1104840c03050400c8000030600030003416581501600342d175000d4030714080035240520301440c4e0128001592003840b0580302e40c520515a0b01ca883c9171803401042c01c080c0c4440b0796498030144481d43d0000c1081c4440b02e103062a44002e1800805c810044035010780291031241e46020f81011200003480b651540240d41c1c107070b8448910010440708004080600c8000350b24200ca0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 707071888 1250 707070638 707070643
    0x303040201020c0f0a0f0e070e06070302061302010c021206241e010c02120f060601080702060f040c090c05030105041b0c110a1508070206100f03170409092015030f06010c080a0c05 79
    0x3c4108ad000d41d008002c50bd00081d0f0008445a21468810000750140d80d01e01c01224002010300010754440c0e1807510b650042c2c2d0011400600500c0e85458401d91800306201001040c0c01c0508031591081c01e40e480d044d001202203e001e66030240500d00340d00c60203c41d80c0010981c41c0108907034500c9038800000221a000104840d54020000b424510b00c20b103070182c5c00940d241d4006207001806c614000c0440d0030000b145001070090004903a050181e4020000018090b8009208040c030550400321600580c103e0507007003a001e00040d07035480081010644a261680f0f9645551b640c115a020800249042040f2007803140d0300c03510741c0c031100d203030520703500007450050094124030381568460300c01c104135682844050304580e440301c0d2414185516010000c0540119440711a899040c03480c0c480800070f16161001742c40c89c100c0e0071310201c4400c41040c0011022414a464960101040030501903070300304208035881541494111409030350341c0e03103640481d0451080302d0003083c02e448002c010400306 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 707073138 1250 707071888 707071907
    0x3120409050a020301030c2306030a0c0801050d08040e07050d02030a05010509060f0f041104031403071401050c0708070203030c0a1415190203100e040b0403030e0303040201020c0f0a0f0e07 83
    0xc2c0a50a55045845030600c206041c450085417100c1c2d202800c0c901d0004555100702141b00501054681c9001c5442d038003d446458100c0c0300048001c3d002280078586041c003042201d13000440a828a810000c0c807401440c80a444070080c8201804440140c54441c0021446920400400303d029403401051045407030000d0040c510031a0404c0c10a030f25600c0d8800264242d0408490200d0350b04540340041d00d6034030403504042c0240d505200c505000c40000401001e10310b108810070041050030302c00403400c03240c055500303001050080091101190302400070744001c03400241a17a1a040025641500d0224071030070450b0003900d41e000f02314401c0810300038100e031030b0b1001c40050b5592a1544890801c1903546881c405882c2e07003c400704012241c06072851740a06a052440c0d52036017014205284c074520100d03021400641080c2c5444020a0f001c030681c0d000b140d0680003000702d40c3c092800c00164038000007800750001008000010781801d011420002000c004404040700d0804400043c4501c58 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 707074388 1250 707073138 707073151
    0x1080309120d0c060b0a0308130812120105010f090902032701020903060c0d0b0904110f0d2103021c1505040506180c070209090c0306010f08031b0a020312040905 71
    0x104034403160300d643e0480442008a80d000c00001524034500700003841c085401d40001e4816140450400b0b083c141484541c800e85030868100c0e441a244046134484512400c040400385203020700c0100420f502841c2078441d9419903080201e042d64650345604226041200c1106064400000d91004c0c3d0750700d6140444020034140095190050240120340d4a11010381528841c01d0700043e000191003048e44926071803803008140032102d05060821580e042c3e412010b0b00d05c5139400100c0b09100c0e25143c488440095441100581d81c6880c124540b801704c1c2110b0924003d00d42c0800086112420003c2003a103682c281c51400034001c1e2243d19000110241030b0041070080345000d081c05410b03a210b4081c1103100c400180c001c03540381d075801c000039028092902c0c025000040d810030300106407404602d549a0150540071100542c1e640c10142c0f4201015200301c948a070402c0040c05543c40c0003110422040d40030200304c9003034410a0303000c685014200c8243d0255142c02250503c0306581c1400340503000074 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 707075638 1250 707074388 707074393
    0x50a0507090618050d02041b0224010f15111c1206051f030b0303040b0d05060109060e060703110610031509020a09051e010b0408070512100b060c01050108030912 71
    0x210355051080c40e0440501031340388100d11100c01e500031035455402018a8520740515044a0803c000c03010f965014550b0b1005060fa0014840380b0031400001e84860485445190701c080c0c0034502100c81d040610303040321050170840d0b0b08510003841c40c001c000d0489080754003041181100740c82c1c90003c0050358110040400c46041640410080d0b41c0c520b03500c106005849008482c8550780c00d000e600401e4103503260340c0c050002107400100700e40b00710040c240c240392810091040b680c0c1d15004680c50000d6000d11408107035400201c422508050002e030051601c039050208000018616240c5081011290314160326040c0c642441001507958003025000d10980050105800a81c002281d04155018010002c0c0d5600d002841c0e2031010309403c5841a907100600703d0039611060466499817250103402b50038400c601c00015641403a080000c8080075800161000304190030b80740d00034080c800415a403100081c40f243c0081c0f4403c1c4280c0b0300906109004603a601164814489000303c601c100b200b043c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 707076888 1250 707075638 707075657
    0x21e030f010603200604081204050a090b2b02150c0c03150105150f03090a061104180507030b06180102060f060d060c05040b07032c0a03061806050a05070906 69
    0x4001c0744003403940d520340301c6071392216414003008511035001d0f550003100c0703512401b4000b424111000e07004000f07460096a0444000351a50550000c2c1c0316901c03421904240030102e0541200342e01c1080344920004050030301d418042a400064a11300d1001024404402c00907241c4e0807021700b0001c500300c001d4142d02421203116a0810384686000520509000e0011400003c0d00072099008450f0381174600d0344202d45034103088640c23607a02c1c0c0a0103002c40b03446140c6074030b08241a00500c2550111504440d0034603241d280171040c0d03c01350002400c00390606445440145155640074040d001c00180b1608061510f0035501c0020700e0610f01070725041c24121441c1c184a19500e541544d14000c0d90042404038104500300400c866520481c1d011142042c030102d16441015804aa08100c000c080b4046414075040301014107603201194600a0b03000d074814800f0000203030550441926402c1284214810700f04545071300c001e407002144c111503401c0d41c0b41d040040a43e0441d001a0103001107250000a1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 707078138 1250 707076888 707076893
    0x121f0b09042f0f041a09030d111b0315010e10061b02010c170409060815070c030c0609020d0f0b1803090d140a05030a0f030b060f0a0309021e030f010603 67
    0x240c1d01000288100904005881d2202401010449004020201713601540044071215648190400240a4428010b9803402e044140c400c4000c280383d1050385002c0c01c010100001c0445640c00c14140c0389801d40201012410001f04c8085090300170a00100d03504100d00d4080008404603185070480320500c11036620a8041c0d6a408800c280010f0b4282080580070045060501c0004041d81c2c165410301c500043c0444c00d240c0a0b0440d0003100c06140032150502c03184003803030700c45070022205800003070314420300840441e11601e00d4030101c502455001490702d8864001c101d40c0716540c1e2055400c0c1e0301c50030340c4000f0030400180042e8820b800030b515640040700208032940740d129440d0624854001d901c1c1030801c0c802c105400c6540740034810205c405252051030241e869400083c81800030641d0012440140390080c0030301300c96010700a00c2e0520f0505120140748907078000c800c2c031108055032002007000686448510400c8410200075084005200c001090303d4100ba5008040c116414203904100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 707079388 1250 707078138 707078201
    0x60109060e0315280219030e0a050109080d151a0a090b040b1902060714031801021309051e0106050f040512070e0604110403022e0806130c05121f0b0904 67
    0x5017101b01780703008141e015140030340d280707072015900002c0c2c21546090000300812003288014290013500141c2440f41d245840400c460841041c0300b4230408600d501c00090081c811381e8000c0044203042d0608804483e20f4124510181d0040c1e00401d212a40028401d030703809010120315000b001d024030052000d071601102c010300170b80281201003410400840800c00544d02d0000d82c24030404c4000085480744d04003895546103000300d100d148141460310300403450f0781c60781964a80107a03944146145c0c21b80d2030220103d48a510803c0c0c0345c05998001d000103d4565600100700001080800c010a0740c10f0400550030140440500710780d204519201e030501141802d101500d080780c1d0110f82054406014501c10107500e0180c5a8a160400c0340a0101c61201d4114410501805096135500d815813044145407045400301d009402c08202e060000303c81c40c2258032521a8020a003102070500300e041d040a4504240c3c81e500407001c00340012400300100e04140c030441100c002501441c84009180044240 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 707080638 1250 707079388 707079427
    0x3021605011b06020409150906080f15060a05130222150e0402070204060e01091802010e100e06031603110906220807090c02010e06060109060e03152802 67
    0x240c191010003000042c003c240c2e0580d0700400034170300184407000e83e8900100f403103841c0d400b42000031440c100f4081034071240060504108030b40f40c0010410103600c00d0540300d00400c024400340d0700982000d804920f135114880c4076448509500401341c3c880003401c600309800840d80d51580e02440c9c1022040280403840140e803802404a4100200d10090b5000450b010707124121003e9041030400300c001070100e10054100303048030041c6404000c2e8040360400c40402002100700640003d807801462a00c03864000351000808001c2d0a2400380b108001001c030301c040c3c200700c542600c48010740c245940b40540501528103004925007040345030540002c0040d480e4001d010b2020716410710304c844c60005135040e20160002e0301d03101040303801c202d0392207140002034082134144500550030b1162034201000002401d80c02210140c40300071410b0305013041200c00d000858007007076140c402d80c0c022841d60034024a24500a182081140140d440790000d900d858401c0248244605031041188c01348a100c200c0040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 707081888 1250 707080638 707080667
    0x1020f1b04090510060311030609030f03010302040509150c0405190e0a0518010f0615260a181a0112030824090a0902120a050613020423040302160501 66
    0x3149045401d19038a0300d00d00141046205280c83c401201f40804402100d941c03c034110200d501c10f9a80b41400d030b8481c0102c10410703003074001c00e000500042c50282c000b903510540900840d01249490903000d40612419541043d00000002d41440a8141400000e40e00440142e600c55170301e01c0c041914050400040000002e1662040803998000c8202000c9d20601c0c0018000e0090080300d4034100000d0489114182e03007a007084800000b03090040983c0c0c03088542514400c0845041000680e408800060800160603944c407003c400c56445210501a11802262090050643c031000d98400e4a41a000700030841d2030441c841c000250300840d0700780d010342005004c4842d409607480c21140e40c3d00c28100d107940201d012040090308107032a40300803061402100d0700c1c4034551103c448640c03146c2e80c948016080ea000400069011103d00141c4003080f84003800000c1d01e5034019000c1c3e1140100903800320b00b82c1c50b55200380302c24154104030354540086110f401140e41e03860040040d00b2a01512040c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 707083138 1250 707081888 707081891
    0x12050c0a0c15090f03080108100c0f080c090607060f0b04090210030e120a1d0a14040b1306030b0702060c09010915120f09021503010807050d0c08190201020f1b04 71
    0x1248020400c0d0070040409a00038402d0050410f41d03d0050101b03002402928003612607455000e110000030f0081403452242500d5030045814580d00c11a05600c0050695540503030800c146152621000020801c1501940001032541f03104003030300301524228500e0500c20360404ca40900581d4983d40c03511205691400c0006648071003807405c50a01c0c3d4081d2146003c540081140c2d08069080202004500503203042e00c200f102e422420070194078514014074000c0c801d11005585035051907400010140ca000b080d1120305c03200c0d4040c04c030941c0c410703030011915114404244000c6039010401280c0100d4028019801c2040040000780294118851000003510000c0c841c001ca900072103403245880b41410091100a002690050240100000c1240120640c2c1c0c0c2d101c150001000640c5d050780d400501410340185041d08101700018000f20070b591000841500041c0c0303000c00c00c01084800b44109a4900c94201400064100302151407a00c1458200c81080381a250f801000e03600303c0c0350f04650 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 707084388 1250 707083138 707083163
    0x305091306080604150b01180911071b05090a060b03070c02040213091b180b0c070e011509080c010206182109030d14180d05030a12050c0a0c 62
    0x504030103000ca07a4004a424003550b4240800e01682d0150401030b0114100c0901c40201004011118501e9074404068030201c00101030098950980081c07020f5040004028100289030f100c0880f6401d4108500e0107814040f217041186003003145581e5801813520341c00b04406407030a0340390b03c407910000744100c1c00c1001a20460f0119590340e41903a176540b0140e03413000c141c0c0ba11280d4000080072a00d0702d5081d4800c0724103040d00024400d50300581c081001c0c0c11a40d51282c03610754041403a8100c0015180f00c0d025000c80460782c0c03100c681c4000e00034954500390008901d01d981c4064080345207900400c2d042d8018034820415a6000900541c100c19280d2134500821212001d07075082c04012002500901104984071110800303030700242424035800c5060b81d540e03075203c00003624011854000c0d20058a824407042588200e503011000380410082c00402c4c50f0f08540c1d5607d419a4048160a400b0803000b40100d085000c0c144505a40309501036045c41ca0000712080181840c042e10070018281d810010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 707085638 1250 707084388 707084419
    0x603060c120403200f0c030d02100b0a0b030c0a0e06040e0609191103011d28060e0c07050c040608070b1c020a2a02010f0c05150a0b0f040504030509 65
    0xc1113030018489051000d1441c810801855403100e040303071803605241c460f80000b03031224035011a20100320350a41e0010120b980c1081954409800100320440e072112000c0c3c00050501d2a0324001c1d07100d6081220003664070050340c000a00381030300005071640290424082030000494001e1030503040601182d80d540d596490101d0841c1d042040b1042030805801d14008030440b10386500650b0617100c0460300c0c100c445d003004010790507201c404c5130030500542240c007810031018140c0c100c2c0031094803614004116181c40d6105101d00180039a154200c0040004004080c803c00b443b84600719442120144101890085a07940c0c605040c0500d601c04800020f50f07400604080900300c14415041304255241d240c61140a840c0d2038070711111540d003192102c0c18600e44100000f4599042d0360585500e0225074240204841d820062241107440b0b20a1840c045404407100c1038041c032500f00d020000c119036005200b849180c00003503a50700d020707600f0f0074103210001c0d070480140ea0401c3e10549466215000303c6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 707086888 1250 707085638 707085647
    0x4120305180709091a0c0313110a060e01080f19020a0201061206022a0d050306040f151508010510140f040b03220b06010f0905031e060603060c120403 66
    0x602001d8a40329140300055503041603005103040901400c44080100f280f0320300c1c4800c3c0c220464103600c4503e02040002e100e128480441e04030640244004030314190b014012400307511042d001500032500302d080c814880d60b44020000e62142c0e4010300700d055814258819260f000b8010f0080340502d4001c184600c0d814800d51000008002803180344842c4500c1e410004002d5128080c6210a003e2450720f403580c04050001c03c80f40b01a5050003001c4c106000a0120b0740c3d604060000c0c0c3e44581ca030110300300540d009000706130380c415810f941e142d00c0e80d00d08404014a080c00040074828070100c003004100300d541c1d88020702030526450401072040c01c009540c200840c4035a00c1300c903000e11808903006c41c0e00c00051004d140300b06490034002003034203a2507516400302c0c160541e00512000040f400503040b94410003114250745218200400c0349519800040e0a1210110207544000400480c09031812000c04c4042e070004812b4000d401ca50038400c19601d400d119042062086040840110f0300f00340c4036 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 707088138 1250 707086888 707086921
    0x209060f04060314060601020d0203091c05161e030203060c030c0c0717070902160f05120c0a020901120308010b07031205090a030f032702280611030304120305 70
    0x700200b160645a01d84a204528201401c0605108450025115500025a10948480c15001141040300804c10003100101c0c48802c603220319001441c41d800120304100a0048228035018541903e05010200c442c041344065007400c00c0d00001e10030001340c0c40100d0341c541c003c003d42c46215034942e1141e440c110544690b0304000071503c200c4c10001803442407001c0d10048000181e0648200f55511050581a802505901c0b440310261704090b0703001421010540050a04c1401581c28100590208903041e410a090034120b80e08002d08220842ca40600d4040c0940040302c0381483c12a4a1344005090000c14041ca40100000081b01420b05005a41403040030f000000144007a00d8800701203a1500c00c0341e13004602041e47c1070840c02d1035030700034081d6020303440d900076800b20814548040c9403d500c1c40c0742c800b0b03030f040f0224128102520768812600800188441e8034500102d203018001000c040701c020609103603400901c103020004a010302011880c500300e1401007003e4030b0b0754011240e034680 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 707089388 1250 707088138 707088169
    0xc041b0e060c07081f02070804140d06151706010e061e090c09010815032d07061e020106152a051006060305090c0105070305130305010f0e010c0c020906 67
    0x2030044002455600081e1174000c941c0444464246200d001c101e074810790280810082081c48240000d12145100810080c0000303001441102c1040c20364845504a40890624182601c1151030038003018040301c03d840f0004201c400103001962600000c2d240b00400034011501c07600000c040d1500204a06a40407400ca40041124034a41071030116164581e000e00c0100b4041181c4400060b0491116294041c0005015014200d05500b10020000441b48000040300c904440c02d00074516a00400042002d482107031601075038400200c2c400d800d000c07025514441160b05011003401410342d03d07541c3c1075440500b42080c1000c83d004009095000c0030301840509104040408a42400700021b481c100f034070301c0a00c0801c50140ca4580840c11381b035084800c110980e100f02c03481c1c030842d440380008165040c040c0c0381050a11480202c0596007010342c0d841074580d691a2681d04030140207500c075105d035040c005002008070041c2c040000e002c4204150019200c4c901940001e21552503919550f84402d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 707090638 1250 707089388 707089393
    0x22090203070309061a0a060509040e0601120212060c0f030604060b0c010b10020f031204030905030703080a0f03091104090c090c08041110080417090d0b04050c041b0e060c 75
    0x74003100001c0041c00301881c00e40b0420b007009040c03030a070745682444081184020f07103200e80e4103042900603100b55000c180403d4120f039549151810780314041c40303414044d00b000d9000700404015401044101003081111a2042d00030005100700d416140342241c0c191150480d4880d16681c0b01c100150040c07441c0d0744410b10200380000c0d0089108419405072001d06002c40e0307250800c40f40071034102e13030340c0caa04100906254010022130104020b1848141d601c41d2180c64041070194403100030a00f004441e600c1102e208001181c1081034039000003a01c94103506601d420059040c1f580c8484131801c5112403114040c60b075034003101061094080c000740190039614814860000340501c01001c03034100b218292a541380c280c80c00d07901745c030309003134002e2000c503060343c60189035215604c40a080d42203080041581c548108807044041d120310040d22041801581d804003140340c10308219040550340c05005d4411460a1590780300b00140040451440744285040c01c22000844c0100b55076110f0954044800e2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 707091888 1250 707090638 707090641
    0x90b0301030305120108030f120a09050712030207140f04200a0504080c060906030c032203050301150f1d01091e05130b0306070e030319050a030b060c0322090203 71
    0x15402000614130100d034500c40510680e60f0340c10070798a90286840d000d41c503943c20080c005488140305911a000201c02c40005103006207642c3c1c0c2c2d403511404d40d11400101c822500381c44141601400200010050380481d000d95201c540001122000c003c500f00d44a143e8640c0c0ea5010100704040000051091000040da01c1020780c81c05001c41c1c119204106d014032950710315200d40d081c0f11007075130340e400b001034002401c42c0c4545481d01c6140c1c100410302d030400200841100d40c0340081c07030b40d03500c20140603446050b44ca50411005c0c64890000310403940c20f1164901484444990100000d0f2031103515400340090a91040c0040710000c0c8590700c11440000012200c40380c20000098140c21100112204605c86501041103000d44007030070000e41d85504100c00290b0001c0c060301001d2a89040101540d01d401c1c5038a0420744440d400d06a0207002940101d0020074071a01362103544120881110910306124185c8031951750b038402c0c0901050100e50440e0b001c1c2c0c6800c0607585c0440a401d1740c000035500c1c0d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 707093138 1250 707091888 707091893
    0x616021006091a0a0e0403050f07050a0f06050108190b070509040e01061509031a0c0702100801031202030f1e041502060415091a06010219061a090f0a050403090b030103 74
    0x6464284522114002e080d4040661861300e15001002c603440303401c00414595407078400b510b0641041c621031328180c42c10001040012014041e02c0340721407144c0e80c41411800c050902c034045400581000f401a8012840c0d8040048100300044030b040d44404176009944d5540c504803198050b4078070060f002070910300302450540c0d064110740d0275122000d100314001004018101c4c3d032118144030140c60580144a00da02e4002070041542e4401c0d981c0014034500805940840e07a2103040c2e50362600003a040700d00500803c03240c101c40540010480c80110b0a1528169054000f84907641000000120b403402001d2940c80d4901074400a1007041d095404140721400c010352210003c039000c83d180c0024589106001880380b0800f4000c41d000707441c0039560004070102d081a5107014119034198840c14480361848014800414905489010f0104001218400440b03034203e801d15480d104030812010040c1541c107050319254402c041640100b02516181002e5614102a410400000700d000001009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 707094388 1250 707093138 707093141
    0x11030f03030118020a050d0b0a050d110a09050108120c0703020909030a0305070525020f120a060b030114060904210305070e04110405060f0d0207140607080108061602100609 76
    0x40783d803e9a40702010b4a40c401000b4201d200d1a100c0c04007162050012030390032200e59000d01900c040c050100070b80e0340d803118009207084034024030841d0042e0391413209116509100c035541d0b000740151003041c0819410285010b46034141c1860b024000c100100b08003100c48800c0000070021600503000c000942014022700d5206d07408941c01d107003c6070500001c6006a44500201e502c2200410b00301d485114941203240162100400241da1081d40c000301c451446c2e03200303044402c06030401d00c002c00c4c10380d03040e00d40002504c2000010b1423181c0d00d050f001143c011000300300940d002008aaa011080ea80c40ca0804030400b01072180c1402038580107081c44560b501940814018a4540c85000b541c4a800c1d04100645661910120f10501d06100800c000e042190141c001001c42c00d08040c1002d0030111403000704e03049010290785610450302e84c1960004280180380e0030008038a450b0040b581030910480e40e030107014100c550000c066810405d1080d100344080098641003240500c40c01d50b07101060030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 707095638 1250 707094388 707094391
    0x702030310060f020705040e100c090602070902030609010b21070509010306051023040503030c0607030c0c112b0c05151c0207080c12030109110c031611030f0303 71
    0x4000220319001107801d6000d69016582060f107580100103680c00c000601c0054440040201018440e40c8420761070003050b8020303640c400c0c69036640e58100c00e1034000000d01d40043c941c088450248100148600c60f101d40c40e880d410f4580901d02941d0b60107100105120500d800c2d42a602030350922010f0203000396000c0d0043c55442c80036a4140003241d102c81c1007110340134590a0440c0485c801150f4445001d040118a071407a203421010581482c0d0349202090845d0700803000c48900350840703410044d90715003621403100d10132070619001d50303440ca150707848407101424a913201c0c3c41200c3c020361403044203d10001000910441b01c1e0600d1030300440346001c4040c1d14440c000c90340f060036456446c8a140c10b0b0f0301c094070919040f82c1c0031090f20b800c64005041c001e500280040c0e41d0b1060812000f91039070410008000440d0b01e260361542d407589000399000c00c44000740910503600008100a2000881c0042560710030310105426158255143c58140400c2006904058050050300781909a03c4004409503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 707096888 1250 707095638 707095651
    0x90117011104050d02010e220e070e041e0203010b150307030609020a020a02010804080d05010b03010801050a02040303140d090c0807030b0c120103240203010e0412020f070b0702130507020303 84
    0x78440c09125481401803805603000d03180e080380b442c00034500550320800220f00d511b0005008601003140300c0300d00000f88080f51000d0310b091a242d24143d821035204101d184014000200700344558189662103400800760807020035040642c02042c90299a030a500c00e024051009002404e0090120388080c41500110f60401c007081c5844000604c00841d4002c91300ac0682d6580500822038031580155103186000d00151800c45041c1b00b50500c85085c0e104950103054955040c1e03440b580340c50910f03403c2d500020200c8100c907005000400000341c0106c00c00002d00b01c5e2041994035003040014150090046181c050014188200d00280c44080807035480300380ca0283e0f8403490644d40b0580c000722140b08101e01000c9505800b0010404a100804540c0031020304914103442991200520400ea810a800c04002800d4180c240000c0005550000e0b00305007803800500f1a40d00d0f0700c0744080d03c8222911820100e1003000038200115038a80142090846820b001000310342056a802992500129082e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 707098138 1250 707096888 707096891
    0x6030415062601090c091e0f05090d050a05030f09011e0c030f020702090103060c0507050105070f080603060702060c0f09030307060c17090a1e0f110405150f0d03050909011701 77
    0x108480c502c018050640800c0d000800c0c0c1140500d0401c038140100018003441292480c00d100c04101d400c51070043d0410280000000701c0c2034100004942d04042d42c0aa200c800d003c010015100c0841d00103040d2070307110304841c6410365140d5400e020076000d032420030322820124042401100001d071881d84040704000c8950b0701003249500108480f022840748660180d80602c00304010800036045420a400d151035514096081c82c41c40c1d682d4a003501d40640d40800482c5003810003a60f015405a0040d0780300104500528180c03e0a03d406900c411000d0510220241c0002c0e0742d59540c0d065800300d81c8042800b07412203a0350000307824123200400461000b500024084055a007010031a20145400f03410220060040120345598000b062624a0000d0b0000802b45504c540490020711080e01d0050003080d030b80004000c04010042101d40090510103011072032200f018494441e40f132071811014003074400034517064950a0981e464040c403030189070300082180011a94040720390840b281d40d60070a00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 707099388 1250 707098138 707098199
    0x12090609030206090d060917041a16060b151c0f090309120f12120b0118030807170a09060201140f06060d14130b090c0607020603041506 60
    0x41100e04103100d12000e540701c1c00a000520715481c0c001d4144200074851000095008115580c55840e070b8288200305440440c0410100030001581680e104030035128480c0603e080000c2441300c00e0000f908002402c3c4943da003403203114945801141d4000d01c0030240b68a9214a46a41302c1410314050500140c029410700c0d0f41810110f15500038014201e5050f250203140c24101600f00c032400403030031002c1cbc0e0b14924400c295008030b080c0c0c0302c1a1001c1560703956030b214040c4140322500705840442156604008902080031540c54035040d00105499101505540c0e506080c206040d1005003040f441d8090ba90000d4001c000c1504000d0324402c6510302d400900c00000b0400d0032102500b0101c0d026080e01103148005a11441d2030802004080307142d02000078135180100031214480401c80341e505d003020b90050207001f881070026025510141000003403402007250701c0410003a01411074000e0044030040045420441c90102000001000101c01c102c6d10303903180000710001407074103081035490010340d2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 707100638 1250 707099388 707099399
    0x31006031407200304090c050a020c011812080d020a030902150a0509040506041b0305150a030c090209030709140f0c12010303180f090509010b030d12050a0e0a1209 72
    0x380244102c5160300c0d0304071070380600540380c0960381c00041400b0b844d000800001c100d4504520680500803129031b06c0b10303200c0b0380d9010003928088042030b145040c46106024480d10081c0051041d066848160b07400d8080212450011242d00803141d001c03841a001065441001e036040d40b1101229000700c88001d00c000303518032071203980e2180001d03110005500f0000e03200316060a030003090700090042e100040b0205840880034180c50651140b40000c0d4440c400e00441e2400340ea81d940c00010100d505c0d0601740d107151745104840d0101e10030f034214a1340110312000c0ca5607082c04128024500c44009010003013000201c51040d40341124050200114440415259000101600c0010540c2c400c0f12400742d0a6803400d8940b40c600601051001c5803c40c030100f01080321424000040003502030110755414903085031800d45164810440c081d600a01480e142d0940c402010f990101d442c0000240c1501c41141c000040d1022413a400144d10480c001c000420030180ea00308049412aa26080303030300c0e242c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 707101888 1250 707100638 707100671
    0x12190b0609010b25110d1a0705090618060c070e04031409030d0809070801290612070c0609080712030f0b03030714030c1903120212011403070302030303100603 70
    0x50015442035110000705840000e000d0740351132000b030302820258445801d0100050321102c03e001044030840b202c0c1c41ea010f070702d41a0301c5901da00700c9800e08040d800d0200010101e0ac0741c4c0982d1405011000304101c110b203403504ca100441d515a200e0005582455448802121000c0810303a4210002141c4807403d010810003c070544000d0348005019200405204404450140d0302505459003402803c1c8001f4520300e003441400c0600d0501c40b04002c00044070307041004020722400c2c0041c011a4200a40c40e00f6640d0b010b00582e02000d1424a0b0380440b242d401c0290090000c0a4028a40701e07000500703505001134403c41c004040c001c1c0e41c050081c122211280300c203440074480501d8056105001440018008900288103400260304580c1005482c044a07460954082c9071501c00d64030209601c0b0506500500c445800000440c2c198900b000c000c5244141e14814451407020b02c03030b0703c6151011aa02400098011070b0020104c0703460342040c41d110400b80c44a44210b8022a180261010303140b80c49 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 707103138 1250 707101888 707101897
    0x4031a0a110706051f0807080c0901080c010c0f05010507031a0415090b0d0203160512010209010503070c1e0b090708010902060d02160c03050726070512190b0609010b 73
    0x54844941442c0e560707510386018003000b800c126030001c0d2901001c442c40100c010050b004110080050401501d8154864204a001d206042c000e420240060000c0d000002d040c000d400303000c0c6454039200e90a4100a070307451100e150300811950800041c06819645500040003004030007143d030000703803a8003082204850107075105003101c0c0030601c000c112441e92540241d0b00403902906014030391510303900081c1020b041400c290b5402016900034401070502e04c103204c1c0042d9a10008514290078400080c1160100a040c1c0003000b10384900e40c410000502d8440c003a100c403800038005c0110b039918001c0c20061040fa04030a0a1117440000200c40c00705018405030960003805035071401c1c052000450180d403050080301120001c88071550002061114003400450140c0050807602e400e1801d012481103084015072b4900d14401d020703590305080814a20102c0c3d00072580c030380e40000407503d41c0d4280004a03400d10b000183e000b944009100348020118447c042c129a40c80f4a40c2c1c8404403240306019 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 707104388 1250 707103138 707103161
    0x90a020a08070503071403010308030a050906280609020a0206160c030c0206030915090105070201150308120a060f060905040c08010f030f02010207030b0703020a0e0604050117190204031a0a 83
    0x5801282c0c10074003500040d50003046070300d0107100b1412800f056081c203520a0b1310840326140c1c000308100000748a44500ca8120403250b000e41078500703045041740588410645d050f00c40480c3d1416007040036a0560200c001048415402d40d1145070f030b500003035180c0c6012203401b4107079101d81343d0305049944510760816500364140c42d040c903644040d400340061078100609550891191300c1001103101c007003440d400e11960228001140074988460028292030390400340000700c00e0525070910000d08648181c440a20000500458a41d600c42051000d09119031000081c00c001740400b2944540c0059000c040d520143c0d002d00440c0102002212803100910922008510054040c000100d84403a9949060300501c11952415140d40740d9001700c040544150000c0ba50014001551f01d4220507545000704044981c242043c0c500350000e80a81c0f6000999000c82a20a00007010075041c040ea1a00000c03002e4404c6403620703160310b0406682c00d5600c8514400d015170400098026155014003c2d2141 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 707105638 1250 707104388 707104397
    0xf060a0e1608090309040e030a1b020d02010e0a0f081005090c011b0f0b01180b0306040308071206080d020312010905100501050a030f050c0d0e06060306041407030b07020c090a020a 79
    0x30071074542111a018090842c074241e000411103646036036294081c1039000c05d240c44c00365540b5440c1c09005441c21100203444509052814083c101607640d80d2840000c0320f8080c24510382441480001907400619900111400c464000011070304810000b00c40e904601d910a0400281d100c5262103942c4008808038940010350480c05001300098081a420000d481020303908240d00d155500c80700a49003d800100d0802da220426010701c2c055400f803a0045002a00900300d5800d103510018115070004040d02d00384402c02c1c180800c82c070001e90001c00200744440550b01e0200f04880003d40faa840b000c40808044611000413601c000203125a070300964584000c05011850b050056840342c20040c400002c1c980d59141a41d80350340b8502030b0a1080908194150340c4a108030080300880340604096000342e03004000b006100e0314001403070b581003a000201858105400c086540c0b42241303031313040107086034082d10601648640001e01c0f298400e20454214000d40d64440005e8124050b407140d240004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 707106888 1250 707105638 707105671
    0x120106030b150607151b0e0102101508071707050916030f06080109140601060c03050708030a0902130b010906050a0512090c060c0f060a0629070b0f060a0e 68
    0x441014802100e5030010f4181c0d4100322403911a243c5410301d1114146a40b41c446500d40c128150071020700150840c0c0342090401241e030200002c1d0b540004494900c1003d540d00c000c443c00781600d110b100010100712080720300441c0c5509000c070042004070b1000c1c80070301c60320340085040d1620160680c8202402d118416070013420300000c8028080000071041c4041d950034010807580004e0041e20031081c040d2100ca105009208100c51410b84164810000c0010440c403007c0080c0d4000c0464500e1600150324980340e44821a01364020185d074071340290f101c2c4100303041a08072511500705120401c000d0300c0303a20044d80e0380c500c04d84070b41c4212112000040c004100030328501401c24401c640008620f82182d2200b082400843e985611080380b04e00039a0044031811002801002800c2d884200058244040303443c0134991240c43d568036100d001040015520b5414800b00c03e0262210103410103d15100381c20036900b41080f0210685105002e000855030104807994001c008074050080310783e440700039 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 707108138 1250 707106888 707106901
    0xf020a020a060f15030b0702100c020c0f06040f0609031b03170a021e0f0705030309030c011115100801180b16110304030809010f110a0605071803050705120106030b 72
    0x203240844000303c540380c2e6100d002140e10b02032a10b10340070310700c51804a226410813920103494407184030242624103060600c0d0064080d0302090280f0104401c0e9603240060709000c002442034090340c0c00c5021204190a000078129a00c80f00503401c40780a00c450204480c007003c104003880400d8040500403601d0741c4044420301c8101b000030850010701c0d1068500c902d5907181030102e820700701c041079551039101e0034101e4407010003800034100411084000354030340840030300820745802e035980c4540d050058223b60b5042241c010f004010040a100c055a81640f41c0040c4417000c8034110700800840750b18042030080c2e00c00d41140f562200ca5002081b140c600da81d03004104400000015611013008514602000340d03034800c20180000d548100303803803034075441712030001845001100d03054820442c1e480d40703000c1b902c1030100f0140340caa40c014001080c5650f41e80816100400f00c40c502541100d0459000800e111020413400700b0f4900407036100d0400454980700701c0c02d071400c1e8040a0410324504010645 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 707109388 1250 707108138 707108141
    0xe010c0206030c07061e3615020c15070509180903040302120a061524031d100f0b331603080a02071a0604020412030c060f020a020a06 59
    0x28801804000b040c030b40392281c0d0f240320513a0000c1110008004010040e8207400a10f400360001840f00c1d1f010341c208440b8540740080c0c00d602c0b44c0440340c22034106103001d40107100510143c2d94614540000035550307441048229a034800081c0c6101c00843c0d1484007040543d44500200c038203080c8010072010310100b028240d004c05000241940d0740c0c1703202c104070000060300c41075900b407225042d010281040c0c50341070902c3e10a4500101814910742040803050041940b229150648107104014581111582d5002540100707014902c1c540ca08144a403203d00c0200d00180701609113804030020b003c0300c034054081409903548400050360166185402d80b82d143c0801015038041c1c03001220746080080203000c60502d9501c0302c284c030089040001500d10600d50000d03101504038000305021031800e042500c0b460303510340c401030120880c45080804110a6034907901a05c002d00090781702c11180c00c05626004e001c02c3c041901c01c40702c483c10003024120104561080e06e810789c141c2c1d0041c064240c1b040d0745020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 707110638 1250 707109388 707109391
    0x5190c0b16030e0303091e040b0a030302190c0509040506090d050f0a03200310060215060901060c02030a17090406050a03051c1106070e03060a090c140a0b12070f0e010c020603 77
    0x44d0544400e000510f21030340c902020351072030701500b140190301c29942c00030f21003500d080d0308006000740400c03101080001c0c3d0000d528841d040910b0020740d0181821320340440412050362003c1c2c2d1115401003440300b4801d0105906004101c040c007162a00d1803072800c140c40314010a506d5482507030741403050804d0140690001d01081102c0c15000366110700340910001070f500240c811070aa031203000824007850b50104642e1101d0b8202102201051070020001820501d05000301d104019400d010101151810080d903416203074020f4008071003010045000703403280c0000c00c0d0a48039078208540025a4101006c444094a404c00050500b945004641c458900f9030b0300c001c1820030210320718541c0440000d00c0740900170140ca0342d40b542001e100004140c541140641f241003a0761070b01c1030203030014501156210458071188103580082e2400c900140c5036008980c031010341070750001122840d00b09003205041c8282c83c6619103440400303030b1020850b0780000c03041c0000d010640c4400d030000903141031006035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 707111888 1250 707110638 707110667
    0x306040b07050f041503060824011a2b1a0622150f080c03090c0f15040f06090e0403080c071707060c110a0c0b0702010c05190c0b1603 59
    0x10b0b4a05035a800c10517a0041800c01c007040040d5803500c09015021701481066102000140000300030298008003418038441882460540c1c1d80220300c080417426004141d07400c3c0382132581c02101c41400602201b0740402400500c0a180d89001e09400d40980d06e40481001960080d14007810700501035400d00c21840785c413241d4840494155400180c0100000c1b0340040e1044641c0e400c001070001ca0303000b5160281c043c0100301c0f41c14051041113401c150000b104010807004940c1842907005800120fa00f12441c0a104000c0c40740c0006c0219220350f5003100f050440d507203607840011042e038480e20403221503400e0f00d00500007030003100800c0300400201301810701c1501405488242c0808242c044550780e00260044a0280d02c074650318228039045060501c0b1085400301400795402690b66006001e88a409000c40d0b01038007040344029a44102d000f255810f0780807086480101080e000d43c1d0700d06031000b50441e460740c02280b01144082c1203070161740b844890b84d02c0300c8030b81c80f00c01d40c0c0c2900c0240441580707 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 707113138 1250 707111888 707111917
    0x60e24060d0311060702010212010e0c0d0507090b04030b09150f07180504060612050a110909040f0f260a1b020117010b0c011a030706080a09061d0c0306040b0705 71
    0x11204040c03400d01c2130074000c0c505c135000182e88018400c08480c61420503070010b0900400ba200b04680e41c04400c0840310501b681900c00601035840000640e00d204650304401c0d82202c0c04100401001440b00000380295440011200c40c0300314110407071125401140d1007140b01d10440c000c649628021800840020041302c4c9400030a0b0300e4601080848601d54000c0b80065080d41320500300c402c0350312032250003001400c0188500c1c100c1456508540c0b1034650a5405412544001001e10242d0544c2c03004899000710225880320250500106c0c81c5111003a102030b140250094840c0c142c202011142250205d072140038810082154082c00d00c651700d04241d041c00010342b00650002c2c41c501680e4040c00d01c524400d80c44022140e403050841d50700c2d2001c1410342d03504002d59000d0399000208041100c00e40e24203010305540380180c3c9406040c0305c0d140141894181038152403090080c05404440c0000c03402100c6507001520308050340c2d21411750f03010b040c1d4460200030940071440b810040c2245c003d201c10 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 707114388 1250 707113138 707113157
    0x14011e120c090303030506030a0b070f0e0a06020319030e061b1204050d090605040b040506090d0b07050711040b0a030809010504030b01030b040b010b2502040b040504060e24060d03 79
    0x1803001a15401c0030300703200148515a040c020160584119600504154000e0a620380e517aa14540003a40207010b200901402403c42c1112510401e11001000e01c090320a01742d1559545010355680c100d942d2070800e0791443c14100a005200740b0230402c2901a1030006c000c903032a0310440b600381d001036404a140454080040c0d06584c101c94000e1030160780719000030040310040090040c9904556003144013044002c00c010000849030034180e13815260115601c07a0703a220480001026040a040e008210400c00300c204030350650014050000d06010744004010a44007104110459841d1600c41d075001c86240c0091000c04c0c4450043c0164500605200c3d02d41600d03503c6443c41807500764400c40c1c40344499420402004000c020780c600500442d5841400c0040442c0c0a51138207140030810040c102d240500c0100f03550f03880e003003008881000340040003c1d050504103440504184040400c085c0b00b524181e0500070781110104807030701e0b80074003680c0168070340208101424800b880203a003001413545 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 707115638 1250 707114388 707114417
    0xc0504050c0409180302071d01170f0607030c200a030e060f04030b010503010b030a0c030803060d1515060801060c0602070204020405030d05070b150a06050304140706030b03060114011e 81
    0x205802002000034130000c09040c1c1894003d1070b1807025001004030511180c10019030400013160340b0305403070015695a200560f143d03860392414140346450040341c0b144800744089147c040c0d0104070362200b19501c0480c40ca2020440701c0c3c070182002110b108a612200308240400d2007a600070764400c400510f07152a1032101c1000035041c2d00301c0e400c03e0380c5038181c0400401aa103001d1042000040064014200120b40e6845a0480c08407620018061480c0040000c04075620500740d1022103038800e88040d00d114020b0344071802011100100006c00c02d131440042407403801900d2082c101c4001c1e50712811403003050351300c0d81c003e900140c0040360400e400b40008901c643e010302c00c4840105460342c44035201c04650902c0c042114001e08005210355900491540c2600c0b40c183c43c40030307100b0030b003800c9a032611149085845c0c0040c0744540020343c001c4200118106606410070641558101d040383d4507a41c980f132806200c904411035450216440300a0b01d1504c1c003c0d48042c8104481e81c2c1081071f902c81251 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 707116888 1250 707115638 707115641
    0x501081f15090617010815090a0606060804030e0109081209040b181b040e0105010c0305120c21060d030e010c05150a0c022d010e100207140303040c0504050c0409 71
    0x4540640071902d8440240000d0358040c12884151a54154503406035260440780d82d00d81d048110010340f01c00340c076800501c803180e080040020781607008201b0021140e4511000300b01200540742100091000d00002c51258030070f03001c500c2601c5984000e820080c0a5050a0002c0c0d8024040c0c150015107400300c0100303d6550b660281440724003049032082500e0055200c41180c0c1c540d015103210000300b030105101014241910300e056a0003800d051041c402030f800c094500e402640e901e841c0e180c00c00d004000c50480e00b0000303040c0c0c0400041800a9104885040361030100701200d0b107036080480c1d40c9800000c00d20440741c0c5007882c201810550340030b807004e481d05801c1210021220700c0c02141d1900303202d4540c216104840011150b44003410140307000d0f981008541201c0110502c92075201c080b03582d0308900c01e40c0f009110000c036400300c2e00280804001400a500020000d072114443d00d003c4d00100103009c011240300d541d0240d003400c0c115042400f00300003444090802039a105044c030020a616089 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 707118138 1250 707116888 707116919
    0xc02030303040507170a030507080a03110c010605030f21090111060108030c1b0f0103051f080c0306011a0301270f0b090901271e1514010501081f 64
    0x500180c44c10505110714001d1120030001820f0f1141d101e07200a00119034402c00303580e606580306200540d200d80c0010118082d00c1c00210700e0300080c034002100c0c44d01880541c00201190700c16026100c001412070603503a100c20f40040c014582d00034004070b4032240385106009000100c03050614440b0384141c081220b24144098101c605282e10002c1c00200707240c0c00704107160400e901c03a030030004920003d0000c290750f0034451824605251b110008114211144100740e103003000c40700ba0451549a803203c80300c1d40e40b4a8840c22030700074092000082101101e0545032000da4010b081914596440c0408030500030008050310741041400013058440180203001e04c0c1d00310344c507018021444015082c104038075003030060310b90b021980c90001e548195444240d009001d120b42c12410550444060070701c40031000c659000748076000046c0d00d81d4001c00201c0c5805401030f26900d002045480010021031881210178020b050110b860800041c041c032452440da511501c914105404845a580d0003041c900406c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 707119388 1250 707118138 707118143
    0x1e0a0813030314130e090a050615010e03280602070203011a010206181b010302120a0e070902090d08071e0803150616080a140c07062606040c0c0203030304 68
    0x120380800615a00038400e1203d0300b0071104152a10b00f600f040000083c90300c1c440c1c00b04a24030000005c101001c1400f607031281540001c10703a21b0030700e0f140e04c01007640e0b010f014100d4045031013582c0c0c1d0700f806c2c140000c0405610710541d42c60b400c0a00140715881c030003000030340202da046800300640c0005031400c0c010035005282e104151501401440c001a050080c02020ba1039001d14800000d84c000400080c8514015000c1c1c819500003d89e190040b406849080c1d1094240e00e130b11028410050910b134480c580c40511001510501c0da00c3c0d100c10801c0e44034041c5040c0c0e101c3e2803403014402003031260b001004d800d0b11480040c0c0450b12200d003c0c10000e44408015102d122000c001c200c0121808107501d8054081207403103d01d0300d002e168506070300811001d0041d04a0b4030204108100900a0741c042c3d041e03c0200e0b150649501c0250b00d540e50700c0600303004510010301310212201d00304901b490904c0041d074a8004078641d5654050070b000052820000d52010045c48050110250310709000440c003450 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 707120638 1250 707119388 707119417
    0xc0e0c130603050f060d0b06060a020106090608030405041112150d121808070609150329100905130e030f0c030706050907150f0c021f17091e0a08 64
    0x4c0c2c0700e0707040140c514004109030b01500c000c400c10070005190004880c0d004c001110001d48034070074000c0490040006402c00180c02c0e2508030081540c000010283c404c4580c00c60302400b8041d107001b089034880c0a4504404181880400850f10312001c0b58010030703180c6006040010030308031a485a070202c00c61079001901041c04034403501c0380030060304100c0d009400f0641c02042d01d01e1801c60010000416480764680100c120303503141100c2c611a400c01c50110440d00c01c6030b450a030704192041c18262001c0c807031500c14498401001030b1135020742145011140300a00303800c2d034205888110700240141a0150070786001c10040d4079035400303200700540801c252000096440b040d884c0f814404407a0054003404540d44110300400c4050484852a0700003080b51408442e0810744400c242c40c425000b03900254882064107034052021248002a101082d10346d0701c00310320004118580303c20050607036520000d6080030440c0711140c10081c04801c08a411030040f1041300304e1584411000d030f08032807a00c64016 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 707121888 1250 707120638 707120641
    0x61b080f070f140d02070902030612120c011a0109140a08030a0905030f030c0303130c0f0902070b060a0302030309360402010906020c030604031b050a030302041509030c0e0c13060305 80
    0x222a06005500199000000300f030183c13440d180107544c0d50001e00c2031041c220f070000001003e580724101c892041e00080401c84900c3e822590040c04107400440c00801c16601c3c00c04424a801000c3c4080e981e0480180c454604281c140390310228071050304440b4a0708280c11080000d40d607001007008000384081382d078071406140d0820307040500742103140c0031404603030340248080c00f100e040c0841241e4200f061041e40200218461900442003c4a54004121400083c0000400d01c500d03400a007a114481c2100700401c0e0341b0802080107000650002039010f501c28040c050341410603a0118100000c2d100d480fa20300e10b020b0301105541902c0100c80820a0b100505200444d600032007400003408103030010b040f1102c0d000c3e003c207544a200030400341c204800c60880b4442d00d4410528403a201c1e07001015104048014200030340a54000c1c840c4040d40d100c81c442080c000c500c0b84d00010143c0e0f41c02550b1061031498181c5170300402c0b43c05056005070032010070004201001c8104044020600d903140454076 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 707123138 1250 707121888 707121893
    0x228030e40050c030105061c0f052d0a0c0201020903011b02070b031b1813090311030c070312210608060a020c0604150b04141006020106061b080f070f 66
    0x480110559007001c1c505007418094216504800d03a030544805a070603d49403030700072106144842030550540085854048200e987c038101e608182d00c104118003100c22903001c403002940b2040f00d191001f004402c0010003003180d000c3c03103030402c6020060740d01c009070810154400090846000c03450141100c0fa9121030819400c3e014040310004100c07072000c2030f0941c41d01d012241c05040001c0b038858a008800074080090b494106d640b555443c0001e44490341080340c0c040c2000003020000c800b9404140101c00e00c0461410002c2251f00d5141c2a5010702030b03643c0b541e50b401e540a0f1a48001c5811b0040d00b107044003140c06002e00541d4904007500e4041900c1d032503d5103081c284034000d841160414010070030b41e000f062000402c00d4006502c40c0c014900746c0c0b9844000c2c0010310040503220350007410848224542e10780c407110b40d4090f000f50620816060b507140c6040e0f080710114031034a404034280304040c1070b9862170444403905050041d0a42c515000300e409280007141e100070000ca4100c810400070005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 707124388 1250 707123138 707123239
    0x1c12030e1e0705030d090b1b12040315110f0702010318021f080a020313030c030e0a1e05030a03020601050d080c01110318150a02070c0e0906010302010228030e 70
    0x5600c41c50700b00344280134285201601c442c401d209404c1c561442101b4248d03a9440e08100d03910001c1c00e083d0a25031155201d01c2c01c210160740c64000d050f885800c00102d15004001c0f6012038400c52860b0f0500d900c1c14046500550182c03c0b160060703929038402d10b40c11005a29611002c41c40c84142445840100128120203000c0328070107080060214814402c0202a0200c0c1c4680c4880e15014104100070780c1e050b00c0c0495400c4859046603402104048000800903017147c06a80c1d5140c000001c5100e00e52940140340e40c0d81840d0b1000b40040e408140104007a0802184030440f807400f905c4c4041c90640140c0d00142941d10203071510f001d0242c0042001103a200c0b0301803030324916005002a04541c4c41e100100d1030b4000d005000900c07255070008000041006100740b140081c030141001c0b6030130b4545a03d07000e480303400901c001e90150080252000c2412507414164800307113441021000410007540701144d4810300450713126000b0f00d2424803205440708003016042e1200300182c0c00000d4244d010005e09 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 707125638 1250 707124388 707124403
    0x11e09050c0a20011b020d0c020a030605060312030903091c0b0403030c180905010302091015031a030a06050103110a0803030c03150a0e04021c12030e1e070503 70
    0x50586400c040c40091a01d180880d00104241d180481c0d24101d180750340c3d21070030340610b590b420035840c02c4040c0801c459440200b0240c81c03445d0302038420301c0c1c29256094488028180c0003d50100c0d08610920004510754002d90300304002400316000000c1c580d4014107030380e10035148520650f002050003d1103150041c42402107000304050041d0f00c48041da07804021130f502800090038981c88404161100d031003001ca4035030882c41a40400501c50792400302100519080c0016400350103040009440c680041d41103004440314034800421180b0800c108400504668510308064800c03c1844c042980e002c0010f12001805000005129451494145009441c0e6005180124030b04001003100480203c1901d510041c403180196a0b656100c3c0c4040e00d0300541e05403d85d200e01ca860b400b00756299240d000c00c0c0305510170b66640c201c402c0300504007001800d4036500101718000810412480d00d00c070750032041d051240a41200c42e0b081d1030124201a410b11100002050f0303010a4081080749000c22064 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 707126888 1250 707125638 707125649
    0x180c050f06040810050411030a08030a0c03020901090b1c0f151509051905030a080a030501090902150a030905010c1101050a143709051b090a23011e 65
    0x30b85840c0c6844140d588070980c14120100030b80d40c4000003024000c0200c40340c40d460074000d0540701e000c20180b9141c61503410564040300400d1802000c100c255010740308441220105868403400c06140c0303101c200140d03020391640b80c140c00490b030f44148101c0c107a00a80f10b40c0c800d00400403400303680c1600614403e10280c0c1c081250703400f07008841d4075440d81010300c10040c0c0300180d0f4200c03034141a442d00c80d00c0c859101d500a0340c1622459441605021002001d80070301c003481d65082c01079076039031031650742a582d800e000651f1144417803030f2060b610b505a070003c25000c3c0340c50074081f50400713030358a60a00b1151524002400f261880303c0015070989c4c28466142e00c800205402c0005004856400520140080849800ca89540b80d1203089811450300420f0920009007000306801d441d079100300c00740c00390312811907261107049580c080c8103000c0241e103d64031101410300116a91a5403c50014000507401a42e01d6048100c0d2807c0040304101e041c4d001e0040310802100d81030304154214140d00065204 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 707128138 1250 707126888 707126899
    0x160b09070311060f1612180506040b1606060902030a1104080606090c0c06100501170f060105130909050102070218090a0602070212010507020d0917060c0c01180c050f 73
    0x51000500c81c1a11070300c28281503c0e490744074a00e00003081154070803034481c240c2101c0c02c9040c100030401c2d90201800d01c070b14030750345105203040424017261150f402c600546921680521050000000510103000742c3d180c90f06401e551030215854080443d44680c019009540c0c002040000c81d030024000d813190718180020451400b031070100042e48481c000307400c4520a8a00c140400d649400c000252040d071a01c030415a051418218a1034107100014841c40c0c0c0450101502a000185052401da1207001000050201135440d200111840c2d0310002c01440140405007001c9040c5085203d40301c1e0041c803c1000603503951540c01046103004040b081180c1c0e01e5154810440b00344030114009074103a90010700035840f0095480026821111940c513010341d5840c1c0400c100c180e40d0b0000d1210000340072610794220041d110b0481003000711030b4020060081c1c0c88500452151010310303005240c58003194000051003841c80454018250040c1310a6034001d5a05c07901340300c9842c0450b5401c81c80c0303501712034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 707129388 1250 707128138 707128153
    0x314130203030d11071b05090c03041a04050f030703030b120d0c060c03090f03200102041505030a1b0906020c01093204050705181c2402160b09 63
    0xe90b20700c500c6000511241d141c1e6a002d0003281090191904582d0021155441d40d807000103804041d02c81c0c2c8159441480310b01c3c0450140300c0319004990080707812203041900c41c2c2c10f0702810380343c402001d08102c80610a07021a60b80b140d00c280040c0004900c640d50114a0340350361030800003d400f82007a914000c0e08001c0c812000e1580114100c90900d60003a00403850000b4000160000d1035007001c05050040080001010994480e0414030740b521071411003400c030b41074605001d00300d0040d801030b448003513205105440d84030b004401031507005c0041f580104906120051000c444100742440c40c000c5001d941c402d0000341d0301440030403031100003883c1c00c2c468131f49802410310044c01800d81c2c80600b0680c40034400540e032165a000e8801503000742051005040038040245075031b209c0c0d080c1c19840f452541e4044802d180a20800d0b0745184050a41070f801074854403000b500c54007104100740c15410100400340ca040b5035001500c64040c02d01a0070b064460b8174104450400001801040203030040300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 707130638 1250 707129388 707129393
    0x160309081204172a0306100b0d0e120d05011a0c06011202040b10080a0614130519110406030c02030c060109020904140408070c06090b03070f140a031413 67
    0x10550b0200e03940c1c500aa0003403a000680c03103003450b0055500a020b140403242504140d14501d41e80883c02500b81c0c11220141d6940d10b0a07483c2e510703d8003901c10000c000b009481c843c07010541044004102c41e0055132005041031701d0100c4181e2245000c8004184c580004010b025451003150515803003a031030180c5003203a180c10ba15102d00c414050a580052001d1400055450300c0e801414180700107480c1e070042c03580c01d181c06400c90100f120100402802c204020440740f004206804040030098080c1102c070452000342c0c0003800c401800c0e0206e00c603114136030700f1046003103005100081b60100043c1d690745003032003030080a45144084003c03e6520811056052038400203038613044400074000142c030f031440d082c0014060100c00310324100341030300c24081c48140300000d0b0041820390300c03c900d52042c256035200d003580d10440c2da104035403601030b040c40000e95a0340942c05018440c0c03003502d00f1044d44807401c07200302c4040d000364170140300003035aaa0600d10f90112207000583c005407101d034010303d12507555 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 707131888 1250 707130638 707130673
    0xd050a0e120a090603150302120714010509060304060203071e030203040201021006050d1407081203160903020105070602031e250801083705030c12091c020f030316030908 75
    0x44c0300c0d100404d565150813200034840411210050b643c018580103001d00710021031a62000340740a00d0b41c1500600818504a40c040c408851001901804243c11595142c48010094100030311240900c00315800306400034000c00c05926040100e51401600d07030805000080c600007241c41100c12981c903201050005907100140c4403c0135901280e040007450342400e005c1d0a044043d80101600c0c071070151050160083c0001440c841c0c5805201c4040340c10070080c0c111840301c0907210213804200c0800805001c60744c10f400850344106000400300c080342c3c000802c3c0c80309050403070341500340d071042460405108101400f1008141a140f900062030f504001500b900c1e0740700c10180c01100680c21504405070003214600e41d00e103c0c400150240d113551107060040c0c41e940526014407182c040c803d0300300015041030003517584194028265001c0c0303049080b1031118180c1d4207036040c0d030311052001c0e011905503803c2000f0a115100100180b0500c40c19280c0980f091075140c0222800c1e4210340501c41048408 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 707133138 1250 707131888 707131907
    0xc06120b010e0a0e07020a0c0909020f1509010804080720130905071401020708010c170906090a02060a030b0d200603040b13030c0c0f1805090c12030d050a0e120a 71
    0x1507403d081540c646117016440c00c815801d00411000007031a0018815059070301040c6440d000756080c0303040302141c00030421a400318044004e4244014030455a0552080700a903034000d02c2090040d03d0003009868130207401c04114000041940c1c05072915510707003090910130b000b0807040d10060210020030740d01c090300c40440e030160320402101c0c2410300e890741c1c1c400c011040040600380003c0212002e102e42c0146482c034140e405640854002c000f04002040029805226120b40030146c80c038040c05900300700082d0b00024426081607142c031802d005542d50320144680443c81044d0110321314100c4010f1040548403040300500c030344410300402c00030031301c8074902d240e015101d042c103500d00034400d00e01550300c1050b440c4040c01843c010309000c900550010203813020f40d41040152203c26030000c0121061310812110198035400403003254030507007411a05000440054003d482c24010400b03007071030460700110b5032141c0094641110200d0880103102016408880085a910700762000001411a804 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 707134388 1250 707133138 707133149
    0x70b07090b1804110f0705060714280c3f05070803060621062416051e010f06061704120905040f0209121c0302090307030c06120b010e0a 60
    0x848810312181381c440c010845400d650b031528460344641030760908a03a1004100d03914404107403007654041c0c8002040e815207901c142c000718240401d2030307444508015040101510414424003000d05e400184c00041180c855108250461001c1c054940c3c1e890050b805920803d0680540e40b0312112040c0d41c0102114001c6400010155981c0c4030780021500c24490302002c50a030700301c00c14031103000c00100c1c001c0b0350183c0c8045421219680d80c803034400404002c0c2800d10380b01248200300c034002100001940c25100e50080095442041107507541850081030910303268400c1e550b803d07100c50310000c1c9204540c0a800c00d0f10b450030302c241b00e4402d5400c0701c40018002402211032440d0390000c651240803004082d1001074024040e1244090f07440d4041d42048500c14841c2c1c4507900704036018600045c080f07054805105501c1d000228900d0240c00035401040c0f600c1c0c01d0b001d41e500c08404500e0110010f070041c00e095580302c000101c9062102c084a107008842c90421064a0b00d01c07a4954030070219005650 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 707135638 1250 707134388 707134391
    0x2f01050f12060f0a030c030311030a05030112021807050409150501230f07030503090d030c0503150a030f0516060c03020c090901021303080409110f0406110f0102070b07090b1804 78
    0x122141c001415580f107900c03801d84d1000c1c0381d038408010444a050f4240c102c03840303078941d1041d484580501c0d40d213a008401c0d882e400100140f0040141e032069544401c5024001b610b0301c501490b80050003881c00750111040303004100001020081c0e56a517110399110005e044400d0540c090406000800f018034014016202120381d031100c00087c0c00b681c0444a940031007001159a4560900e00904260011500d03c4003034054208241c544a01a00a40072088200c5c4ea88502c0c56841e00079640301141c01c130401c15080700c4000400720000701401d0b03100c072140b03001d00c0003050851701113420345446684a800c10410402c010704c1e60b1002980020340c51054100850b0745120300d54401000a0090003010400001ca001502c1c0c0003040c00070f4400100146d952550041c08400501c0b20070034030703034843e00340fd080d80310354100000c1001c5842000050803045007502940c0001180600c4642a40c10811080d0342c015801c0d0140010f460304103032504000d055100c281d42c1072140c4903551503c84103201d41c4041c0120b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 707136888 1250 707135638 707135641
    0x50c070608041403040807031101110a03050c010b03100b0a060c0807060c1205040303150b0a140d140a0b030606010c02101103160f02090a060b04060309030c2f01050f12 74
    0x106a00e03d0a400780c1e01d49004a07911503948501c0142c0d51041031200f600d8008800c5414180e551051400b00c1092100400508003110f0980d0b04484551100710704101656940c00c0d5000c0a90303060140706da0f0701d0400340c80030518005120801031080f60580c010002d1000a8500d280007940a5040d9400b080e00b0000014400005503001d540b180e001c40820b204a601c0c1100b0030041540540c4001800035000400484031611030028000038840e403200c00022a10384618286220283ca0080240d4580b1060204d01e103040103101404800007645c200315942d450341081351060404100e03040e0701040901c0c3c01c8058804540100b600380c200c0301108800c0109403484001c440404008896007404203001081c0500c3d8241400300c2481503d030412803140038203a01140000703500d40074035010b551481030110718003071400c0b600390010300c0c1c8803c00705e050110300803189020806400400d003039000c00741081d01c0d1039800028200c5003075611010041c18408240a008910801601a54001d07030310141d024419 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 707138138 1250 707136888 707136893
    0xa0e06040b0901030506041203021c0b0d0f0b091603020907080a091205070318030809100e04090c03020f09070e011b05010f0c140903150402010509040e011b050c07060804 75
    0x1900399444095000382c01603000100300800050034901c6540940680e01541203410822026032254400c00050503000c2d0260101c50782040c0d01002180800404142a040c403650703940400341b41d0501e040d6000da50940800c40520011722204d0b041180a0000b140f403641160b00090407040b000d4220420030055100107950105154051440390341c100c151040f8040d880e500052003644140380440004140340d0060150704071b03401e80030742942c1d4890086c03030a03c2c509105012420b005400c8200800650b0841e2504e241c40d644200103903a4081c1c800491343d54154014401c078240004481c0d030041d0603020800c040300f80e2080484c010a030f0246000c101000c505880c1604051340c030540039000c4d510b0040d00140c0070b101940140c03401c1e02161502c0c40c94020161503003036031303010303505000750990010108000c85d0034001e44081e92242c41410302e03d0502255501043c215000c103420704096039034400f64618444010707a440a12500c082c64494900800c0c1e0344050381f13030405071060030144060035011804 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 707139388 1250 707138138 707138141
    0x7211805150706092102011d060606071b030507061106042303091807030506030a0b010605131d0601120e100c020a020d0308100f060f140d0212010911090a0e0604 71
    0x2013a40c02c60b20b40c440d081403101340610008410008000503600e81200030f0410b1203012020030602951001405c461b548003001d000031035000310012a5400c50142d00c41d160036408845010245029400600402e03060200c00740c02c4074031600903054244d008004010018050300e0001d888041310a42c080c54442c1c50324401072130350040080c0b056005245c091078031910408001392030b110340555902801241c59110505481c0d854401025000360702c44401400202e025000030195080401d0031200d00f56a9008641c510700e4603003403003025003409a41800090740e84001a24411500754504100c0b0321100ba007001d1341d40b000d0300ca502903196202c0030300301843c5009125503000c15401911907010b0359013620b40205044400ca8890141c132800550200300c01648000c688107681c4241c44c0d881610021a805450b40c0028003041200e0600c1008100000f03921030010300b11a888001202c90a541461114415601004400700c0c54070780c144031800355951040106401c4418100100ea8643c0315140071a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 707140638 1250 707139388 707139401
    0x110d0c0302100c0c1a0c030f0403020715050a081015080c0702090907150c12030e160f05040506040b011e03020c0304060c030f08010609060f020307211805150706 71
    0x8858503103944410710642141600c6102840380b420306442140302c101c4500c1d205ea0560701540c40301c406100103a00603003144a0780c1d4101d4000c0c012510205e41c4d911101c02400c4460170410300040e40403d000c0d0081750080401500034060489040705113081151180040450603000820082031b0004541c45140b84401c540c081030300600031010b580307000400e2070b50724407e5121b000100d0800d6984000c003240305c0d80700c50f6015540b1841d2140c0b41c025440044000d40380920300302055016280c81210020120019080103044003401c0c410580d02d04002c2204550004024600550401c0c1b499201c60f80d028059103240b075402901d10940c0000c40350300314024000c6007503c1c0d1507840b002a0208134203810050024100f13206e0350f00c00380d030000d1100080394408000c2c400d040100d2408907040c086180209001100c1c49075502c101da040410984481881d4612070103501d4440010407801425150320144030f4280a204e141d00480252030103011401c000d8500803150030302c4030003043c0300d001c0040320741201 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 707141888 1250 707140638 707140663
    0x50a0c081201030501020c06010b0906030627090c040e030304150c050d06080106050a06030b0a0509180a1b0e070e0906040e010e0d091d1f0e010e01030c06110d0c0302 73
    0x19507071030b4513125000358044c184000c1d00344205c100000e140010301c822a9106c9001510190554444900b4803200f082a8580ea0f291000302c1c00c90140000102582c03144907040748001000346c402c900042c80b044501e249000c41481e001041048042105a80d841e400281c50080002d6030b2408640101c0b02400743e1015591081d061810000e44000150490000e4072000c0322000c0303449075126001e5007266482c44003d07411a00a910070040c9182c101140baa00c15881103818100c440080354250400250140889020812140c481802c804144054019188074406c0d8542420030364006801442002c0c4250b101b203951a0000740151269000444100035141c000e110301241d07600120b031a0b8074034103005000100442c0d000035400701101041550000003100016183d141c80d15040b68070446e4080041d00c040d003007840002c50030304004900f0700070f050520f00c0040700d5040d46412001074004d40e00040c1000704501c22b2141501010505030b2030001d540c1840c2142112a2401364204561210b04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 707143138 1250 707141888 707141917
    0x130506062b0b0702060a022703031b01270b010918021f0e060a0903110d0f05060a1b0816090905010801090309090c0c02090c0c01021b06070f050a0c08 66
    0x3000100004002d440340140d80680035140c265880d031388480228040c0c00407500d40c04400d109082d016074140b40208202c0d05000c1c0a4a2410050200300c130403c80400c0381c1c50301540e65802040c0280b0394984551203d00000341d10300780b80c1c0300d01511040b20307445044c003c140b442c641ea52640340a0282c2c00e801c2642e00c0754043c2c01c60380c00c000d025551000031202c4a40c000c000c98103c811403e80c0d0320b331940031a082c052203500d51040e1075003507071600103000102c071020035084150303c1c0303840300420400c224100d80140308100030100303440c00d081c1a0041c0d4450f10a402d0048420f518100101030304100e9407136100940038034121044903500c00448842040c1da0045542d40d14080007c501041c06401c51700d0307154001c0c3c407819245a81d40d9045800c8464040070700e0700040780e8420742030051429580031900124240403550828500c0031940d400c99100500003002c1c00c4031008641a1010300f0b000c4198049800d0400015082940d02d0141c0b441c81003c40310720820103502024010040010140c41440b40310485 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 707144388 1250 707143138 707143219
    0x10e1b04090c11011805071a04030204090506040c060908030d02160c090b0f010809030d02090a080609070609050d02031e03040f030b100b040f0302060d0b040203040b04060513050606 80
    0x80540205403030400303c900f0794245000d2030320044850016a501c198860018070703847c0d15020091541c805c0301500c00640b17400400000001da500c0e8000c4140745070080c0c000e44018101031505582c0c540d038590200003408604d4004201c2d825010041d0783e1109042c0101594404041a175000e08003400c0710000c140e02130041c404108558030350300031012414180c400b403050080c850300568149104540b1b2900c1d9074003c2102941d086102c4d009090074400c044c0c04041c110fa158503e00d030034a1400c0712400441d90040c80d007000340541c40045a40106800e881d075584202890700401d0322109807041841000100d00f01c1000c0c0d400c01002150010b101e03804624041c0b94803440c0c01e11100409460546201004017000300e14084110101c904aa440081c0d43c0d604614540c02e010301c5800c4518032400d00c07a6100d055480c140c4a0780003c0d44643c0c483c0040c8900341c981454444202c60000d011511009003688100002a0000a0542c1c0040d02114141c080e901e4012918a2240a002815024018101 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 707145638 1250 707144388 707144411
    0x30b1005191a25050606041a040c020703050d18060f020604020f0f030f03071101051314130f0b12010213050909010912050d0c02010504020907200619050609010e1b0409 74
    0x80f05144140c41401a0380d880e85030b20b410403090b9109503001e40e840e805068269182d606e03040e40409405c001c0b03401660007595032925003504040f0000c5076131010440318140c500504401c242c0c2400a44003e0801a0600780c519400958844004100070700851078100e00c04016600c8440e200c0c06110010304490b90003000000054072034100381d8003286c02103880801003100d58047d0054448a400e00103881808525000001c20102442218580c1052412201009a003407500036150a403032035804c08584c403590314003889086080000e9081140c2d01c140042465507594040000c2103a00444480d0340783d407550210300b801822401c400504c5000240c0750f0104058000c8040d040344501000c0c00c000c00c04540b00203a00fa40c00454009600682400c0000c0e0721324004c031352030b14880b49444444440610601c240600e461320a54100350a402e640004101d00c1d0702e14000c039a403200f015116840c132940340c00c0d511700010402603ea06d0319034004c20314810f400340c1500141c4006044046040c000458807a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 707146888 1250 707145638 707145697
    0x3140c010605060d140c21150607031106090a030f03200403121101060b031803130602060a0e160924090605040606021906150807030b1005191a 63
    0xa501c1d210907282000603410064040071f55401ca0368024072a0040700e182903e490240e4001070417402c10019062862030552601d0000c0c0000502c66140c1a0300c0450784c10220749082070003803c0c482c0c1e81e88084140000030364004c800040300026410b0200f84500807014168a10b4002d11002e107440101040c0001805292881c0949004440d1110007884071900b40043c00c0e02d819000e09100c00308204041000c0138201c0701103241c0201d221094906143c01c49226640703e0b034469008800680c481ca0a0141c00a107510481081a0008004004035910a10840d030003416610540e0712039560390342045c6040d00d0f00e00b0f0203014007080d0100c145020f074450701c1d0701c801030400d8012240142d143c604046101c900010340301c3d804070742040d45105801e030310b0350ba80c002402543c06119010603c1d00000110307102e00300702c0310014502c070700e0301c030900ba14000c00a0005541540e205500c42c3e8003420300c10400c5c502c0e000c24507081e217a4404c0300e80002c28525007048014403071031040b0004083c0e8036902c02016200c2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 707148138 1250 707146888 707146901
    0x3004052a040221010506310e070c050105060109031e06020c100501081b090a2406021e011509092102011a01080705090f030703050109030c03030e0a03140c010605060d 73
    0x481c0e1843e400c0b030762682c05114081c01850170503c10003940c0034511010b681c81d11240d044404844840d102c495413506440ea12210703003604c3d40e201091080e605082000000e00626600c40001e01e0314000c054595102c004000f61005521020004454a00014880c140d0111012107901d0001c460540540150090040400740303c0c0181900032400070501e40d40c1d030202d20b10302038403004100401a4841000090040c4000715841c0c6c42c550b40d02e071511011129a4918000030542d40d00134007540d4142c204030001791100040c00341d110741d01d08643c22414001d00c01880e426035408250000303c0300c00c2c40c80c0001d004045210071f028140480f1034414a1140c0c15080034009002d140366001000759040d0054445500945420012030424006600c582c1401ca038a46034202c0001c003159291030340ea44444e8211050402d06800207040d009006061641502600c2d480a486100030305c14900c1e291402858224070b03034021888880d00049101140308250000c8024007001082c40759540000003206008022 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 707149388 1250 707148138 707148187
    0xa03020f063f04030f030e1005090114130b0403211406010f0e0916090b04090e062a0a0c0b07200a0515070c083004052a0402 55
    0x440c010802c2c0c40c203400191070140307a164565500020108030103402500410034a100355100d20000e800d0351600b2400713414003614070704000084c140b01c030021003042a903004216001c00b150b403071480800580c070002c1040c1e00c01d03018504810b49540713101c424001c040d01007003041001c0d07041c400c07910984803d0201242c051070090325298242c103c000000e9800c0c0d040340311811360001411000414200b500340c1d240050150510b480120a6100c1ca1400c1c150341003074001c50300ca1550b80c03581c184010000c00c54a0780050703621700c00741d58801d64030f00398542c050341d4503101709941d400208403a00d059000c1c0310720714552a4040031000c598030300341c00d0007030900d0441c51090712942801018840e12308404201d01044030b4209000d000d0880703a09803140c50020700505090100a60360705c07080040342a02c0c0152842c4007004900c00c885241103403019490400e07180b814040f510148084c080020750001d00c4948034203201309030481145410500500105052940d20340150001801c0e900e40c0d41c0c41850505543d5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 707150638 1250 707149388 707149477
    0x1603030501051e1807050c010e0609071706040312020904021c0f0c120c0e1c0210090e0a0c0e040f0e06070f020706141c0e100b0a03020f06 61
    0x18a800400d0b039092425802a404c00620500010341050050081c0d90000e903030306109140c010a815040c0c00c4980c1c1001d000080e801440910030050401e00800004049000401440c4d2428800c072989800011f00020103000e41c150000c04881441d8054540302040103008545800c5800b24000c010443d9090700c884c0c4518084c40710020401c1c40c840c0280d410ba19039141c44020720080400d0b0000c000012481c014002103111030703403696407040c45040741c8210080e510f49403490184148448003d11101301018007020360424800e00b001440f003154420407550340070a0146107520203a62140c1401d1110381c010b170a0031004045c010440e00003da6404a05046664682d200d00e01102c030350541c44d041e0401600175440411203e8401c101041c0150081d0703107000d02d415200043c60700d05050014018000301c1c0c4402020800c0340f001e00401550072041c0d5014480003080900142d003c800c54003000b0b01c41c3d081c034040020b5684414040d01c1030120084625030341d49100d42e961141c10341c205e0200e8807114 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 707151888 1250 707150638 707150659
    0x7030804060b10050f0c0309030118200f130e2d01061518051305070e010306030206041206020f0c2a060414010c1a060a0501110703021005160303050105 67
    0x90900f0084488515850769446090804404c0b0803405a03101000c458020f1105016401c0c40d541c0a100e480e400c041400110481a09903160601c00201584a80854014007007041045a160404105a051000c444001544020845040040005a0103441d40e0b04c00c140038004208420141100e06d404020341c003482e0700400300c2540e420703a420b50084a2102391400e1740e030034055000f926003401d50a0200c2c0c0148007030340c41d20042001d07006001400412251640d06010318990001c0c02400034440c06c0c60144402d03415074020616511170b510038121008424120001400565410344551204552405640b0308d20344044a90f01c401d21021202c8000b104d0300c1c52a4032400040c0d42e82c499080c080d01081c20145401b62000b039a00c2d1070701c5101d0601c40000c42d400f0024400d0515400c0d41607494a20f85800d003448010302c580e8809a4001d00c0c1400700b00c1941d0205681d0014055040720f60446614041076141481150755005000003100c001026000704d204168164102c0d506860058070b028280 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 707153138 1250 707151888 707151911
    0x1201081608031305090c0706111201050d0f03120212010b1801050319020711030f061008070303051801031b050304030e0d08090906010e030a0605010f050301021321080703080406 78
    0x200d00c1600e03440d0008030081d107070400842c24645d0b03c0d294414000180c05044c029240c5904058038200005480b18580004042030a904c41700043c1e4050307d01981c480d517220849035605400303403040f42c0020f4184000c003080450004030381c0e0125a6242e004060300c0c212035948940c11080e94110300f402c5514403807544001c80c1194070520a5034031804883d10202420b05040c150030f0002e41c0849070581c2c00b00d0000a07513602030348040081541a54a20000342404e140c103031105500c0041c940c11009054000c0c0d0020004254807100750384a054501201d8052040000c0040e002400b0a454074508400008e01d450122034101010f1440303a0301a17181d05070700011060400100810580004103289400d10443e030f124180140801e9120b1018100300550040c200c001070f03d04500360104844950302d0b00014000035015040503802003005400a60510b41403070607220314217045010b0144c3d0007442c6540100f40414400c502c280d059084031900780e4541c0641001031200d102100c065542504054005c1035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 707154388 1250 707153138 707153143
    0xd031d150421140c010b3309011d19170105090601120f0f0c0f1406310f14030607020d081b041502030c0d02030702030a1104021201081608 61
    0x148058280da403005582c4030940880c078984c005908403103140d0341c2caa110f00c40f552142c2440c0300c0d020700080044800c0241144155503000c0c451150125890360500030705019981003000d000707500620001e000858800840403c40d40070690545820704a41c04c9000918403039090703582000045940024030080e40e84600440e9a0306007072082135902105103509202042c41d103800d0804403840b40c6183d2000200c0d94071100241481038100b96070510072900c080103098a0040300c0354190b03200350703801c0382012003004c911000d48920700d094200340861002d1854030001f040320b040010f0520344682a08503505e13001201c1030000c0200d25180203110700e00200710b60034000500380ca000501c958625000d50360f14905018000358803e0b65081d0b10f034040c0000308a01c0d42031201160707102130b02da00030341e295482e181001e8a0940c44210314800d54208100750405600c0101b0b02d10b105a0700840c2008031a0070000101c0e0080c440c0488801e03006001d0300c00400c11003004a412407100a01e4410b05a81603100c000715234 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 707155638 1250 707154388 707154443
    0xd08101e051201021b0c01020d1d04020a020f0a0f0308070c02030604030f090f150f0912020f011b030806030d1106060d020f0303030403050d0f0507020d031d1504 71
    0x80c803148900e80030411480d1629400300d00d60b4500c0005410b00e20440d01000354034540200207450341d0400c0800f80c40f40d5030304100c1004400a145020107181803000c1803400810304ca8000c15001c2c0b500020182165402082600d040c03241340780071600f8050240c140f00c454420b03000350407000201c400c0042245244252179000c511030700100030b8111510703260f80c00c2d251502800060300038072401c03030302c00120340010801c40001450700242c80000002041d0006000c480c41700c4041c002d01805c0f102c00c0c4440d00c0c003408e03c0d110155040e10560401d98407140141d42c40c500c402d9128030391000d522034500405500c00b0206003d80d0341070701110114108032000380c601d920344c4800c207031036944500300007405440d144140108807400688110b01071014a00480e0440d40111001c3e8040b403c000b50100c041c102c0343c0710300400e49104070b00410543c1410381000f0345a50b02c1704004410551a085814640340d5051000c042e907207503980c00c407420170105c42003030b0298034000c54003a00d03004000314514002484035180ba0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 707156888 1250 707155638 707155679
    0x10e01140a11090a0b0d051e0711120a0c110a0f21080c03090f0114160f020402070b0f130f02060a0e1207091404170c0106090f1a040c2a02030d0810 65
    0x8d0075559641b600c2220014442c1030b901125218032002c070547d48520000500e0180116070f110480c3c2642400c00c81403c00124942d54000d028010042012001018845c01179414500c018120740014a0071803101841800024003800c000080c1c10a0301d00b000801444010015500e195200108100646050b000030102c6407d40108101c0d03004102c60003ca400c400620412005480814a8000c1012030b000350200700c0c1e070420714906100d00402d460320301c0d0b544200700912840300741c00035a455260714401e840b0000d00803480400c003184c0480c007400b0403042d6170102a042002c001520f03907059075100c41c544524a1003500d0304281b100007008203d00346120310303044a01415000c1048a40180b25404804a5282556200030225403081c5030f024610384140b0404000c100ca40003240690510b252042e80240308a1a0809103144545c20201151005504e4010510302070b4514403e80c05176007004c2d5000350705029020910130002d130009a20380c02540f031001c000c40ca0b55262081c1840f00b81e05070010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 707158138 1250 707156888 707156941
    0xa1211010e15070f0b0a0507020f030a020a15020d1506180f060c1a040308100503060403121a13052d060906040603050d0c05010e01140a11090a0b0d05 66
    0x20360b00114000c90060400502c02c0509006108254071400c810f00c0068840006094079074081c01002641044030003042642000910700c0c0044a01c0080c0d81da402140004010300c051071030074003002c40c141d4140c8030003142088041c000c13155078580e00d030b03140c020314015800850341c103581c40800c0585c0a0486403d49a400090f01d1103581440400d843d540055101180c8250022103849004020030300c5541c01a4420b40b500f1950707041c41200d0420b0f10f849138000900981c0b00404000201750300140d142042c069250b00020141c11b0a1041c01e2407072030b84194160403040b44080d24001d082d00c0c0d80708030710400790f44043ca515000203885600d0100d000540500b00c1404920100f5403c0c45c0840200c1d400c1007004000107000760340e95a0700b5040450840452004c00c025114017803d0000c2809034a01710303440f1000030000c150703009850481c9039801034102403080359510b050b0900701001c4000c0b1801c3c10001440030090a0b078403107019105a00c440003051410741488046290b0034000307000d40c10305c100303406030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 707159388 1250 707158138 707158159
    0x2030403110409140a02030d0c110907090902072117190609060b0d05060924130203011203031802100c051002031509011a030412020304050a1211010e 66
    0x112203041520795006540d00c565100c0101d00041e40741c007204204220140c0280481d40c42a004242c1001544c02c0f11a06021414002800180020314202c1c0c44200c1111721074000c4c1c44d848011145160f998000c11050b620008609040c031200c54250030410040410000c0244d9007a081210700f1681c2988520314601d14402240480312100054a94410202c0c000500699104508429540707960700c00d001c861400076410b881d41e045406080d41c0170200340c581c5c181c1414025003840480410303664252030a80303c0721004403190385003280c0c9101c0c45185541507450756111405c00707c2144c0c0030710040303001c01c1c6051074111588002d01e0072030b070500740c0040c040b509a01080c0720a0f14203409a80003207400d8012540b0a41d040303425071010b5030007584641da070700c10700400b0181800602d65040c2c20080325121081da8949a041c5a042242c0d40540d102e108800c4140c41d4800a903c1c41c0126005036600000081010502240802d0741004160003800744c019050843c2d0300560303403100b90101f801c1e0401400607 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 707160638 1250 707159388 707159393
    0x1c0215010803040807230a0603020306190e06040e0a141e2e02070b012c0105030309150403050109030c0b0c160624030b010f06050c0d120b18070f0f02030403 69
    0x10650007501b00e0300c02c4a080e40320f40c800039480041035000140071030b03804030034080c06080c0810f07580c0c644801402e1850b420b03410060745840c8400020172880c46141c651001042c2a141400038604155105140c851b9102202100c6a2528075501c0080c1c0d80b03510403602542c0100c000a45418a403882a9050038409400201c0c01d00412036055035801d041c1d002c01103c0c1c00940d11044103402001044c0e4451090302d103a0048841a007820704139400b00d111507100520081e503021040b142d26040494007a010326010b02c009000c24081d9a1000e031a40d480c080601003895000f12074415400c1c0f00b8002c0d2005a5640c07480a1201d01a050350742801d00311100b140c9000410301d601c0107402c0a056080d40c100c0e101400d60368085800746400072101040c0000040004a010545042c042c003154106a07007002d0045910715034404c2c950816204114044034902c9040884d82e01061404001400d20b2440c54426001900340c0074064800e440090081451010007502c2180c2d4800f0070001503014510342482c64 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 707161888 1250 707160638 707160659
    0x15070c0206070209240f06040b160b090a0203060a1a0d0203010f0216020f06072f0a030818030c0102100f0b06161b05060403080703021c0215010803040807 68
    0x101800c036008007040100ca00503980302c0407407602c2244001c0e00d4140e151048a0426900f002101c20746010309088081e020702e95170b415054409844080102d40e031200e03c2c003038950030f605012050103400ba16084082c41031004002c01d13040c210500980440f03507140c0300c14614100701ca00c0f44c3d181d2030440d444d403040521145401c000146001d40001d00103c1c080c507013171444030100d03407103101c80001d203c07104c80062045041002110310b443d48120317102410550780c2c0d1205603845000483c85080360700604a8142c0c15500100c010302c0b4140d000e02144e58040e100c0c6410032140e0311446002020300902440d02c90a8580080c054a07101c1c0c042c0e01030112101013101003c05004641c1d0f24480240e2030b228004d242d41c903480058100c100c0d005051900e0111107042a45044000c41c5d8001120b14400703209002e10f03213604080324203e99000c41c42540d41c0100d41030403800d0044100c0c603040c41d41e04500704c5828081d80000d9502d24403c03410820000381c0d0f41c2e8400c040e0349228a1003680801d800c0160100550801c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 707163138 1250 707161888 707161907
    0x120402010309060e15010b0c0601050d0c0308040e0a0b03010603050c040c050d092a0b0313030210060b2101032a15030c0801050405150f130f0902040c021507 69
    0x1030501080701512541c0381016240041c0c1000c64030762005c6140c86564030418030341401040b1a20072a07240580c1c0544864403080b0502445004d6100342c2200c02c200540c4442d07400003541c014283da41c40365103440c0032082030813007039920005450420403100580d113018400c02d8201c0e0f070b020000300441582c003030074000500860307804002408010710000300054454000d52140c40e210310381482d41e066682d0824503d40c03480d10440002210681814080414284100e80c0c000710801108111119645812450036244018036042d560411304001400c2040340060308104080003003030121030a1a01003044410000d20001d08a040c0004107841d89110481084008542d001c03c0940d84940740c0d2641030000c1c00c803201c40e00010796110a9541444d078050089405018200c8050080d400e0115aa40108136070400341c605c10850003446507910358902a10620007103a414040c40038040302e0060100802400034241e004504145c03200c0301183c4045a07401c1c40310384402414030036850702501140d90707284 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 707164388 1250 707163138 707163143
    0xb0414061c06061409090708060112230c1f1d060f1c0f1a01031d0706020f0f06060112050405031204060f1a101206121202070e0c1204 59
    0x161006100040b5100c0d00582c8040c1550b84450202900f0840901a13140e00003400049603400a950030300206802048080c112011800070010600483c00e003001804600840700c402410344804203041c02c800414043c143c40000c0700c035204079140c448010350f215990f024440e40040c2030300080c2143c00320001e030205020703207001d0f20f00c1c0e05000071201a4007003a440f030062554403030804d10b489d2b480e14405024044501b400030806014a41e81840d03200f542100075981c1d58149034683c82c1c10f42e000403c0b46551071489105004842946a5442004e0b45940407850000c006024488201500e0a00042c01034081d0030b044c1e4034070030000850f1a04000424028004031400c0c0002c2005108146140420601917406074600148441003804031204841400c842d01c600341542c4424810342e540c9404074144000414100343c00c0c801c90080d811070081406400c81d0705468011041030007448801801c1c0ca41d82d1081d902100e002e1616100c60480c0002d00f2101ca442c8080104000c4460441959100f5001032 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 707165638 1250 707164388 707164429
    0x1b01080903070212031308010b0a03030e01030f0c0e0a0801050601090b0c0a0b0123041a1c0503030f010e07020a0203120c0102120a0c02010c050c07260102030c0a030b041406 76
    0xc0c003070781c002030445141010481c840d6002007002d213901c1b00b019840c02d00600e1108000c1200d050040040761281281c0c1c40040c05004d01c034840600264080d420803144800e50140401181c01144006004091014902400364118081c046002201403246c18081c04058445d603e860b03140c429500d40303592000b68540e0003400307600c0c19003000501903980c0c107019050000ca4070142d4100b41ca101803900f401d61202d5071080d4148000d049100d44520100103c5d002c09480741040104e91021041183c1c00940008165200000401045031103001246068610704080c4140700d4442c0c990880c0c0c0c1e4807201c90017950580015a40841c0140a03800402030010000009410030300c5003824000400300c100c1d0900742960b01c40d0161010254288500260144107081003801c09074282400d550380c0362039014100c3d800041c10382049030094580590407078114854000d540e40e2a160300c5020854110748a54000b180c18040300c1281032800303004612008452000d8001e45580700c908000300350b030100c002400c405 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 707166888 1250 707165638 707165647
    0x81b030619081c02060411090901140f04120206090304151e0c0201390501060e040809030715120c030e030408010605091005100e0f1305100501021b01080903 69
    0x74540310801900824103400a001c1c0c0c082411610050f900300c82d58842e0841d00b002d030811000542000348805660001e681c06995940c60896141c014501d0600001928450608021405040080c1c0b86e105902c102030300301440d004654103034dc0d640c905442c281c41681050105000c006400640d032071031074405141501301070560307141c02d8046052001c01c1100240984041106550708000140a21080400c030310303000080c07144a0b90521700c44000f00610a00b440d000c41c01c2803080c250401d40190015002c0d04c002400c040c50b000f001a4441c44940c0d001c0c0c000e040740014105100034400c4081784441d04c3c2c9003a031403071401c1242c4c01425829041c0041c19582ea691034094182080900060306140000041c0c403401c0408104401360300034088241c1c0480320f40d091200b0340725210801458591401c040742903210040000e4600d001c1c6213000d035080f181c91901c1400a000039040a401810500700459466413108012600c61100700014401401a00170002c100d5125094072a070109441c01540d080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 707168138 1250 707166888 707166919
    0xf100c030f020c100225120314070614010305060601020109123e120403030c0b15040f05010302120c011e1b06060e01120f0822030c15081b0306 63
    0x4d0b4a00d4030040c00583c025241e00740030341c072070034100301072072045102a5207954500140b1a03804071411900500700100401d8203251a5649802d40b10034a83c407100c1130044000056003414451000d00c0b0986151240c0404505294018410380c1ba800ea0402c1300440420b1807005e0554202c2808000c818512007943d4440e8042c00d00e1083d039844044003c00d4221125803001c40d454606000c090410041c010104800c00c002a0050010380c2e09070361100540311255038402e084101111800003203604030381448803d0034148065481079050740d200b03c0b21110790300091000c10350364400c180107190210b221184290400c440d6043c3d5501024924039040c500081c060000e4421464800011905541c0f20b10301030001004003241c0b58098401d004500400d4100d980350348804541001000c0d0211000042c041405108207054110300001e50a0070500283d5920b01106103034858441d48040c41708000c004e00c40944900020b03401001c0e000d8900d003284c51903d25100c03c66202500180d0300c0034505902c0350f00d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 707169388 1250 707168138 707168149
    0x501050a030b220e1b030705010309050f0303161b02090a0b060d0908040306050c0c070612020f1215150711011e18050a0b180105091e0f100c030f020c 66
    0x400d20f29140007242403549503050380c0c070f410516101c200c03c107401c5101030916a28001703859021242c00340380c0441c015046041040c20816a81c030b6145560000204110b001c1d9907100c0b00045409075565994080c031a031414103106040416802540070039010080340c8095070541025000c04401400c1500e020101041c1c00211b41c81c10741d00700d8030482c010400f001030115520032180e0100729090482e00c2c1c01100c4004c0d54550102d4002ea4040c48004000714809100a50603901d4000c0009049030b540c84039401d00f5080b4100c02c607155200d002c40082c59407600d003002440052a20150000e46040800710f583d140c21003108a03142504001c101d0100c00401c88050100a80004458407840341a910002d0308402c04061030b00a0360050b900780f00100054040001207404c021098602c0d80c05001c000700040300ca034403d90b080103030b01c90000c0070400000943c2e0b82e03154910b008111003e004a1000780180021801d070f01c1d400328089080d41c20302c1000300c0d0082c802001294a0352050300d82200c10700e00040c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 707170638 1250 707169388 707169439
    0x15061b06190b031b03010f0f2007080703031802180916080a142103190b090f060a0506040611100e0d180803181905100509061b160f0501050a030b 64
    0x31070705500c40701100c009c5d0014070941c0080381d400ca1203042c80d0140c240c4840016208040d002002c06580c1c500007681542803030300c0196055130040004452611160b640c3c901454113450306045030051928502500d00111701500460b58000040c080c60150ba48400000c995855100c02e1a40502d039100241c54000c51401c509003507024542a86909128255901400c076110b03407140801d242a0310a00d060f560441c2c7d135584801d04c19810b85050765260041041a1f07411b500043d00181c1c04540440c0580c1c106502d0551000c203481141d40383e020302558201607849000403410383d9000030610b44051030ac140c11918140c144d0712101c42100b80d0340c1600f9459640060900441c00c4100002140340d0700e0314400c03803001d41e107100d01003003c481d040100281c2d040c0d01c4002c060050090014440041c0e807900410748207014041c2555170341301e4880500e0f068560b42c2c0c00f844960700b44490311001c40c000c2c0000045009440040e9240c0e402c042d40004d09400400c1d124080303592003800000302000b00720b10110101d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 707171888 1250 707170638 707170661
    0x3040e0412020d020303060a05040203070210050405010c030b0306011a030622050109060b180609010e09040b0403020d090b09060d09060e0a0c0510050315061b06190b031b03010f 78
    0x884506141c03420003410040034156103011900304106219250f9a108200020f03980c1c1205e00580e651540c050907071610040b00f481d0000c0505003810007042c0081035000c451035913202d40b400d00c0350445d44010552180000d000f40c0300401d01a602131490000c1e0107020303540c403480203070540042d91954519600c10341c40034001601400d417a480140401c10740c40c0201d10041844501443c2080e4140150a402000c5402032074080c003404140c00d907550f0b21480b110581508042d0000701a404c213800c062503002021a0243c000d44510310340381181e18441c450210481d04401846801e1007903032002c12941c1d5001c000c40d03006140e00da56400010918074400c001c16680c1000c01807610340784614101070112415800544a0700d402d10004003400d40100480750b00c024500180b0050300041d00008015004180d184520a20280c2c0d401b0320318038000800e1409141c2061368a00c5102d000301a01041e54680c000c003d0705504803007912030051b280a00e100b00c01e0301001b00040350030854100d80c54204c41e040e80c4007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 707173138 1250 707171888 707171903
    0x1512010906060e0123041508030d180b3601020d0b0a120f060e1204231c03090e070f110a0c23060417010b040b030d1103040e04 56
    0x10010864544144002002495580041c84d89820410045c5c03001d030603000c1e5041e60b07011440800e50398855008200d2116507481c0c5d08402c40d1030f003070b0407540c03908059607242c10315141605000190828403820400242e1007901284c19a642d40100d5002010850324070720584544010a00c14950070301c0c100100c0130111000507107a21000140d072003a102e0001001b409003009000500450211502001c54590050a2581c1001d003d2500e00010880202100340c1070040340b800511a00d0136400900031603048904410304442c0c2c5030001d6848990580c90382c0d0307001d03a0000f14004007800708120b249002c1d001e400c0401c0724940e61605045400e608450703142c002050b444100700c4090700000f11555264032500208a1802c0710784e83d03c4010442c1d80200805030214501c2e5aa45501304007050400c11009442141c0302c0707a40d8515400110680c4540788071075401d1002071200350415102e100724414004000b4110558840020380e400603415402d5135140c0000c00c804106030742d0724080350740180c1c0705020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 707174388 1250 707173138 707173151
    0x6030414031606020c1504050d140d060f051014070f110907030606020709060311010c051e10060b0c060a050a020d09081b0312061c060c0903020f031f0203151201 71
    0x311741d0030281910710000450724448140301c003103000041d00d041d021299080c0100e50f0796900004000c070b40900c402e0a02c0460404401040750030507500400c0c2129010b50f5680005014071506549500008a0002d1034102c240005004035034182010200d481c080c1100b4400c80c4050404154240003c1750340c0408a91290b2040044981c1082540300500340b07440f00300308084c1150f850400018840c40704504025510540c6418400107000062450880c1403501c1d01c4002607030141500c590113250f20410fa03615103180060200c06420884200d0480d15010f445166074105803000102800b41608421030390901041f85011480d102d000c02841c002c0c00c21a44900b070200d4450108401d0000310b080ba41c109121410880d80f402c1e00c02a00491708407103e8061400c00e0340d514100080c05d02e0060f200904101c01c0032009074005a4800030f59000b591105121203084040c5039841c01104100e03c5035000d000c00c5205041056400303036402604031403450510161120001d0140e180315090400540d65402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 707175638 1250 707174388 707174407
    0x206130b0d090b070e1c05071203030b0f0a1401080a0b060705010207050c0609150c010908280810031b080703150b011704151401090c110a020603041403160602 70
    0x101c9556002c030f4a45800d002c00300e44d0b200446c1129a000782c603c032808000c1c1403081c003003242c07d004440242c10402072003009000d442c10010094000401814002c265291005801d400e100c1090340c166200808044c080505401c0119200b01000b015024040d60751501c203002c0303a440000506140d80141d0016885d00c40c207042c03080c02c03c0801d038015407041c1c0c000c10007214151504030f41c3c120700507155040c882d15811007101080c0901340e003007070081100400085410f0100c1c0d02e4140d00030b10700e01c0500b0003500039410b42401d072108181502c0384031091041020800005201ca500c070100c1e082e041c4200c03100e40c1c1d5a407581620307141701508100e40c54282522404650070781441242410f070401d00c0e01c0303c1e0130000007104d500308410141001c1d06107240e040e022011404030360030400c05040d1035011f005496944050f10001032481e515088000340c50f55000c0d20f0a254000340304920990003c01070352440d00d171035488840d081c0c12080702000500080c0a40140340b401180d14482144c0516000340e921421035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 707176888 1250 707175638 707175653
    0x2a0c06120b0409170307020a08041215141305071a07150501060e0d030309120f11120a051315030207120503091b0307050604080a061b020a0206130b0d09 67
    0x4400d800760b49029030350f1011130202d12448040c050001002e50307803034580403002c0341000200c0d017010704078010019001901846200740c2c140041c2c011510a2107141e10101a0307c2a00c000c001110ba80359540300c040391182a65000c0005d4a510500854603070716038854004074080c0d42c54940c06040d801c0401d0000c01d0000710380844a124810941c10003e560504401a0040d00640805802510022004820540254040440c040d045090403c1c04200300a00070001c0d081c00c0d45640000348100f0705481144130000300d041d503441300c001c3c000d424041601e000702c4848d084038841291001904500280750101d11072161a103980950b00580c2e40d8000742000c01308150070715901010840d040040201d808000b06004051413203017411000d610a040000a151000e50740080341d101c0000a03000903e41400207050511610130342c820702034041a07012490403644140450030260b0400c418a10052134a50003c0c1a040d420088a0b0740003a240c2d40d41c5640764201c10b801041d49550340e9024001c1c823150 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 707178138 1250 707176888 707176901
    0xe0a020307030e0a0503030114010908060a061e03020a0b030705071401020304020f0f0603070818070608060405070806010503070f170a09030e06130e04060e01020a090f050607032a0c0612 82
    0x8004100643c13255440d01d42e40d110520410001907040c0d0544032282c2e20540240c402410040129826414001605402486140700e0050440c00034030a400c110281c21540608032900100516081c41c43e0040b500441c0d80024010000c0003030401422001039025101216241590000140c89241602c14010f003221421074403131045030005000c1c0c00b241c0d1341e80c1c21a54801c8891400c01c0c0c40b603c92070ba400d203a400300300d0111200c3d4082c04e40c01081007503101d50718511410f8100c07424002900c8002c803d548032141a1085400a20100000740d03031540240d82c0f004d80506d286c80c0072020040540c802c1000502c05a4101c01d1aa8403030700d82c581031560000010002c940c04482c00c1c0e24180088820003050b500705e100300f401740d00c90340001070309203c8107900c40d2204070756500081d0b5a4170030070300008100f240f56009a58200700c4492001c0f074503003420816684800c4d03040d100c060b065108800c22403e000b80c0081201e07150410b00242030300080c00c0305070703034401801213464225050800d041854140d641 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 707179388 1250 707178138 707178161
    0xf21040302250605070501060b270a030503090d05150408030604050f150f010302070533160c02040b030a060204090e030f07080903030706090b060112090201020c040b0a0e0a02030703 80
    0x500e008800000740c0b40c00c060340c226103407030800300d560303207400d01e0282d001d0071603680040c00030344000c10007110b10b500ea0391031211041c3c0b148884503a0345c042c01e801c01100f241d06010292a40d8000d2015903994280509010302040c05901207440303a1f0300d007243e40c048020701102c1c119441000402440707002c0c1028003809800501c810700801d410300e41903400502e42d540804840b80301d282c1001004805901941c111228250040c0c180c5409520000500d901c48000031180890501220000110b44040306d80c0d007070090150110400b40d104550804403401c51100b0002d83e0b02c165510740d040320a507810030141c1c0d8013038410726026841d54a00b040c0103045900054100403590000c010a00303021700ca410448040b154041049904c43c102d0340302007882c1d4091090001e01c600c1c0761540740014016107007802e92003140c00340d07101c4003400c075400294010b40742d001300001c3c050790000c182c030322444c541034005422480d0041e100d8005a40d4468140340081429100741e280e1fa0b03030000900004507410302541c0050310 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 707180638 1250 707179388 707179423
    0x13060f0203070b060114070503031302010e01021b310c0320070212011b170c18101103120f180d030f021c14150d06020f21040302 57
    0xb0300310b484241c81c08000404042c100b0625006c01624010040260341c102030300001101e0b103a1500442c070144402c540d03d030583c0426484030b540ca011f50700c0083c081c40c00600001c9030381071110200d03061101c51240080c064002d4050780d136007011200b0f485408071001568003080810741d0071224001508446811202c62030aa0310f51000c1b1000400308000c550038560f040d900052a2040c81d50b8460061641c00c00882c20310705008400c0c020140c1c44400a04040391202144040740c5502c03100305d80a02c01c208010801403100c00f0098040d00e00012034100c0c2a61900345244d00e08003189855055901401c0b0010b03c0e840c00009001c81c2d0002d00c98050ba0152802c00e01c03240d0842d9a00f001903403154521000410151113402da030321003010350b4060342c009400c004000400c40401841e090040d01917072002031101546040044d41c01d032500c0d220041403540c06031641011360416203a00000c0c1d0b02c118400140740d50200300342d4500d407039180503440c94400044c01249050900f46002810519101404695076 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 707181888 1250 707180638 707180647
    0x9060b0405180304210209090303010f0b041401211d191a04060612030c11010c15020706110c010209090114030601050111101419110304060203100b13060f0203 70
    0x105000044034103a40b0000981040d040462008017482c10075650020f4001210300b00b40905507000201a43c143c46603222822040c5440c0c50f02c1d45580d0245106041f0790808145411b04554020240c2050ba0404e034440c10b0004802c0c810f200c010f4440a00c080c1c982032031002d24503041240140190202d45180401100500f602625040840c1180c40c00040b018503901d0f0101e420840c003688150000e040060005884500c5401c0c0170b040b68050308002e943d0b20f040301c0d0340b410301588645c1030013103115442101d00303045400d00b540710002508031800072500c0c01da480748511811300c000000752424000c0e5100240e9900301c0799003071240300d08042c1d01001550a030310007025001e035004200103054038028070b440041c2d00001003c1510b4000080760100410345040303a03c03441003007240f0000e0f116501c0945001111296201400200c414112206660070f00c2880801c000500301d800644d000005441d10601003900c82134200c100c0d50010403501c80302002e02c0c000301700c81070700800c00c4002c00c0300500145051 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 707183138 1250 707181888 707181931
    0x1030605060f12130f0b041415010308030901020c030d020c070e040f0b1b0313050706170a05090f0f070306060e0c0307030c02030f0a0e090c0307020d03020304021309060b0405 77
    0x10301a000083c1c03556010040050700348000d125000307655581000e40615500154202140c810109070380035201000c0400c0000c901c41400510707000c4070251005001c40316032850300c600445820142a5030240c0d5002c1000350681402000601203041d070324580160b80300041c101451800c07400d688110890001c020410002c101c009440d030808981001c80800169100c081d402005402d1501403a0702d480084144030020400300600400c8030710400071551400d0319144141e4840709920600351034000b0000004107802101d801868200001508a83c28207146d10b01140c2040c450390b820004641c01640b082082c003c45d03004010041050f150b2a10141c00c040c00500828800188007001b03054075103c035402200d100300201c0e0a4504151038850f121260224000d125500c007801540c4140c607080301044c110a41001124040e910320740080a0528240109a002c0d4000600a0341d0100d0204140c800d0b2815500402040e903115950009400f0703607500c100803c581001d8030b0703025440c00c401e0041d0003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 707184388 1250 707183138 707183167
    0x150806180603060a0b0a150806190b0a1214042006070f02010503100e160e09060d1b030b01060908160501050301140607080d0605010f02190f150510050103060506 71
    0x801190980005ca0901c248501040000d48a5888041c039460141c0b80131000d541d200c00309500822040b223018007a2000a21b41c46140019030003058035180b000c0083c05103545c02449104003603a100440030030240d1500c0b03c0a0141c042c1100d0030380310b40d150303641c0b55060155060b481844c007104c00c4824500f00780840d12003518070402030100a050150000100b2459240f509106004082c40d868016151130300c1010103425180c1c26803020081342040100400c5840c103c420a4032481c80640b00450307464194440c2158000907000942c00034a22040100114402d024154007130304403a1204500145881c0c0c0346883c00d2040d04501d0600a1011000d1001d41c0c0e101045034111607040030340c2d840c0e200ca044d0000e2194481c4160040c01c0000019480c1410700842c1c1198084030801d0b224401a0160310718141d07160464601041c6c0b45111100c0c0c0b038000214001c500e07900c40c81c000c4c0c102a02c0c14015090207421541c01b40c40c4162401a9407c0411582da4140a480060b1806954940c14444000403025 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 707185638 1250 707184388 707184391
    0x901090c05100509040e0d020d08040b06060313080a08100611070306020c1e0a020a1e03030f0c0501020a090e16170c220f0f2102030715080618060306 66
    0x502c6240d0510031800c806204006a07051414001c2007003000040703088400e5aa6001090314134054010a100c50344428001d41c080c522486e00207142c4a610780c0d0306030410210b980018821845a050301440c030300410445070246c0310308001070f101e1054909155840700e0788040f05500200402004480c41584004042801c0c400c482d80141d000d80c8548030081d1060404502900e131902c0024601115008000000784516404c3d0007554081c2e01c4a0312461400407000c0d01e681c46000344da800000420000e44514800a030300000d915011440746040c4d42c130103080e40d04c124070480c0020461101400300d054000c1915401c46c0c4581074000841c41c480c58050410120104d55240c01c41d40b04002503508440310048610004003d201021a40c601d0842c00041d511103016002400c0d04a1a000c070380000545120800da502071b8001c40c0000ea031246034030f4214509010103c3e0140507012b400140d070b101c0421181d9459000d912110120f2804106202540f038600c41098807520354034007070050503140416001d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 707186888 1250 707185638 707185649
    0x4090518030d05060f030a0602120117070303080a06030b15030706020102030919080c0601060504090b1504120213020a02010b0108062b03210c11070303051804060504020708120901090c 81
    0x41419518200040c0031117441c880555010b00424002c802000000e5004020021441c019001540d0703c03281c1d2284240070708055903105510500c810b00119000c2c61513a135000d00d41c03080c0421581c1d165603e07040302030001d0320880810703030f41142c1d0182d16140503c401c0014200070b1000b14154508800f4032030340d03000d10360203000901908503041c0c414170442c1070407125270f09150070032110203580d10396004143c0d503c640f00307110100386000c1e000c034098502403842035402c00c014502c2c039007003600709404000e0490340c104089038080040c0d101c2c0716440c250750020703001250306600001100c00c142000540041002002c403441199070820024001c1c0c90b01482081c070305100070304d00c603502e10a4a07054412100107110f000090280010380401c2090940110071040da196940c506c00550341542c440c0d4900e010b0000902180003800a00c0406a0410981d0b003059001000031a04607581c0d000324003284d1040c0c10903140c154000a0034807414824100060f040000f0740000c200031980390301c51004800320360251 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 707188138 1250 707186888 707186891
    0x1b0305041707140307140f0c03100c0c020316061b020603180a0503030405160b070b06010509130504060b0f03191e1e03030f0c0903060f020403120504090518030d 71
    0x10741051102c3e156098031076403103910450742c1d100c00c503041c8042000100400d41e06644107642d014058403002180d01d070a40c40010740103180c3c0e195140d034130074003a0403551003040401c4030070207004001d0382e004c00c40480840030032501500da6900b0140010000004406803010002c4034624440c0161103040407240d00c2100d02c005648522088401c0c1030800d46a03080c0902184008428402405000b0038412104540042c9500040743c2d225541010303402201300140c40c2d00755001c0000d0055001e4401400d4080009103041d20481039172401c1c0049510940e0196002a0b41d0010048a0708101c0e0845408181c11002054a500f0002416a0580140304010020a02030f8650f01c4085000c41d20008529440404160003045403550b00340c90946d500c400790300003401c101b425a820b90592283c44101d40ca80e0baa0900c40fa8216100e90340504a52060a400146d003000b0020125060310209041c26101d6600c45582e189080455800c3e60030160040e80d8442e030714a40d542905000108446221110000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 707189388 1250 707188138 707188147
    0x1506070f061104030803150409050d210c030b0909160303030b0f180f060a08210c060f090d0201110301030209180304120507150c020904241b03050417 66
    0x8128000d08282c103400d200310580071802204115000e009941300f00c980940604000b03683c082004107a0302e410802074400e4218000e0a00f00f540704049191041403003251404814219089900031141746000040000741d4600780b01206180551070207400440350170041c10302003c1858407503103103405880001d0034145c2c4c400d050076868482c082c0140f40d401c0000d01c001a10101d0f9401244951f804a500b510355201d00c2000030344a2038151042026542e018006125209422009203e0b004d501180c51000c0442404070074000c0380104101e030320803c9040003600c510305040f16030a2400301c0b080e140740c0c10369040000e00401c14641000396411660112260f03070150300d40e4801c10001c5e01c084540f007035150000090114410500c1510a02124841c0c01129266540d502c90f1011018011040704000364000d000a805407401300007071030b0014080e62789201d40d60400780110030995406800c00e00d0765612a100d010500c608021240140c65007401c00b406145401d80d940e00304080b2094203482c8450f070108 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 707190638 1250 707189388 707189393
    0x5120f10060801114b0a02010c140a1b02060d2019030f0b0a151106061305101509031a06010f050c010e060a05100f0e13030e09070c05061506070f 64
    0x100c055503c005c5991048100e0340c10300004a80c01d52082c0001c0002d0740c02c2140d403444a030710441844440b400e520403c6414140f03855405c66405114540009860800303a020034050b03502e1100602c09400e21000018001030910203002910440400209801105011080342007981c0d08018140c500749250015600c070b140090b08000b03210f0824030315041800a040800c5020502a0302c045008203030311b40d94621448110340642e07802089071015004114149025401c0c08560007080c0c000d603a0b60301d030220711a110650303050b4003c10344242d940040e070342180400c24081d0005043d20340c6c8511810700d800e9032501c02c0020300b1306440c030300c3c0c1041040000179800120131001c0d4041d0041042450a40d0340350b04020301ca0710054402500c1d9a140d080498000113890081045c0000403240702080000c62691204035a23a130300e08403408282c040c048e11508256084d80c42c1e0091a102c2c00840e280c2d01c6540400f41000da2404d10000c1034130300c09100510324449555101019107400030740c00070340d0b28452400d51 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 707191888 1250 707190638 707190727
    0x151003030311120403080a0f02070f020904060b150a031104030b06090a110406180806060109061b1410050709120602031e100306050606040b030105120f1006080111 72
    0x50f4480744040b850350280000c15a0255034940601c3e01103c00307100010311780b45410100e00c1060801041440003030300800060510b4101650700600400e40016882c3d100000700e2440303a880410f01441c0100020134118054040c0728810480300b600400d10304050440d50380c02507086010340214818034500e400103210702000d40003e56184010908942c0b1156140000340c1424290029880f050000d82030203c0c02440008845110314416507135030380118a04002a5420450314156203070001001c0d04440c0443d0005010180038498540149400e03043c0000f808100d9030003170035040c20001c1c1000704200400e0400100d00e8601d401c8200140e9a072261540d181c0340c000000d0003200c01c04900d00c100700b1809080003110003201d02481c07060040f50b442a04000851045000c0d0001c90301c0c0610052142d8103008011220303842c0b68900b210040c480b440b09092805e000001c5e40310352252106000e0180c070100380501030304030082415190a00b60319001c0c4d0340c090040008802007102c2c048104580d120b402 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 707193138 1250 707191888 707191897
    0x20d030e0d0c0807050a30030c0203070303081906030309061103090a030b0105151c0b040b0406090b1306080a141903020303071b0f1203110c0708151003030311 70
    0xc242c034440c025942d0022107850764924881c00340314400002001070301e02810502c5c0b501e00e0b50405817560b1501d0311641c441203c031141c12400d030200003210f01001c005031010020300014601a0300c44015074500344048a11880400c1c00d20b800b046d00304181080003917041181c003c141c40080c00c20030300c8580920340381c5186000b00790348a503000800300380000034001d0040340b0506070b0344243e8081014424000200741503100788000940c0c80488040c4c0c0500304082c590040c030301160010004240c1c88040c030005003d4804e203401994480f81d0355405d56030343e4a4064641009040444814011546404240d940b91191044080c0c030b10301020800c030000c404140003137281d260030040104040751460600940c0ea030800c64404003c220900a8003042c0c958410300c484400f54460a581d01e11421a07403988c200006440e90141859115800e00c061000700002400820510400514000d4a80707003003613160481040707a600400207080c041c48404011202c1c41c1c0d017525054100031031517801082140740607114 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 707194244 1106 707193138 707193143
    0xc0503030a14061207260d021e010e030304081b061f0f0b0a03090c050a121707020a09181203020702040501060203030c1b0f0a031713020d030e0d 64
    0x4038910030035216036041610341d1100340b50751348061a110307010070740f2400b58100c2d2400c10040103a1527010104111400000e100403050402103540324400608090504040058084540d100311905410209114000c454540c41c2082050fa5800000b24072700070300d524031040018251885031100e1040c0c81c52032041c6490b00340001c0b415030081c410554100c80d4a05c2c0ac64001843e030b603810441800078100d1800000d4290a00e28100301a0200e004802c0e6259030144000ca0142c3ca4604c0004151011068001520641d180466145001c1c7d07410007001c3d2400081001c00095143d000307003044600c2960140304503600c0d4035050303840c0e0001f1100040180802c0c0301010900482402c5185480b0305c581c103031103025a6038810f4a00f801c04402d01600820700d411030360610780510701c1c412944143c0c204031035140d02041d0f078002443c020940700302404100442040380c1581c2d643c081250265603 = true := by decide +kernel

theorem cover : BRFrame.Cov 707014388 707194244 := by
  have h0 := BRFrame.cov_init 707014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 707014388 ≤ n) (h2 : n < 707194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
