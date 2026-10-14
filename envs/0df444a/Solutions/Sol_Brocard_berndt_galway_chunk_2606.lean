-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2606
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:12:05.677091+00:00
-- url     : https://prove2.me/submissions/3f2b3582-bcf3-4297-95b0-31f37344c681

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 468525179 ≤ n < 468705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 468526429 1250 468525179 468525193
    0x17130b0408070c0603181b150201021824030a02070f0b070219031d040b0a03050105040318150f020114180c0901150c0309080307050601140d0b04030818 67
    0x1410701242d502c54101500c1450a4075404526070348a802403000c2c6100711100600b2070840c588880d10310003800e250000e00e00b641c8030300028a903050454a09004020340c3c000589602c2c81a245091090052241c28441c103c0301c0c0c260079107151120b4001d450001c8001c4007075140e5894083c1400203100d6a100a040d4a0b1502461400c001541c554548900b05641c2a0741070903d0546080010359050440100450002030050300080f500206100342264000c002250710a03039036020845401041c3c200342c50507512042003100741600040c01265200c0d900c00c41ea90118a4540e80000800001c0380403000c00648001141e040751003500182ca00c03903500019034446003401c0394210b808069007280214107020751392100c802847c02e0390105d4121401480c5640241103440400c840011704000105c041c03000c0c01c20042803034a02000589641e901c100300034070595051181c00100e51880c10350103031042c01c55007001c200064200c404c403034106505040a41807611000701d0710301c0c9110000c030600160b102d046 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 468527679 1250 468526429 468526433
    0x302160f290f04060b0d0b0406020315030607022a04021303060b010f050d0e1e0106360c05040b07050124030b04030c020a03060606020f010e0d17130b04 67
    0xa59418010742158200740348054102000003034090045400861032106280054080386040d0803040740600f00a09941400ba240d41d070f0145484025142035403401d40c00710400012070f03420210b8a0300a030048000b0b11482c6065400207585400c4014505845030064400303810051915480d40340c0c070b483c020015500c41c020b0b10344c3c649112290748000d96a0500344881e2841c00c0d401400740d92040107096071003924012034920100c2c0a080f400c0a40c21661284180c0301da415440c00d900145044084000401c8007807400a0405d10b004a006c1c41c0b5007038405035200c0b51428000c034005007074401e280f2200490300d40078105060b240c0e401a60300c818014100040c0504c200308065001803200001c11017444029016a004500c41001c1800002c04014820000c6000320740a0101524424801020b0540c565140c2d920318060307032855401400036078841120b520350b401003806114040c4024200800b2821150f10005154640c000243c8510455140110764001c0b0bc0d2244a4403581e00444007850904081c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 468528929 1250 468527679 468527693
    0x105060a03120516080a0e010305010f03060518030a0903050606010e01170912130e18070302011202250308060d1e0c09020c03030f13050a020108060607061b14190302160f 75
    0x244141c000092420010407c2d190700a10680381070355040500b11a0040c19547c60030020040600860180c20000c4c3e84a941545c0800003822044125502e85070340300d195182c8503140407405003a09060081c41c0b08207260990307100001c4544007081d4084000d264070741985079403c0045403200c0710480d0100040b4060440a440580001c840a80145503ca42e560080d04c1c015402040030403c3e080e0481c520400166100e00004220072003030381001850a46058811209100f1003030142c4035000305500c2210900da0412481c9a00203402c0c5d800620071005543e61314079084a0241501c5802c2e20407504c4400e0060f500c0840001c0d06940c0c42c119950b100380c051903070340c0f90000c940c21807007906400c0001d461a1140b040d036808031640800281550745080d4015103001000404050b04a0010320461010a803980180540244201c0c42d031608800f8441005241000c500803207109c0900410100352062441c4182c00e0752100c040c42d0050b1941071070114260403ca50140c041d200c011001c55500078031900c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 468530179 1250 468528929 468528937
    0x103050a021309150618050907030b1f0909020111060708160e04020c0709060b040303020d03020304080d1b320306040e0f0d031803050d15260f0105060a0312051608 72
    0x5000b4040746e4541c0c501c0b100c2501d200312180341260300a00010030004843c4000960007102955450104460080503810118030f182e20904034142c48800034410765030007040031800420188046c040ba4682404098110000030700784030b0228680b201a40704a0b441203914840c0c2e00002072040d56191303c0d8851030341d5100254060300000d949405070001d6540b01400071a03040b6076140c0c000d85854180800140c0c0290801002500c4812040000b400c50301910301c07840000303c83c4030725443c10544c401600100703075000e440010b504444000c0290076154031815035005880e141c0b603001540c0c90307079681c001c03d000d800081c01d6136405115940030304400706004a06801009095a010400c0481c1c200c0490312404520784060042042088941c150244541000340c0f6102200c1416200558039001d000b0302000c049065005074a19142111443d00c043c000c45040580c41c0009004509104000904014452000404031060a4203c0440700e0144c020364142204a00658406800c9030414402c9580 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 468531429 1250 468530179 468530189
    0x3010f020a08040b090c091b0d0608210f0706090f060e0601061e0e01080901060b04140f030a0206030105060310031b031406010e06011101060308041202180103050a0213091506 77
    0x1044c10b0000d2645500010b85ca00070381002001041103403260001d0101e00444001031100e111070070040d00501002600642d070003010300200600508140a9110b17102c059404221450300c20200900d50455808109030340206402200010310b18055107040c44090002030b800410036410001c00a607144004140c81e0304807041602d809858a01c40402c070281000c8102d207980201e0710107150040d0301e500c2503d070958840d803000000102c498442101c812690003a84c001484440b40281b102c034541840001ca021219003500100306205207540051940e01050003114003c03040400082d4100010810350402143c20003000040d86500e2031030506d0740340c01800142e07504c45031098014140600011403604848074a002080d2039141d840c0111281e2440005114a540d200c44c00400443d40e0b280c02040101803480c50141c1c4040b451040c0456442c484041c0c10140e01200010030108502240c00352019034112003100320464035000c140014090740303074064403e02c00b103400113191b0580c84c0c0c01581550 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 468532679 1250 468531429 468531443
    0x2a130911120a110412050307140303011406070506041214040906031a0f010620160503010c21050a18061e06181116060b01180e1503010f020a0804 64
    0x1980710580501035a03d50011068080710401040160112042c52100e0052150055174940140c5031141d880e40000b0010040c1203800c0000100f2105040712050120a0819a52682840700c1078494584802004001610400546035000c2e045803140101d449883da85550f0310f91160744039001280104124041206c07180307401340358020549990b0032a00e20401d444c1c442601c49a003040000c5508102486600c1c02108116074805800c50003840025542401020844001340c0350008040c203580310344041c0030a005c07180c2c2102408200800031100d481d1640b01c0c001c5091f44811143c04024034210641d00c419903007611720700302004610b400040c02d111186e00341c02c10504060b840700d800c550862041110200c61407104010400190b00f0440d09080069032050411180d0340287c203c0c099410800c589055803040f0414440d1b8004012100d0001900083e0f044503051483c0b81c0080e41d0003525040e0810114a03140d86a503409400490f0b00e0600f0100a54480078641c2000e490a113040e503045801d2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 468533929 1250 468532679 468532681
    0xb040801050405120408341d100f0e1e01060216050301060b1210080d08040302010c0f0e0120030a050d0b0405040317040c1d0a052a13091112 62
    0x401402d105440656000202920314a400c1960004000100a0800702d01c000c02880700c0b014180c7c00404400280f1512040c698800d0030750390602c1c0b030104000c01800003400000c106010b4085000403032401c1da0644450105184c035038005c1d40001007294032655141041d528000f0070615030108803d048010400030380412141c49004240c20f0390854051045403480601141c005259449070064010442d44403a5015585400206081001441502011420b2041444201a424490090a030311185400000c620465400514000c80c12050504004460301d00500d00d160140498406214030402c4990755000100050300796002000c0701c8500d28a40076039101e02d8207040c041d8a00c9280e050b52000c3d070011904a00c07542d017204c00342051341d0400d0f10280205a150039400c0180107094456031b4003c03640f603c02c107188191103006113070f01c185036594911440c070064102c50100c2401c1c0032850310783d1501940900200c0074000d9900c0b880810382499035407400642c500000300319640d260030310103c10f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 468535179 1250 468533929 468533953
    0x8061303020607031d060c0403170a142a0c012007051c060c033e030a1e0209010e0d030e0922110f0d05071e0b040801050405 55
    0x9050026100500540c00072000207910034820792001c0e4a011030740380500d5003404582c210a03d4007100f180c24010b6100001418001d02c891b214142e00906032240c0010f2030100011001400071442c19003181e14450081130310802c0440025680d44030b50004c11074901080c8025840ea40d545c07000581c9907020903034190389420302441c00d81400c4d0000ea040d00080034080e2404041c087c101d41d19100c124000000721640b54000b400030302a061050300c10b80d9001c156580d44428200303d08100c01001600080302940d455510781452240c11000d18070711002d107840c0d41d60104603102030000d2003142c0700c203800c1c001080444162240c0c05405248400c0e40e44210300312211081c8070458041ca070001e8081948400071003003c0c98280c040d50340c050000301d40800740900642443c40503070311034442203030088815140100682000c0390a21104801150501b00c56039503a143d071502c0741c3c481e00510418010703a00c24211240c0190311410018241c1c8003160382d40f940e84200050092405070790407a80e5024003072107001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 468536429 1250 468535179 468535201
    0xe010c090b0a020319020102192d020a03080402041b0216090209090c070204110403081207020c061602030115150923010c0f15020913020705071a090901030305040806 73
    0x40c04402c103400451400c240c0c0c01c0103a00340010101e5001c01c545d02000b03000c3c0a081405080c040d4103025449210584010f04d4024112000900106264644103144020500e900044010103240c040c2000c0c01c036500c446c004a4003401130403680303101c0a0f410040c241c004550001c3c1c80c003480020030040c4001c04e51507510308010f030311550a404d03a101a042d004656062107180003000750138070003400012703500509407911189411550056030131040115403414108110080d540d07002050f44090081000440c1c001000c60242c0740c100c00031440c40c00b40b0441191800d521030072513100d074010140d1760550349820341c46c0c030f41c881c40e003403000002c076500390028001c2c0d4034040340090146144010f04814415100448400701e07000002e4500d400000307403a9010803089411502400030b02000507a60f40544000c4c400202030790415004558030400109003c00d6022503100150340c0c0306541015000ca045607844c0183c0034080c0f4142c0d0128131580000b00700354002008008035070180007640d03115990354000300c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 468537679 1250 468536429 468536437
    0x1b020306040305030703090b07030501090c2c0a030f1119050607032106080c01030c210504020a170102310b0d020706021305010e0a24120e010c090b 65
    0x25016030054001c500040d015401555004040e842c00250140a9482d12203410000341d030700001095440c001072180f402c080c040c845203030f9241d00300b409900750f60070207800d5199014180380c111000071581c8141259120001c080040d40c000c80d078040d4030151803e046c0c0440311550704481c410404a03080c002d12101c075002d1013045410003480c5034200704290301d080d150031081c1241050300207021030104084000510500c40035281c00e01c0101552083c510000d02260300310216601070061a0403c480550040302c030580e04000b0503000403a69403614408160a1003081c1c0103c038a45a0300c03801c600c4210700541c060420f418801600d03036401c1d04001e210800090341042c1055030100b641f0700034490107400d03500030501e01c1a070340c3c00103240400c1a11010120b030801640d0390b0003c2c181c100108208d44e07000100f40b18120302101c20710b280300c1c41c080c5031100300f0169020b54032903010558200c50569010f6040750310040445c010034020000c540c0607242c024039110304080049070300da84000c580404c40809803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 468538929 1250 468537679 468537683
    0x130f05030a0804050118051206070206090c13090f021005071104050f06040c0e220b030105071709100603141e072304020a020d1e09050103150b03010b07031b 69
    0x540c2c0343c142040c00440e0035511031200f00411003404040040d440e11450030b11488058010081c0c42eaa0501c0c01d030003802c20001a0006d038051703100d906080804c1e9035400d099405d1180c0d0b80800550140c5620b000c8284020005001c0d5104194812006000390448010100300d0f1040c200240c00303440c044100700c02c40b1000e8514030451031011000a100342040c2d404140d180000341800e00c52078004400058511102401f113030400041340d81c452107030301c01c1070251802210080f8003e0001d4074111000818252925918000a05601c40843d450034010711009140d05039002083c0b04117500c078101003154110010380041203200d00b0050840540e200300e61b1300300700f50014028205171840c0c5003818a043d01d010105408104196280700c1d06541c443c4010017aa0502c0c5e0060040d040c40c008d03000c0c1044000064203109252452944810076038020308110540d1024280000c09020700030b0460940c1000c0e82184040030b2000001103079290101c03001e8000c0e148241c1e01c220f0364214018500d0400040a800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 468540179 1250 468538929 468538943
    0x3020f0316060906060306050109021c1a060a2d020c030a0803060d05011b0305060a24030e01090c2306040506070602340212011b030e030708130f05030a 67
    0x10340052583c0d0465404035005040106803e5102d40710082140c0080c0e124219056001849a0040140528542c0e105440c4001049a4010184800845040b01001d541b08060020355194501d009440742202c011000c2ca81302c00071001e036960b840100310000a040051f200c1c950b81e4540364540094042c042a40c00080c0c1030641c1c40d03440600040d02c0380001d0480315552611500f04040726003c1404000503445d40c3c0c049500e05001c010b1111441d40c80e000401c4250310000909101c1080d5801d01440c40c1952800055501e001c003c0305004200c2c9a1009007030b1a9015000682c03c040c98054030780151145540e013840802c404108115072040b4400c054101400384659008103001d43d010b0040040c107038454404041881c0c2100c00c007615280da0803019000e10501401c01e605180325601c4000c1c071850f00070000451110030340400014401184c074101511000301c074084800134410b40e103880f580103021a859140c40b06101011041600a004900e614094002020701d00010100c030250b4001754 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 468541429 1250 468540179 468540217
    0x303110f1020030c040f060906080601121803080103061a0d0b07031e05070305011d040f110d03030b030d021216170d0207060b090105010e1210020c060403020f03 71
    0x460704080c0640054041c0c041444400c1416a200e8100056110744554403131141d407203080c11100c1003400d4041e0411810000440005c0c4a0140c200070141c1e004a02402d00076891079030501d4500c00b5080c855965000300f803401d42280b04164000c0d081c81e05803842014280507039017400c050101c00d0081e102c10103600a40c6404680c02280740c5c19a130a811400b50726001c82c65800e514a140c41d00f80c075600c0885000ea65500400091550521500d17024001c44083c1121825060440b803400500180014000c200a09011003c1210204130346080600c081c081c4482c00c1d26604014005105ea4400a0b00074024040104e49030b6102013031280d0f9082c0302541203820b0200c40076078044c5502c82c00380c080f80e401850350000740b11a4101005070003465a80c03000540c0d2120285841026111496440f6001c3c0c05901c00500c1644e80040741e8200380f603000e80320156101d5001d4400703850900202d4945030744034400a1041700240f00851120302c01d070700940803908020340070000d95540b480380e280d4252180381c00b00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 468542679 1250 468541429 468541453
    0x111040603020d110a0f0e220c121107050114040302121803101a042d020714010c020f0f1c05090a06090911040509040f0c0e010e010303110f 62
    0x241c0948010f49120030b000540401e60080c4641036401044001c000c501c03090b0680c01107952005c0d58180810040d10b070518941520100e43c810305180803981074186484e040040300c080d1081c100d03540a052140320a029214072182d0400c099440100c05941715400c00742803038a1812040011801294141c2c000c010118a01c0c3e8009401e170011000c040b40c1c410b090034010381302e681c10000300d5068007030307444005503020b01d424005030703c05079583d442400346040500c0000d1105200c0030f045001e00903a4000c820700c3d601c94200c54024030032000024007408002e0580070200f001503200d1040e5180d02d80896003850210101d0a55504003118074011310b6000080c890481b809903d65200141c4244c07c28904004680002402c6500c8907000600020f890701d8003086040603a010300c00f000000852014906030418010611010006201610310752145030f00070200701c140b5400c0760040c0f59480c203c40207561540384524942901384029400641162400300200c031001c03546080c10101382004010202082c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 468543929 1250 468542679 468542681
    0x30a082d19140301032409121d150310050102120a030c12050a2702011706060c0f010b0108070e180603030c0304140a0b090306010b07080405060a080f090111040603 72
    0x101295104006039042a2658840410b000d540614850581c615090310550440c103011110034a050031583e00f840c1281011664012100d40e507010103152140300101404540e1101100c950500e171b8214074804031100401541101950003500c5420704201d0b0942c0e1400126500e00d103000c40d000e0000010454601d045009a11400c09007030350342000903e908203021100e0855104032516840f02e41c8850841c4a458814800d4880c0c14000d0701d0007850b20103840e000286400421440d24000c92a601c0101d5130559660044e0344a9550080446005010440b015806829120041d0f40444c41d4513003c40d02c4c542c000c098007004484054012a15049000c00041440e82d01030082500350004020812030b014040c070080019200c0c000b01c903034142e1103010074807141003030a074800b0f0715250341489840010b9a01041507411207400c680000d8840a0700c1c2045201403045034401e507400513001480840da56002400c85101d0400b1000d03483d001c0d80c820f40c54a090f12030070b240c041c031203030020030082c4146406 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 468545179 1250 468543929 468543967
    0x14040902070c272f0306040e0a0305040f05010816032a180b0304030f11100204090b1309120c0606050306010803090a0b090f130b030a082d 61
    0xa078142d22001d641c0f80d8104900f400c40c0d02400c142040700050402c103107482d41c09085442200600c8030100050302000f44003c0c0808000c64804c203c9001004c90480c4c3e4032a040040703520382c458180d0342940d0b510311703010b401d0ba403162140500c3c83c164244d00040a602804040e4490311000f1010b213036080c100c8100b20014000c1421100c01000009040403030030f548800c10316030071689501c4d100c00e0304080418002100030305a210314a200760400400c0f0000b43e100852102400e9507090003030700354918450303242c10100012850220b8610105c0c0005000207541c2181030044002e072940c450a605013010340055580c81e450103441c0078901c441106445101d14032124030790b8054580003c009480301c0010b4108002070748078a00036030011506844518000100c0d038000c0803406411480c04180201003034142003801d840c0e40c0b103509030307007541100c500d410b81023400c2c201802811b6451440e040d181c210004e40140408c0c400382036007261244110701c000120003e120700303e080302c6070074140141c0b298941e01d54 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 468546429 1250 468545179 468545183
    0x6060a11031611131b0c020112090b0a0f1a090606040504022701020303010e060904060207060c0c050f030a0804020405090705060c0d0210110d1a030a061a011404090207 74
    0x1108011081006020008040c111031140c4901c0448951400c10424452030b0541004d0a83d8503103810b902c0a24403060510100f40c1481c105031300c6440c003c0c00142c54082d10400001e082a0609040c1f800304102504070b144203800c2c4c80f00801070072035904401d00886640c442c3e65002d17100c03e01c1c00000c3c00e2401c50001a030000740140b10b123103855101c00c0420700381d802402e410b018801c0e525500080d200310407562142030790301c02c0c801141158504610250407840190146000d6900c6a001c42c1c01c3c049076404448241d0f400071010b0002c5c81049030300911400a2403030903030300d5006024220301b40311004011640c424525582d83c0105844030b030204001414040c00402052142110016490b01c80e140982100305110000c0c084c50322484101a0518001018004036035280c40c0c2000038544448050354070381868000c00003004c140080220b10340303504820900b54944104051041048a190811100001c809061180ca03a082e41c00545d042e800c000070342141110f00b44001c1c0507140345c0798042d0043c94 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 468547679 1250 468546429 468546433
    0x301051302181005151305040510060f0201020f03040b070e150d0e0102070b0405030703110d050a030c0c14160b090f010c030203040506120609060102062e030b0106020109030801080606060a11 84
    0x203a0391400182d0984480c0326070320701c1d04d80104507110010306d2540154020b1606842c14482d82c5040c18042001b0710840c0152424003000d0507188150354401d42c1941c2980e03103404075040d503074205401c1a19031490225010702c0082e420100b180c00034140450380c151548031004079503060152148000001d0300c2ca20303858071103566090003c1e4020920010b105802a4015001f4540da200f56080003803030204010700305003c0750300001c2001c8420354094110f465500445c82c00048415000500319049079104201a14166803620700f031400f2280491032170b4550350f800360f0190030300359181c903048011b0040a1003154401190040048554000c9900c81c0320b05102e40306072031800303494000103940d580102458080e82e02c04a420050581005566250801c609000800c8149845120a00005d80450054030f0716802800103000721503440d10210041c59018040136203a68407950000d000702805542070380042c0740380000140507078000ca01c5a02650700605071b185040c43c0743c801a106071894a402c00e0480c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 468548929 1250 468547679 468547711
    0x20d0818030702130203090d020f060c0304020f0405040b0105030c01020a0b01150507150605130515040209121005060906010f02070303300e0706030204060c12020a020915030105130218 81
    0x5030f0311001348030780c00991a1001a100e0030420001c619150b130440e401001c1d94001d075480c40c0c40403800181e06900c035401034003850f030329030311f51000c16144200194680e82107801c0c501803104008800c180e185c142c1d242582111120301c0c0d0827004a0350340c2c2008001a051141130300041c020800c0503c03001500808505040e0f10b8284240d0361301186e20700040075160155503c580502031072400013400701503809035400070702c184e040c03542c404404c4607851071900384510741c0001c015000f521035103103400300583c0d0302e815580c6458807000340b10090101228282d220ba40390b90005000f641c01140d075003e0009441e0300600c844c6003159800d41e000c1c05034160540322500400403101031160240c001800256038410301146040c0807090340da00e8166a40c12100c10715005000502039140d100a0700c251207900480d2a80740202c86100c181d0a20b80e2503600030790001c403080104116824002c40c09a1300b800250f0003000103a80d040348100095420800003503002078064000e0050080c0c45451640010b81440c400010b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 468550179 1250 468548929 468548933
    0x2907110117042a060f1d0a0305070302040b030105091509150103030c051c020c13020f03010f081c080c09030c060c0d091401050a0522180c020d08180307 67
    0x101c001100c1c2100d003501c42010549080e00c007000c10100c0e84034030103c0307485040d090203c05840380d2606229034040000507150100300740d805080380c1c40c0000c2c02604410720951039003851a15180b950105038022800d0880003440e5003014400d40d41b2034a84070300034040e07500d42c010405104da680941004100e1084040d914400c03d10400c50380d009521039154841c0c040c485103422800e040d0102c892a004018803001d00420326004514080186811945c0343c1004100e000ca041c0203024040340e20b501c0300c1c00800085003901032030b0020002d58204030300710350356102d4000200034002d88884902c0001a1420301040400110601804c00c4c180d00400f9100c9040d002c8010400d9600541c02100f40359004502c45030402e0340020141000c0c0c1204000c080d90030305801d001030aa07106e000e0000701001000266082d0450241a040243c0c00100d004a101d15548000c111210849005100701e05c80c5002582d41c12a4000181034400c110f5a4407007641130b42d0b601c00f449030405003030a40107506000c04c00c98400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 468551429 1250 468550179 468550217
    0x20d0b0a0f020a050322030e0622080102130b07080418020d090b060439180b0a03060501021902150409050a0603060c0c03080f191529071101 62
    0x43e80036031560f99952289009048a00500c03e40d5a0403110208400e40540100c4d50000c01d941507903409596031541c981c22107800d07030042c0d8840e0000507036007211076a010440f810190014041144032014050381c103500d03144400e401e840f888030003c1000004200c104107000107240c42c69414907410302c0050501c25407101035019143d140c0000c43e112040e0f5400c0192605d01441801d900c00e002800141040c0e106005144180b6200e00039010035042401e00036011070703c0381d59000c2c91144404000500c05541c1c034000c81c01c581045071940007090403e0000301b0254400200c028102440c1e2802e044900c1071602801400124003442c4200304008000100e1201214059507008503816030000032078038174600303180c001c851001d01c468080051034034020020030f40c003800c130507080b038100c516002c07a0745c480b0084241400202403d4082032070078450b02d0a814141c00e5405c00880d5a90507025481c031601100d030b28000e4540a40b0224861824450600403c2405081e01c11002060412030303054409002441 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 468552679 1250 468551429 468551437
    0x4050a1e090212010c27050a08030304061a1c0510060b0715090201080403030b01170f090708070f0b0309070902070b0a0c0e0f040c0c0213020a020105090307020d0b0a0f02 75
    0x31110780c07039600840c21801d01200380000d5801032402000881c02080004004604410403a40d0071000f152805284150406151004280080400ba176840c2e1b245d52280d20381d0011102500c030ba0b0301d01130a210101202000a0390b100200828044044004d180050758048420100f1b90340d510480254541c40d00745071160308060100f240d03a90f6201c421078038000c0c0515250804da0703048d59007402e05180050342c024a50a801942c1424080f4204180c20012107542c030455a01034131510140c02801000941c3c0260a40a03680807019550219240c00c0f59a0791940c5030b00c43e40c84501c800c800d040003003018003005150410180400d072580555070b20058030580c2c104840548020030003031b0910040c0b1030544202c401d00000382c2880300080c5150310002c2d80713140d8030780e10803401652078221a100091040c64a041d0659004200c1a038000c80e5031640c0009400040d08100550b190101007a0114400000d0711503c0e64020040f0b003501032150340340d00c082c50000d081815155168a001c4000084500281c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 468553929 1250 468552679 468552731
    0x4020a0c1b1d190c1d0d0f0807081204030302070303230a0c0207080304080d2c1002010f0f0c020705010905130c020f010903020a060c08040b011401210b0a1d010504050a 74
    0x452825006030705d00a090600d01c91940304030b0044100d0310014120040c0103c00c590840b009507120b21081c202001184a0104142e0f10400e4540400c8100f64169000e0503205000742e80400c071031000142400f1030b0a12001600701100c1c5a08005070ba02115900640e842000d1031050301c22144d510984549190003e4200c0000d90300715007a4103031820303813200903803a00c1d00354401e40d6941d508803050020501e05464242c1c0d80108400303250060b20034000d4014008001003d00c0030050302007081e903001c00415000034082e00502900d580001c042d8850381410041d01c03c0204420b24003108107070a0741c0180606030402d010b5025030036500300c04610030300c6450082400b0f900034210b13182e00c603d040070468140c81d0b010f20a02002e4418040400c01c00d807403150544031694000010214800f0041e81c024207a0500e20350202031400d03043c03250651a8018045585e4159602c018040d05d841008802d00d0b80500c4001ca58012440104201e14041d0009a0080c1c900306001401055404406c80043c01c01c0c015 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 468555179 1250 468553929 468553937
    0x31005010f08120301060f1209020d06051f0b09130b030a060504110603160c0302010b0402040803070209060114030a0902011421100812090f04020a0c1b1d190c 70
    0x104006040c070500199090184452821340b80d503040407406800c284802e0f10510400c0280c035207401c2e8031140384c0e0202e00700580041c81e05282c04c2c2c482c03810303801030001124401d00490101d0442d100309101c0e1030202c1f0940307241111035401d1400a070103000c20007292aa50312251078851008100703903141800b0b0002481e00a0748049050f1429040486641d1019540f20740542410420040100302000c05100481c440346045410418182400c03809800c4e0000c901ea40a0b200080000c0c0d40c0720000000c001292003034400010340e41e80c4000540d4580d1052410300e4090300300b000003d102109551005041c40d105040c040c2c86086080e220106503002420440415010710281c1d5908030284064140d02c464030414000e034142c00c080c082c54441d89090007109103440003045200b059601c0d180241640032001d04115141c5810344e200504c01d49a80d10140e90008414540101103034412014409892120341c030b014090040a0410076842001002950f444181d101c0003200d14441e401524040d81c1e0a80d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 468556429 1250 468555179 468555209
    0x303360901060903020618030d0f0305090a03050702060a051e0d0e0d1211072a090e060726010303020d02070504090c0506070f050106030602210f0f0603100501 70
    0x4802002050212829449034900c0001003049541c030460a10581e64180c8901d501c9412554200c0e4441c030440c1030442d854040d0034520f241c80350303201e1004070070031519a07000d000c280c440d03624054aa003121000580051001c11240015041c210020091221030346010391506a50304045030804181882994808030300041000300304440b030090480d0600401c014007880141d00901406042440c42d612149a4807050b6000058029500790f80b01e032074210006550180401e0600e00b16030b4621800400c00000c401c50100b1803012610440c2c01404042e4024101c517104e802054403000c0789480c07281c2200816070b1201302c0301c1d04a404540c0c0250f109400a04054100c4000a8104026038202600807450650b074140418141250310702151010b031507042d40d518a9091850a4440041003d0915800e040c0000100b0100381e005240140422200e925120b5592004e0244000f007954120301c0e180d0104045030000a45814207500807000504490b03855080b80c210302d00760788003640490030303003c180c072 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 468557679 1250 468556429 468556507
    0x5040b030a0b010f1a0c1b030703050f0106060906140708030604060329011409150d2103060605090f090c210117010504050a0314131502012a0e0303 65
    0x10301e00301d004103140300817034206800da142680e9074a900380e90300c2e10a5140310143c2e403035584040c880700b40650b4008081c1c0b003402503c03e00c0720b400b034840c512800c40050300e14000060359620401c0c1894500c0b96101c55140b80c514283c0300c03400300b41c1011b843c00c4e91041d5104400800650740c448084910196940c0f00030106018985014403884140d1014154a500d80d10542141e55948495a8854031714816810008201404100c40c0140d002004001002c0e100e203c0c8043e400c4c04007210900a0503550521156842d100121214012021050b030000029450100c4601e00800084c2d407000b0707180d4815080080d00c1c400200c402965030210707004c03209482d0040c090304058040d010041101d040091003a81042e03610540e0300c0c0c2d103c0e527002d400c10040c0f11344001d011601e40100e0701007140300281c140c09552600c0150070004801c50480001d503180100341400d26110100603402d0151406072100c10996920040e0303080d405107440b0aa040c00104002d14503200e4060a60120004848814400d82c0703202d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 468558929 1250 468557679 468557699
    0xf14030702010f0609060b1209030909040312150302100f020a0602040b070302061005090f071403010e07020d030c05032403061e0c03040f1104140f190e0705040b030a0b010f 76
    0x1394102101c2c0a0620809020070140c0d08100e8a0a4040381100c000030754580303a40c0c504601869a9032075000382060f040c0801d141c1c2c480c2c01003080c610b072100f042101c08205002c4400c0c00e0624840250060044202e070b40174603025292081c81c800280c01a030748203200560f102c104991142d0007015100b0804510242815410044c5a9128107680410001c803400d210024807603090003007102e5a030b44642000550128410b110712008a220240055265615810710321a441811122103005125126081d0101403280c00390644116180d241c0a11b103442e994010074400e5010b12089540e4131403030005106545082040602c81c0c16861011001405401c00c541d540b18009070807003215840500c1800b002c9140b01c0859a0555417100d501095041060003040251184d4a1a40403200f400c4081140842c2c015040c0ca21800b0a45000c039031500080d101e10003101d940d040141036503440040c05000360300306030f032064071803030f80003000c07035142002c0b80d65000c2d40302d4006d0700a640c000c030f0303c840200417507414 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 468560179 1250 468558929 468558941
    0x702010617210306191203120203040b0a0b0a0b040f0504110c0601120c030609030e01030506010c41030c0c01030e061f0f080a11010903120f14030702010f 68
    0x1c04009000d910b250b041d1401004800c1c000b10001910300040451213503079a0304120202038543c4103950b840349640b150103900181030303c1d006401141140b6840300e007416041c42143d01c595440041d000c03c076100c540343d54000b44114151181c011131003410104098100c3c1c0042d00003015040d0141000d68200418082a11403219032042180e80500c01d0028003180401c1d202e040d44e012030043d110280050170090000b202c2c541c0050202440c080d000350601d03a110540c03420440d030a890504c4503454110045901d00380074600601260904803900d180c089840501c1c90034185d4103044070817400c01044ca180c950103c1e00010000c0baa00002d40b82d01c2d0480140f08410034450b09090810901204444441d00d48400800c00c44950404e5000c1003241c6840c070a4070740103807200c48843c120035611201e049a440501002c00d48002400f011142541c1d807240c2020820b40750302c61269108410716080c144d80c0c2d0308000083c1024422070b045034500303a80c0441d010354403a1444e0f50010070940c1d80e107c03840040b038003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 468561429 1250 468560179 468560219
    0x210020c0a03110406180203090d09050f0f04020c030c060405060106090308030612010f110405011d03071505160f15200a0507020301020a2714010c061407020106 71
    0x2400c100c400c960364100320002202d800c5400d81005041c5500014000c000580000c429030786e1641d4101c02c4c82c1010303405184540e200b00f080f11501d010400b02134822034018464554040c101c000c494145060021041041c07a802403c09070501481020543c02c64109255042c0141e00400800007170100030044107004000c02c0c18113944140c115150f40c2c0c2c15200080480380107210701c900084180b0000d5120900c10f40540b00100b1101409450340c44890340079104890014075070a44000c810040d20001c1340c12803100400408800c1d150031214043d1038000c898031018020188147c0c0d1022a9030000714000c80e100d51403407a1000c5907441d00f40f000d0011a2189410180f410ba08201c2c4984117182415040001c0744046403030f4002c50350300301c40d07074400c0040080d0554004500c003e00660403544d02504170100704045a174031f194500c1000a0343caa5032007415844280707003d00f007805e940600e210340b2980740544001f040290440200c0d0100300780079114080140c0d56010204040c43d10b00c1080c0321401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 468562679 1250 468561429 468561433
    0x5030918040b040b06210c191217041a0301171501050105031008010204080a1101110c0402030a020403080c06060f030c0918010b09040302070e0606030708130611070c03021002 77
    0x705280c0c50300055100000c2c00100500400e0740800c40a95441400103424074480764401000c500007628251601080906e2a001c0c85000e58078040b10f440200c10041516000300341848074071590746038264520711840d104800043c040202040b001000d81c2c110079070000311000c07969654981541424050317241210402981c00803c4980c0c0b11106030045203044a8092030050b480351900d00070110100f0b0b01e640203286c1d545c8001800241c0d49008103085c40c0041c0035203854008100c1d81130042d128020014800403a5030011092601545003d5000c3c40e04000c5048006003816200d40d03900c4855400b80030000c0b61540302808009480c42e202094800c46601540908200c49940c0013041042c4000380100080a907a1b0000c01d14045007580078818001c4000c1100070746080c6824003a40300c0413180074020081c0d50b4840018407600f0200c3c2100d0003014182e03642880b56071503a00f01401140e140b0700031a62941c0304c032045d06883c20640003030a242402075050741c07170b91444e40c0704100d0400c01400b605010342d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 468563929 1250 468562679 468562681
    0xf0306080307060b030c1c020f030d0f1214040605041401060f03030c06020c0a1b0602010c0801060c1b061d03070605160f0b0703060e0619090f021605030918 69
    0x102001c000d8405496008402164100d180c80000703051002e9209419000200304a1030740b540c1c405400c4a141c042e000f501c5414004920300c3c141a1164400c0340d0280100711500f40040119120701c04060300c030703142000005443c190714116181d00020a95096900701e0f2030b02d05001c103010340c40844130305505480c0001c001c1e07203140a2002c9118030302403001400388400840803206001c1d00c0c0d0100c4412450b881d056030b91035420382c0380c6001c04640c028a04246995205804039002e0300501c02c07c0b04541f102d45880e01640c0c60000102c59407c220603086030750014440c1d06100c00714844c891100580032588a40052000110069900e06045600e05200742c2c0420000c205541d00401100e52454140c000f5040d4080300e410604152159802c0081c04000b50300200310086503d584090180c031540221140640c450200b00310b055040321250308c07001c03245542c040100d51502c1d400741d07010800d4010701509211062103004800c100585060b500c503080021510454902601c0d1800c04403000c1e0310070070013 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 468565179 1250 468563929 468563939
    0x9051905010f141605060f070c020d0f141617150114030a0b07031b031523090a0f060503030a1202090a1203030e010b010e061c110d05070f0306 63
    0x940c000c0140751003440740200a00f03007420003010884410a01600f14120190403610f40035a9440d011030344416110b080101107541c036403040305081d5603e50010903100d6044204d80300d1680d902c40e02c003c1102c45420550b403940c4070f034005000f401858601e00000001003460014000c80c00200c2503036000058110000107030070700828443c1c0505441c0b1f02c481c0c08000340c200b6000309150a03140d102c0a0081d594100c2080340f16a4543c10040700341244e04031440302d1680b038140a5040d1091400020702000754014140680e160305e60340c0e903075015692014038130000811001710b2105102520301404040e02c4070002c4181c041c00d0b010b0f05004207401d070b000703600c0c0030300c81d0f4401031078129480c0003c449c0390f0700001e40421665820b41c400d00070301802e0900d04122440f610700507006001e0640b0340301e16542440902c0034076600a980442084002500b0185030075030444004030761496542840b017149503601e50501e07460414002500c040410900002013500701844043d0000040c151140c041608003001440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 468566429 1250 468565179 468565187
    0x1f0f030c14030615041401170103030f0c020a1a030108071e230406090f050a0b15071b03030809010612080d020307031415010e0906010206061e030307030905190501 72
    0xc0e90807041e892040e103a40f1100300103810501d11800e030b0302030514045000318140c400e18126500d1900c0988803503441c16100f8030040008102444090003107614a10040340b698003544410041500c01040780d003865450ba54400c080c003403160903807408420080014040c00c10300300045d0019001c0501d4082901c6400c1130060031a0299015903565404803038101c015441c4684e450302d04100d0000d0007882095222007180005088440404040c0c504003c0071401c3c1030310314071402003035840c054410a01c680114000300e0341a8807110301254050080a0a080c03003030700749001040514801c0d0b0f2816070904014525609480e09034001d80d5084405140000001e070700c0004a03204803421141c00f58685c0e58961003a030040410b041c0c2a0264070020003003211034100c2020154900e48262500007803000c40350b05000401d0000c545650169004101061a500d070040e24414110143e03d8000f810241e0780300402d0842d0020303603003100400c041c28003d0003685003c60800000c0c1029894804902e403a140c0020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 468567679 1250 468566429 468566447
    0x901021207120603170324150c0c03060c030405060708160c061d01020d06090b1c02031009061a01051207030513050a210903050c09151f0f030c 63
    0x60144004100c02d404601980e41202d0025a0050b20382d0525100c40c05581c4080e900444d8000426041121611240c0f26401c80c9401c140038041c28034500c2a11328001c4900d181c3c85a02c0b181c0081c41002d401044940d020010705100703801c2c9a00880e240e080629040386091800340441f428002d0610400004050503d0042c51100070351a2150100290b810094028040282c990010501e51821030880d214150010100e100caa501c0400115035074000100845000d03140c0325038051019442030402c0718039140c5402045000600741c03441b10482c001ca131811070b6402c03131040f58150384910441c003540b40307034602841d0301540a00348036103070410001c840d54000e00020305040a0550310404a44e40120030390207101443c0c0d0000845070020340d035092602d1200d007014039102001c080c4e1445114144e100304011011650f0180003026000b807800d04101544100412400c0c5c0103406100c40c10581d40c0d071444103c002d420b4203104000c180712203900140030705540e4290340c0905080111980400341d1041d008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 468568929 1250 468567679 468567691
    0x3061a040512060937050c09100602060c0906090306040f02090106030203010b390105010305100c0c12030b040f0203090601060e10080408120405030a02060a061d0714041d09010212 79
    0x100030001a19560380c000c0030044174000d05004044240020000c000811610780c4000306d9a400c05c0d96a14842104002d47d14003603500141c024501182c14051050043c240805005042c1170030402c40d2401300f450880101d4041e214212110049000d5003001408540500180e182c03d519660400e0407000f4030303202e2584030301d020520103881000441001c400c3c40403800d401d4220500c061074260025400b034202030000382c405019807501415900b8061203440071418194850180c00c00c0365454004201c6407850000080c036407502c1d001c5c14196a648203c52070302880710f00050b02c0381081e00e0751514100c2d05030414001e1105070340b040e4001e40d0300d0982c0340c4070010700c03482c10019075030315890110128041d4007944d031001e40c009400d2004009010016103c018174580c00c47c0c206da030f140c102050036141030b44501d034407840d180e40e521480c007540407642d01e0340580c96081040281813450391a12281d44294000b00b00480701d5005142641c0114030301c02d0300200f40500030350800703a008404e440410005408 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 468570179 1250 468568929 468568963
    0xb060607020a0e070c02040b040b0d02010f0302040807030c0e0a0c09050f01050c12070b070f0c030e01020c030715030f110901050702150c0610060305150402090103061a0405120609 79
    0x480d0215079400d098100640b20000301501c3d907081c00003010f01654000e00e0101d1149040c41400155070915101e01c01f11004000d213086090543c940064038072194030200301e810582c00700400706140300c0400c0410001c610415030700d403807145026600c08441780c0140884c100d203400d00d90032801d040e50010440302900c4007298182c2303444129100684d031a22850550401034018241c03403002029072803005e011401e0042a001c0e1543e80e4010b012502c00765034001160211b0348400740b1401007441a20f409001d054180101d60b010307441440028900f80b00c0303920989003001128000c1d81c1031380d4140141c00ea43c800713590062007001c601003040c0301700d80240c0034114100130f0085240011341d96520340c080c0000b400728048954801d904150103841c2d940c1201c20300a01c1240f048001030061003403154070b104146540410604041440c1088065070208800504050b110003012424034416102c001100ba4094501d90b911460401031000511076860000305540050040200d10100414050520189240f03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 468571429 1250 468570179 468570187
    0x11106101403070806150913031b0f020d121202090a0e071404080706081303020604060504080915091e090417040b040806070e0405130308043e0303070b0606 69
    0x102103071034455150712403062442180180001d0414021520300c042201f95440d41c0140c0c0c40041104d00041d00400040000342c0040c500d000c43e405a854400500b84030348110b4814040c16000142c1b0b000a0305000d490503280294110320a980162000c03201e80f40c40310066043c0101c03040016400d00ba5803140d9107003010403000086a107403195820045903140d4241142c0c9072510b074480143c0e80d44050080b003003c039640f4004991010f00c00c0c08442c010542c994010b08559450390f6070000a0f050213001202c0c02041800a24026034030703250050030064416080c42c0d114022030342003002c1d842e2007110341081505020b2215a45481c0c1c040001e600503003015405483d01345810305010288100e83c002043d00328041404580380101041442c05843d1faa5181c80d142140501003004880c0309940003040721070300c110f03102c000034021441d1647c01303030261528011040c45d42e200358144860458204105a041c0c030385424803144144070503031661800b500103500b401d059540304d001e1072801515880c41540042 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 468572679 1250 468571429 468571469
    0x20d0606082e0801060609060e010905090a02160503160302150c07230a0b0105130b030c150c030307080108101e05040203210901031d070608040302030d0c05070201110610 75
    0x341c81c14010083e0000800100d561440e00810a0000c4d010780d00c0050781144404696610a600740703400e6603001407140309181c0301d01f04003000951014900407844505020030a000ca5400c1c0050103050395481c018076000400c80c40c000b800d12010f581e003019400201e2080c04410540a410340d841c1d146d228040102160558045407200c0c10072445191040c802c1101c1481044140e03400c1310b040b244259541e200da0800711840d0829a611032040e41c0c2c00d6403101031a8805490640a9042054400d14a80f4a001c045e040b000e400c5920896480c0c001c04d22400042107289410401c1003042034800300100007e00d0784442c0d540d1215030000f0001c005688400c04501990313001e000c002081101c00400e201745214030390050b034081d0048000745003c80d1034410207220440342d07910140390301e480c072101070407800b4204801500c844801400503400c51006004011780440c9038807607200817140d582c5500782c88031110701c0014400510001103101c0c03074000d00b09000f0107801500300c010540303421441001002000d2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 468573929 1250 468572679 468572761
    0x6020c160312082e0e0703090201211d030a0801080a0f0303050601090e04031e09080304030b0703060305120306090705210415020a11011803080c090301060504020d020d060608 77
    0x440d2043c0204040c904c4104094100c0042803003c4035a04034100e085541d60030320940032921103003006030100f15003111965000c1071000391340086040714500040e500206008801d801c0782c0d4142c0302c0f03d596200262144a881d00102c2c0d00303005119031346c0148503400540da40c28074007109000004081c5500d40c000700d84160300075a1000702502c003c3c468580c0c01d18007410001e10b01044000b100d84d12046000c41c25865520410b00041681d108500852a2602e940d4848800d1000100350204043e07540c2c41c08000244140103908424414180c003640700e0503d80b007040080b400c003800c0001880801c2108521040c0c4054130300e83c08946070701e034021140c2e40782c0c14629089260241c00b03698661001980035005508059994040a07204000f0801300000803015000d400300b2000c0a0003182e003e2000076036158213880100f22219000c0d0001c40e00960703420104040c2e800c1b15000300d8249401040c40344980c0403900ca07080086c4054540348100d800d00c80400910070100702110103031400001e042c14403620390 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 468575179 1250 468573929 468573961
    0xa15120501060b03132a03031407140d080601030203060a09180813080c06030c04120602040819031704030e040f02070b0103050705030624010e040b040906020c16031208 74
    0x3250307480c3c55032803030030480d028215a0018422500a0000000808812070f842003030481c519510760768441540c2907480680300000e10746400b200b1180e00b00030100000e40403062040740304258a009120344407040d4009844820010102c604041c41030040080355555101d030743c1e046600c1460001514284030002c2011a101460050221640042e000c88a540d01c0207041049649210984588101c0c16040285900c01941d24500000301070200340000c880a402104240380f25200042c5000d9594034581d041209500c0250300c001d038045100320038190400c84490103496001c0f0070405500d00341da4090031441c000006a4081e641d101c0b403603034940195a04540025404c041c611042e5a03492900541c0d419003401064028024000070170380081d0007859803480c039030101c821111085000130044501c0560720802c69841522101c541c0f460347c5a610403403c07141d0044801684e24a40740030407505d4111401c100d20a405060b02003000032688080c1800158281c6103440030454464902090781c10034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 468576429 1250 468575179 468575189
    0x10110a060501170c030f06010312120e0715030c170c070803040c031a090d0c080708190f1103030a0f0204050a06020303040c0f05060d09061e140a1512050106 69
    0x12034140080752060007040008400038030001142d13041c4c3c03503030070525843d52000005128142c0c0200018030015965a8401900c10854504114034802d5000c10009a4803404003100c50f6070020300c020312001d0404401466200e901d401c041c0002c640e001d90080a02040c1020680c003010348001142c01d00200c034045881c41074112020546a0400307013002c0000d02002d11084450115184d00119114844c0c0070301c620072501000542003100a040c3c0907100d000001c2c9040703c21801c00c2100c5000100c401d00507218110201d001070000090180d40901030012030100c141c03d00001400400b1000360020840380d1010007200301148043d20082048040d0065822041c0d2046800354081602a0700001961007103001e140da0204d10707561100000c2c91410240107607504244100404400c07600b840e0000e06038035204002c0017402d807a00604c5084032602d21400d42841d1501c401c040842c00c410046600c2c0c0000d014501084520303611103002c0018922403084020050804194070240442076101c039000344 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 468577679 1250 468576429 468576431
    0x1050d121b03020610170a03030507020309091314030c120705010f05090303040309210210021e0d02150105061605010f1a1e011b020f0a0303031d0c10110a06 69
    0x9061502a44840c4102d41441d00044200170001c2c6802d00c205804942c2805080a043d0041f21030718101c0c080c1c00300078141020b600c0200b02101e15a19660382c510b11582003503085081c4040149021100744100c48480003456005200c414610180851400d00100e501041141d80390814039205014106803e42c2414852a01c010044001c0307010006510582c480c0e40d820003140c0d1100d00030341d200800001002107440baa42188001801d0a543e00100204c2d00c1c011600b6100f694070307101d030046c0801240340300141c20060031014080d0301080880f564030a06103171002d4560502000c14528010f445500c52401c004544c0d400a000303081d4041441c02400410920041100c08414003482e10303031594560003a02c400400301e500002d8800c10030500c401c16540e0307240400031841041c0b500e0f0314008007a41e00001c511b82c824203507580c84200b100107603c42e840100e13420202c142c0c4800b0039040f40303050007040d41000316000029640c440d0510703080d128605000300d401b5401d920641c40c0888940c001481d40d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 468578929 1250 468577679 468577727
    0x3051609092d05010519080d05160203060108010614043b0d0309021008070e0114040909060e0c030a030c020904150213030b090c0d0803280509060f01050d12 69
    0x6079a42d40c200c14140c400944550410803004c4402c500078440d2031140310043d030005400d540001c0e09c03400c010407099800780132092190403550006410420207a01007002a99980c20070810444814002c2d0744d0440d08075030401c960300380e999102c0c05141e1044551003000d4218180c2c01c000c000f046d451000c030165010704440c0c1d408940c1002600800101000341d100300c180300d4051210701d1081d400644151078035698914140894401500c0354242100311009900041c4070101d2401001d20031451114025200440c00e0000c242c0011f041c000c0f01c045150003500036030200e40c013181d003003035021101590640e42d0a601d03580764144100b4440360305813a1403400340001812405825041110010340340100040107964540341c0c0c0c916901c40341c200c0356a40016810f44144082802c0b0805164002c501c5c0e008140c2c0c1003240c0e041c44107500042a9040c4515558a05009101100f000300ca82d0180d16560f5149155042c1400208402d10904c4000c12448005605c0d00c80d4034800e110345d00e680071901c03c0403981c0b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 468580179 1250 468578929 468579011
    0x6300102190305101a18040f0f05040209010f030f08030703060509090f070902090a060311130b030f0105030309090f0a0e030d0c1202090d0f0c050901150305160909 72
    0x505000e40341521451416000880c178060f4883d0034181710360a04026a00d0a5920703000c0b2681c08600c402c4081e4020742d1000a450720442c00e0013050000307150794000041c0c52806104026441906030010f1846020700d500510000390200d500344011a003044440d80c40780c7d60b4690480151900e40c000940040003501800003003180084e100c01302552000a840b0b0858079901030000301c2c06100c505a038040f4400d0ba04002d164001c2d403020f6100d00c03441da8070301d00e0b201c440441c095039510340303500181c0c02050000070001d92206400b0b420340500380c03c8000d140b40422480000b140803502509007191906407002190b813201040c0d1201290140020503640ca0304804042000100700c40880b0101040f01454100c1c0e80e9861403003100e5003204010000108488140c0350003004901e0550101c0d202c50b44007001140720740d2001c1c0341c01d00034800d920081c03040810401000b800d40340d000c1c10104040310010207a0030b038583c0050683c8251000b000c000115640040c1c0010000755100e00d00041e5003164602600b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 468581429 1250 468580179 468580181
    0x1061b12050c012313030207030602190906030218040e15010b0d180b011208041703040f0b28020a1a070912170f0904180209063001021903 61
    0x82034110003c21030511910444c40e6004d000d00c41c3d003900d80004400141c042c244001d0b03440070340ca01910441e07546d60348a5a42004a0b4130850010300f04402e07a05d0002d040c540c1c8406001c0182c5114a015401c1651181c0400241140c0c801c903148215219601c100c60310f0401c210700f581001030709281c100c139943c0d10348003540980e110300c9200a82c582003072000030400c1c03030307100a00f40c185070700c05150b20312030b864004550300880215000711000c074030400000075140c100d4940d490030309071014061941c0310b20309440040c01e11240d6101c00c108030b10500000e11000d01c00c10744406d5148000d5104007103808500d804034180001030000600004580f0700028403000300c120201e1007080240ca540c0040e40d1100d000182909800100400711400ea081180036582d55034083e0a00c520242c1c155401c01006900080c181c540400404154540d900300170340540c81d124818035045a0301791900460100960041004000d0b0a90310351300244c1e4410202a040c1c500754100c404a520011843c0006004540700034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 468582679 1250 468581429 468581437
    0x1c14030714120f180c0f10020715090f0905060d060903022503060f020408030307050903070f081c030203091203060a030206031017060709090e0c060a031d0a0b01061b1205 75
    0x10125805048602100d001c0003a00c09041c0705c004001e40c43c425490340070041ca840d001d034450710450054141c0056115000b08000b5603c4442d510f035003401c41e007001e02a06a081c0d240c2d2003032102600300302c113002c0240c0701e2418000c1a42c0d00141d010680303d540d414260325052603021183d031078240a0710b004d201031401104000950380701715024051134808025aa0590149019140594004101007819140078000034504c04001600340c8078400d540f002121069200340d0b021548a41000000350f0300c100071003032068400b0b285400c0031415424042000c55541410707d640920200c000804580310b40d890002e038000841e4000c026580e64544007150b8505c12106104410001d014981060340c1104040f0340d1a2003582c1702d41d11004501d140030039803409084080c8400c4054068050400a140c541c8001004201c00035100410265000501d01072814080600c0c140c0d10b810440c80e0300b001800002201c0c1c1110240c0c80c00420171300403604e0005000074094001847c401d820115500080c1d0014068 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 468583929 1250 468582679 468582691
    0x21010603060f0902031e090c03030706021c060602120a020106090e16080303010b0f03040201200106061d061e0f04060e090105040e0a030f030e01020403051c14030714120f 75
    0x11889503036a4000d090f00341d000680748240c170459001390321076054403014615580078000d50304840715041c019010030b08652229038141c0e0360540010b00601c9000008140a1411403082d034204190b519102009482e80c4603561100d07625403000032442103452003500030b88040d1860441c2001003041d00d0150968862401c20b5000c1d1617034040c80000b804034004000c0d24100d41c00f000c24146072410300000c00d91941e000030800c90600940010000c2072020812181c07400c407007210300002c2e12504003c0041e10707100420445541550316030381c64600903100c0d94245d074540603123401d4429464010081604460150040881c06804003146c0018481d51000c0e0344200400161822205640c90b24240801c2c1c401032076040c1d12540c0305ca110500081d10a15034070500c60750519000a401d201c0051890a9a1140d80140c503d58003104418480d0708120784140b0204900e0304100d090411703172100414403070000501d46424841a40c00b00304403000920211195410f624918800c2407410030394001c0001c1c0141c0b80 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 468585179 1250 468583929 468583949
    0xf0901060608011203050904090503270301060b09100c080a1d0405010321022812050309060403110c0904120801080f07050f2106011d060d03052101060306 68
    0xc0061014011030500781a2984800507529002154130162056440088100d8105d41c0e180132070320218000f8409003881e880403040000a0382070581340c0402441c480c40401313110383d00d0603100700130040700e00d400c81d20200e904dea809413070481d03480300079200c0020b01c900141c0088400104820615405115441c044072900c0704080c081208900b1f1104031202400300600003c106103481021110f6030020f00e98001d1503104131900305640722a0381641c0110b94540103c0300e8603d044100800425003c07048080d03d03c1c0c904203003589041039441d952840054805021301000a1144000c0135003070000e00342006029200400604082c0703441a601810160306c10000b03640440041100c2e0000f00715440d403c010035000b010754030b043c0010804114a030f18030499003da441030104600000b146415040003500201600656151540c0407810381c60741c8070040040055030701000401d0b9100110403818a815240507500d8a4070302a00c0700300d104035a118407110410101c000241560b240c0c0004050b56402c000c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 468586429 1250 468585179 468585191
    0xb090f0a0c1b150b0a08031201080d050913290f03061603020a050d062c0f0708060103020c06040b1023040207081303030e120619050910050f0901 64
    0x400b202d0000e109075032012581c0c84481c031900424400481101603120020b800240301c1074030b00002d11007209907401401241c001041210382c00b00f818001b203004000c0180a0100f140e400ca070024584e105216803a4407a00a040140401010780e03846040711007001007036401c91100f20941409040700c9021410710480c08094500c2c524140440c00a0041300c1d030003203812031101d010301d0580107500301c0e00d0b92000b00030082c0988500d10b80c95005100050154410008110400d040c0700e4048030180d02000c01e14821020500080304800000d6035480401d034135145810b91103501c0102d010b4070601160709070038031685060005012081005a00035100403000d80115580d98403404004242084041d0103074524402d64415070030a03800500b00e02e4460300c1160f250101e111030100c1c41c600142c0050300010b110480100d8641807281030108010203070070046c445031400f00740d44e420340710b9183c06049055840d034001c9038060108004884080500030024040d614000102415440f030454012400d0340c2001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 468587679 1250 468586429 468586451
    0x90a06020a02030c1e03060a050406050718060f0905310e190203071502030901020106050d0209130204021e030a0b0f0102120708041508070f03060b070201080a0b090f0a 74
    0x202541e4956003c1c02510514040740304021450380003810b0400503400220490b0700513501800458494888210006440d0905e81495400c8601c003c0c296418000032400754111070b083c26240d1030469455141114034901700040403240e030006030f4003940c0c12884000b01c1400f800241d919981c42285d410320306115450055012000b994080c000021050f0852503400100c1e2402c64565601503002404540da865641e071003c00e040103a4569981c0140c001103807644c01d40d83d081c003403400145000c482c0d07400c1c0174280c0c0d0001070744500090040c1201e5841c45520404545030f07601500c3c08a07a4a0290480a0403910040c02e0385a008482040d0350524100078950507161942c1d507441d003a80181e0040c0980e4045001c00707111940710440039075100409010000b10b1041d903548540303401c070703003640d501000e07003401240034140c20402c00765481410305245083c030851041d81c0a0303804c81902460b10100b1615507281400c010f000d503006041e00602403208111100f98290a02d80c00303651190b80030000e1000c04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 468588929 1250 468587679 468587683
    0xc01050f070213111c0e0606090708070c0203010f090303050c0708030f090a0609030306030201080a050c09060a0905030109120809010b13090204150807080d090803030a0221040602090a0602 83
    0x40d81403011000144a84005424440c001c0f2a04040f018800142c20820140c5040f41d50401d901c0d00c2c0144c03c00868100d01601180a14154411050003e2060f402c2250006501c020f0042180c81007114180c0056000ca100d000d18031700c021f170003800811440c5080303121900900360340030082c3c021a0800c0c0c04144c025004004035004150000340c440d003151038070001c3d091038860140000c100d03441400c0c1c004003c142144610800d2034401d8800080082c03442c8005010a480113010041941c6030004200744114100c1c215000100103c0d40c00d03907103400e00c24081d11400d405070030082d015842d21503c0c20410001500900914103582ca908500d540c0d00c1ca4400e00760b83c0c08458440d0800410040190020101e800c0143c409100070000324000c100000c00c40b800c102e132580070040c140e001c504c0070022810103000142072044245001154641048103c40c1c2c4d91201400801c41d1030382c005103140e001c0004e42014610110104150743c4a400d003400c01101035008002e019104900c4d5180005401d800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 468590179 1250 468588929 468588937
    0x250215180607050d050a0207030b0108010f050703090c1406040305011b030e030f0702011407050303161803020d08030408131e06080f0406200a021b1915090b03010b0c0c0105 76
    0xc0f01e00200100403040c0c00c200c4294026628039819440b070942e010001030304102c2e205010f0043d1000001d80d5404144410303080c1d40028241509041c84c2422000101d0200c4820b8801d07140350848800742d00c0d40d8107001c24000c1c49a07070f101400c90751805c1101055103007008031045610515540500c42d52242c0e1420a460307200d8082c201203080310410482005500a1844541004890641908280e070b551101c40c1035a20480c5c040e00d00c44550141400041d40149070303419602170103040340d0811411580400c40071400c41001500501c000b000240c10400200101c0f000080c004901c090300942d0b4414002042c046802892b0005656a40220308107105000c501e01c03d019442051180d07032501c0d141d81c8028001203603a00580041603d000310344000020041500710132660050520001c41c4440050394030140c4e455a11400c1c00f90340c0e030349a01100e0403a150907203030342145000b0034403903000d03060302c100c40140e000c154402c802000000700048400050004030191030295a11424800c0c011141482 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 468591429 1250 468590179 468590183
    0x3050d0c140d0f0f06090905060f0907060806031002070c030c0e04110909010b03030a050a1107060e01051b120702030d090b0d0b0f09010b070515010b250215180607 72
    0x9061101011102c4182c000310700080c0c0e1200f00080241114600405440c1c094006c40940c64442c891101080000c105650303001241740d403a4403483c204008042e40b01d110b984180010003c07020045a41d5039070504c0740031809130305100215520b803003919040703901d9210391009032604013100000060060401c10b181e882258804402d46580354a14200580803501400c00145996290340245054070200f0040644110300d8841c15101c0a076010021b00e08c0000501d00744180d0080901045030070f400102c440c40d907a00c01d00340070f81c4031198240705c04620403030000012107500c0354084000448164000600899000742c00381c86505000103402d40b03100200d44030302801982c0411400740c901c04594045e100360f620040c001c200c0b04140c803001030b8a401d42038200c04000480080d0220422030104000c0c0d4140c1700001140883d50b2410081c0704040c064540580305108400c0d05008090144480c207038500713030f4010009405600c00e0340840100f07400c04801c01615011110300b142240c5400300035a0b845035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 468592679 1250 468591429 468591467
    0xe040203060604050c0d09060b1201060518180106090b1e030d2102122d0103021908010905060906011215020703021509010f0b1813110d03050d0c 64
    0xb45403081030000030040244010f80c00780051144019040c0c1340e01aa5920902030200803540380100780822481d1000c0000b402d045a150090400c001d444403070203400902d0b0060740603d041e540d0480072440301c02e000418a0030039407800c1d002054480d034543c41004082001e545520040300020300300c0541c00c100606196040d0300051090611a04c00d007142003214015803110364000050711030b80c40c26a00011083d1151903065410400c04944a0b80802c203144400c196059070000d180c0f000c0f580c1c40d030042c04040d000b406119102c4514540645102c401050844002c1081214a003085500c408040da0610558000c01000007842000004803a80540d0070441d507940b10a5183c10f150300079402140100e040d4001d09440c4144030f031203020014850481030001040100d03a04440c01700b01c610046076203200b02e01c181039109078400c050ba041e56000b00030074903600d1155098140f140207040c007a81142c1c1e005c0303070716040c4d401099030203070142c507030009050703003c0c032000581c170505030741080d40c107204a0020f03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 468593929 1250 468592679 468592681
    0x30312041208152e090302090702240603070315050703060503070609090e010b030f0f0d0216120311030319270807060e07150206100503100c0509120d090e04020306 72
    0x610f4031313400314941c1e03800048100c81820445024040c1d8200307010108801306517076040400950405043d555030140251001d00501000d140c0c8a010000d03c400090001c01ca114000401544003000402c002e55088840b602020300c0d48910600500012581480007030f0030325a00040b05d090029032032064032200d03164400301d1401d01100b4001807d14030100c480725074855000c01101d403418010010480d400d94081c0c5015030f80700c59440d203070841c001c04074821588103504c11390314024500c0108060f15084042694000f1050804940091010b400480c40b808000103100701c60749290010700000d50600d0b0103001ea510351950601d01620301c160010384903802c19004100246400b0001e01c0c00300d21a080028158203184c158500d09101d03030304104000c00d400f0110a50300c4c0c2d01048400c0d840381101e14841c0e540303410f100100380c0711921030b00c50381c00e500d40754502508000c0c00340e0306480605a010b40b4401041c2d540d08400342c1e642440303a0400c0082035180c0c030041b4181c41100000c500c00c680180c002c05e51 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 468595179 1250 468593929 468593971
    0x1c020f04021615091b080a150905060703020301050a080a020607020d05150a1e0513060c0504270e190b040309090c080f060616150b030312041208 64
    0x1030b500182c0c00c440c01d10524481c076070001d10800002100750703c070014005200f02e900d03d00390100252034840814074140100f006c10403501c000580012403940000748201c280c0c0034000e000050100150000e1440c011001080034842e40b540c003850413503a048440346000c40c3c0d1000b2090f160850004060b40080c02004800c2c00b601340226401002d074130450488050a5042441d1215a4020f507081107650740c5500c000200002a001a910480c10030300c01042241403510201280c1d0400400013002d040d2210740ca41003440c000e00940d070003049051400b04452007104140124031181d048010340315807400800c020742640000303007a81e5107402c0e10ac4c01c50601806881d00d0000c500010000c40c20046405c00101d01042d603805074102d95540d503154003501381000c094003a24504028045405140244414940322a481e814400666040000c0d002d0f4004145a940044c080312a4250f40610000580c2c0030b04610070021144075070300545909000c01c050bc042292005416508001140200c0500f011 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 468596429 1250 468595179 468595181
    0x90510080a020906040b0c01093f0306050a1d010b0c031e0f0a0c020411090f01050714030c06040b0108030f04060f03060f090e06130c03032105151c020f04 68
    0x2c00030f038010505420540e413a07500481a40c040e40b00741c58565118100780f000c20520800faa43e04450805041d0b5641803444040c408540c070704003e8050800b10340d410418828043d81c840300c094600540340d8601e907a2074902041201001c2e00c00e5440103501c60b8000240c1c5462030703041e156691803200c051454681380e054145200c05482c811003400c0c1c58200081319107104110024105081507840e0304849014130b004000c2115445c02182c841054200682481e0760f6400c0c000d0204501e09080c041e4070780c40b4074181211140810300c682c14071840b000501200d01c480010360184194400c0036a008940e03250344400e5100c2c081c2ca054500c265805000034011540205c640c038140c12854940001c4803a503410740300c0d01c02c06017907010b20702c3c0b44c7c1d4030035400c41d4045007840219400079082104403c0d4000542c4c5035040c00c1c2032480040c042110a0a5152841002480700021021f800f6014811410b02c1040700c00d40151840815119034081c3c0c0c8143c40494a0180c0d800c0c00c3d46c1c00810340181c84144006100c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 468597679 1250 468596429 468596437
    0x206030a0f060e090c090903030106121803081f050102030a110c03160510080f060609030f01020a0f0f020609150c090d05030a02010501050603011505070f0609030e01090510080a02 79
    0x185994450300380721001c0029108000003040c00380c0301106107082101d0118244240600803a018408507004c02150040002c201c80c1101c0591030a0407405403048559401004000800846400104145410302d5400510303903020309600d203200b200d1048540140803c9140e688034840c05a0002c1c81220b013030a0260581c0b80c828480013041e10205110100003e080114040d076200e800702c01e40704240001d0803c2118104202100d08000311141855034459800410007455035100b0300c00051000392a48041c0030301c0284550101c0290f40b86e24500350040e22179002d1800c15000204503841d10405e240c0b00140c014084d01903a00500b8007485074000b28000200010a001103800c000c20007840c05465080d991240c082c082c0028540381e1150751002800d4a106030300c5503210744014001401f012846c2c216040d4070b0b481c01d0414980c1d4000d41d00d40358658242290000d0700b071902c1d0034a090181034100c000100298001d036503000d1500e8a542c20070000b140f86420140000380c0300d01c005905219242e0082c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 468598929 1250 468597679 468597691
    0x90f031a0403050d1803030507020f0a1509170909100302100806010233130203030a0c020406090609150504020f120903070c0b0c07090c050702010e01030f0507030c0e060a0c020603 79
    0x7241c40c0c004100045000c0d1540140352548110308045c07070005240e810320459030845007500c0076004c2115840926a40c42c4071290002d02100414480c0025000c0343c1d6002c9001da6070300511030086000b82c40312000315600015a21401288014000b82ca09590083c07014240c0e42e0043c1a882034402d02e0208a5500301c0003420641035101e40402a034403900c6009a2034841095290501100c1c12501a6001f201c0c0c4041c11101c54030f0b07800e841c1800140d0780402035840310000c602d40f0003e444003038000034000c2c1c084c0d9031000d02c09a00e00040800d10100319005691f00c06003c40f44c8030781c1c240d900c2040c0b2003244601d09610401d00301c10702010889102c1c444100303802050040840c1e040c407219032540f60352418981e0012403e40000a84c40408078002e00221000301003c41080140c3d41d074002000d4240c2c419040001d04000300b503138500c425a07020354800e103c49802400204101e00c0c00c06005401011449040c02c0801d1140d9290b130700502c0c15204903201a400c5690700329049000ea4284038460300003400b5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 468600179 1250 468598929 468598937
    0x207060b090108030a02280b220c050117040309091a040510030506011a041401020f0703060c0314060f0d0f140714030109031409060d0912090f031a0403 67
    0x10803141030765100c030350707a01030451900a582c0c0c402000c04080d16001500044d030f00030003e0040b00b280c0050114851108650304180c0411039550b80964056074508000090f01a00140401c8042400b00e04001c4c00706855081e01d0302910000c0389158040c82d40c404981c0200042c034040001e10480c0ea154001e0700c021690414558024441c4100040c141c50080351041002e4462103020030500c40204001130041503011150050030148085030180d42c440d0b8002c019204032480c0c41a171031030b40b08001c2c7c0c01c081044c1c1e03000e0300c001c01c2d00c0e0300d00385000d080440d0201c8006802c1c076080d0000b8402c1174000d180500070051000102c00d40313143c240700700031107108010344600780b48110100100c0c6c03a03900c101c010608800042c004032030509070350100001c01561824000c1e0b2512600c0e100094000243c07203042010303001030700d445203851800287c2e80c0c0b040740303030049046041425690800c150007502242c04c0403144c98540803280c0350300384406840c0c550701c0084e1801c034590f9420780b030001c1c14000154000303020f440c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 468601429 1250 468600179 468600191
    0x30a0509030325020a0f060906150803030c2505010c140c03040e090316050a020114030c072406030602120c070302060c0d0204030602030c070b061c03110a05121c1806020706 76
    0x49211b03041d041c414080c0d40540e101c104250411503203104000c0030012038060704580301e041181665a0b808014070f05441d21303200048010032040e1000d110755441101c45107040d021041454403901a00d119800344011a81e0f6814400c1a0b0070500b081c0d482d68a00d0320010b50510b444d0110a0400d618094101c40c41404204480c0002c49847e94902c2100d80c0500014444000280300040807482100300d0081920410b1091041c81d03240b10040303842c010f03049184404402e0b500c0120104e02d40c0580d441e16040c9240180001c00c01910345c001e0544200500000b420076070303c48055104900c81c0140040050b00400e002440b45582c42014282040d02071200504042e144c4d600c0c14100c1e402a511800c5291000c41c1d00020020380c4440d03298855025650302d03076600d0050000341c0803c041c50200070240440540c0d0f01c0c2c516001049520b4560360801d0403100302e1240031110000e654400300c0c20500c400c45920400e11482c03128010180b81c0400c00040b98480f00d101d841e464025044514110b88550300c0e62 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 468602679 1250 468601429 468601433
    0xd1704051c110405010b03040f14190501050603070303140d020405310905030405130f020a03051008011a010e030c04090b060f150301050121060b030a0509030325020a 73
    0x411010303401a05405155901e002800c01c1c4090b0441403a00307901c902c0c1008018052080a90141ca410036413160354000301d1005482c04640c1038510b0701660310b861160400c0c51101d030a94107881b000090041008100c0b5450762000d1549440040c0400380209081c5004070303541c1c00c0007c000740340c0100c500c40014106900c1348009000280b1301d004601484440d1110321154071811120740028054145003005490215600d25499018900c42c4c80e200c0e0003c01090403a4803070942055241300101c01e02103540b0300051102038000d02041d14003220b1581000b901082d001c00511411041c07a0112010804c810f20342c0e00119020381035200c8840d01030140060011080c0c607540a024059842260500a10700e0100244885101c43d1003085100d1210240d820001455003011030b41518800c4ca0207808154040710315002000c1c1d00854a03141d00d140c80e80c0040d10003011009940203607c055000d2206072036000c109552408181d600300c80800560410f850b0048002844100020050040c1e962458441e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 468603929 1250 468602679 468602689
    0xf0913061a07080316140c01090b0a020304050a0303020d02070204020706090b090f0327120607020607020d0c0602090a08070b0306090604061508060a0902040602010e010c02060f04060509011104030303020a09050f0d170405 97
    0x172587e080c145c1d152000390040162070b1001c40d034492010303e8214150316060b20b529585848142e000b03420f040e070004041500f28a10f030111503402c0c0d0090401c3d5a14106490a50300900c1003150545180446d01c003c900e004501080c18199590350400542c2070001420910144c1e20b480e50038190313098000c9248803540d4507480c4e91100c4d02114800980010f01c6c201602a0428400805900440d00041214110a41c01020040f11603030071420042e01e8245101c0420011718040d04400c82e0741c03081140000d44041018003c600c1008182c0b11141d071610b5640500c02947d0f06401080400181d0200142075180f08506250b404030005184400c030a5a070348040049a100740c00850041c0d4403996140301c400024040c6514610b01d42c8001c14103460500d800c410035070700c082c0009102540b01c2011480d00760307094005074401050301110a80c0d55a80e4078000c0c00030b620000810020071551352000800b8640009002a4400041c04000d2031444c0c0782c0d540c1104082600071440d0a8005100c0071442c1c0d194 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 468605179 1250 468603929 468603937
    0x61d180c0307021b060406110721060c080f0f06010e121605030f0c060f04080607080106030f0605090703090201120908030615040501050f0f0913061a0708031614 71
    0x108088140d5079040c4580700034141940e00118203610a01c04d10200103946803034007100d048541529141e08c001c0d01e00c000003410022140d1290741c1154a09151141e40742c065000402c1441c032816081165015000041e07685000c00c032603d1144010203000a0840d4290300c0614bc0d100030140b4050292180d2072000031510001090041d0b150760010600203c02020301000c0809850218024140001410b6278642e036940c20f590f499010f44170108021540440b100c0558010307114120684240c0d162140f40108034034401d2003800700003030602528001140c072903c01c0900340c0b07101074020071440d92400c600798080c000c0740100b2410003d0030030a00080000b00d108031030f480c42c03040070140d03035030b041003401c11035034208001401c4407480041104004903a0400219601d0100103c0d50b561110860702c09040325004003407006801c91080280901e000c846941304d04252000f900d04800c140215012804040c01100d200130329411082001c15014200542040003045080ca801c8103241c1c0c03a1809500c046d00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 468606429 1250 468605179 468605191
    0xf07200d0c020d0b100617041e02031219083d0509010b07021002072306041d04120c0305180321070b01050d051911032a0901061d18 58
    0x80b4a1011b00100303a0007038100740c1034851449403a130a03080035118480f0818801c410403070040a445440411524240400700100100100700b80d12145c04421240e003014060b2a60b000080a00c00012101e54081101e030f01ca841d503c1004200e48000f401c2d45648001002d58901c406045c0310400080316550148024085c0010001181ccca8202c18814084400101e10000c0c0654110100c01c3c0826001100990f00d0951a1b5811441d181d006d000812002d125903000500d42c211610042803040c400760683c02d014a10a0a00c600280d00600c0110307220241554000c000a80411082803e811403900416442c000103064030001c0310f0032a0f140342c400c044445602c44607040411824148480b20700281d005020543c0c0c00003480a990f5622a100c6e5000d03200b00000201545400301031064480f080103203210044c0488042c1410001c07501c0420301e02c4031400d81100b501c0892143e450400150b524104c0f4142d4441401c0c85c03030900148001141ea040e40e0b660403005076880480c07003000201900b40940c1e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 468607679 1250 468606429 468606451
    0xb04020d0e0c180a0c0c020d0302010c020d0518040e0705060406020d09080d1b050a021e04060902090a030f0f05070b04030213091e05070e0f07200d0c020d0b 69
    0x1030300c05034919040030303507030089a84111101c90b01038261840040a65501200001c000140c484c00880d051b541c04e2200b0360041d4220003401c0041c4101601540485017200c05a02142c055044014044400d8401d4055848401c03c01c0f83c103c1042d41001d41218140100802c01c1e11180c603101c1020a1070740d04540d002c2001603010580079075549070451220006080028040c0811031040702d800350000d21039240c203091400030380e490b80701030220612a2100b51503009040f030729800c603003107501c480d11241c0b208200d20071132510b140052070031a1071084078a0341c603018040c00203152440d00d480410b01d203c4078080e900d201501700c8003800140c00b4082c02d400303004440c0b5401d07290340c11401401584041d54174480751007440d100d141c0021400d1a47c220701c800b0080c111034220b54140b490a5400d001c040e40c8540c51100d076010038050061108601940b1800c441d81d56000d10200d200014988031105898500140d040820700307028403880703507030710501040c0040c2a049400d80031f9641c190040004a441c0a480 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 468608929 1250 468607679 468607691
    0x1204030921020109050904060e0f0601170312040b0402130f051008030c07230603010801020a23031b04081603050d0f12091a090c100c0305071103010b04020d 69
    0x50a81c2030407009000c12941d030540c41a0300c09a0019085882034014103101e11000e400040c108080360b0003110100c0025002d40c1d80c11984105c82980e100000e00a81c0c0300341606c0c401040700c442d4004152241040c2d804001c000325151500e40c41e000500140090b44c11843da2854150f1040b81c034054880f081d066a10001803d1400c02c0b407180c82508190000325568100b00321180c0303c41d000080c52425100301d03815082350842650584442180e5650040341c1208000c0000500c004041d4040d041c0d950060320740380c5100103803034890030743e044851000500c0c808040c03003c100d80f50211913420070060158403c0c5803400b51900d07801890002c07900d503d200301c5009104184200103060000e140d00c15080c0c100b80b00070040428001d0f110b40580011000120355502c203410922860406904050302c070025100c140e8180004142c1d2550071508400d8002ca0090039800ba50601c10b0854520b155010380c0c0d800c1c01c0801665400702c1c00d440d0181d02c640c1c59900d42d0081d4006607140d01c0100040c0000070400255 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 468610179 1250 468608929 468608939
    0x60a0e060309070f0605072303271c080403030503091e0606010f0f0e1210050c07110108060904030e030c120708100e0a080d061e0305060f0405030d1112040309 70
    0x404c1226410540401c00c06000140004d0112020801c0200d007090b009a10050f03000300081c070f5800784032101c510380368840d82c2030f4800d4480610a444030b400291b421210100c502c11040702401007560008115072020001000840e00c2107001d103402100b62400d81e000300010411040e022100d0010603e070079001141840280d680003d1509004001410802c58060500c003001e040440301030040d038040d642004030000f00500038041c9082f4480b4407101005a8108003041c0d0b446c035003260004442403a003211000020750302a0f020340c0c0c881c00006140000303907035030340c0c3d0100d440042c0c2825a5400d4070488240075200e684407082080820224401401034914001e0800c2c544820348804030140ca00c1c0c42c884d00355204010911003203607038104104660700d00c1c5913000d060042c201307588030a503001c4007401c00d07022a820300850041107a000c6d05c220303103071600c0303540c040451880145c42c0101194010844000c8012990304080d40011080c2400342c1001d0703441c180300710140411107084001602c00282480 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 468611429 1250 468610179 468610199
    0xc1a0601030b0429041112010617040b13140a030f02010c090e061002030c0706050a09090216120201060b0d050f131a19140103030f0c020d02060a0e06030907 69
    0x219010040703d0038800c000c0b400d01511074582d541942e441a40c0c03034503500b9807250386441e00700404003200d0140c4c9554606a05061340c0c4400c0e001e00800c00003c014081010f610b40413682e94600607078000c1c080340306586030020143d05580810008440d40004410404403068051107011703030719402500c644880322200d0b078000382120000c44800050212101d41840034100d0700c00d8083d44000b003070380c2040b001d850410050385903000b02101446244606c1d513000c100994080054001c5003d140c40d000a55511074007083d06078014076101e000110038042c204000305007083d694900003055800009001a19884802c0f040c0e070000e030035400090f0f110410321071640003c90049a100c0851038900c4501c2c1c4907030b070b5001c040800d2400c41d05000059040411f1484984840404c0e044e43e01c2102040b0016004961415104003440700b43c0219100e800900712803030003500322600c002d038020182c01d410041036003000304640040303210408105080a0718182a01d07a90000c50003030564034000c207102d0f86030507610b01d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 468612679 1250 468611429 468611441
    0x21030d060f1d060d02030705100504090507051c0908091302130801050103031b170705060a1d030904051506040e09120702332101050d02010509010507030c1a060103 72
    0x100d11020140301da40701e0385060082e070b00e820980454940d03074002c14600000e031400d600da8100d60342c444180040c400c1c0d40d0790002c00810455000b00e109014a60b01c843c01540d19010350103408c1850403200305070b002c4100035503001e50304280c4103001c860b0900e45000c011440b000104000d00788034990000f0074484280140c20080c0040981100030302580d81035950050054951140381295104024134000803c05c6001d4140700000c0c0c004101c3e51126018281a6a00e01066079034010b8a0701c0c20320800310042c4481844900c1194481c002c47c5490074904c24400209001000c280702214803452f0740340341c2e90f0703200300030001404c04061403d400c0c20300300c2030b8905110464078215007800c0100507110041c1c443c903075402014814100074140c85882c83c03901243c0396041040304003d024002030180341000c81c04900d05440f03210715a400070b141ea03e400a0205e25041000040d01280341031200800c81c0d807240300144502c51003460880e980800361382e0340b1003050440a40b4140b0f0000110100402541e15210724 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 468613929 1250 468612679 468612689
    0x305070c0f06111213060815040911330703020f030c0120090a09020f1c021e0424120c020105151905040e030f04031b0b071121030d060f 60
    0xa030349017440b200f544100a500c2403040f0018071444c2c0b000035240b10350100c0f071454440c0004c0c2c41441034400515001c100b00800401c45032180e5414000b241745501018031541c81d070714101e09090400d41c910f8500103039039002804114114400c824411581c03100500c0a40010704a40001040c881c080707050b45121100720032103001045806200c00f07503180ea511680101160b5040d03d00507918040303d0300040c402c0c450031401102c100b2071b000501100120680c02002c19046042a4211b039030303000c440c1d03540544110b11858000e4001c1c41030000c403065203210302250b02010b070f0030070707510343c02892500c20159450a4134040240c0d648034100f003560f41c031081d0204800c15080b100018240c2d440780d110715010f00c0030300030310380600d0b0340d2054282080800c0084440c0705914100864036665649001c0086c403440100701d40d041d034070151002500d00e5404c02075a0b00302d58001e9804078482c00300702c1808079400c0751500000095041410420101d0300a00061070081000302e0042850341c2000c015410400d00c075849 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 468615179 1250 468613929 468613963
    0x3030804143c0712051e030304030c020f0616120516060b01020a0c080102030f0a02031303080a020405060d020403061a0a12020114040902090405151309080f1b0c0301090b040305070c0f0611 83
    0x6c08070300b183e0200071664440e604d4100340701142041c1c008101030b040034000d01d035048900020480b468103450303890000034074460b845024544501e070004881c64000d0f03003000d6840d41d240f070744c490001440c15048100b01540620442d101688192600203c00b01c8651108041c1d035400000c2c07041c1c0b0441160340b1640401000019440c5080c0114540d8109810140150811042002040f41507003903404484c010000184115114a5007400c124025807282c802211900d160020040c2e848110861120310400c000740021780e43d600d0010103120303401401e40103c0c1040107101a01d1441c0302180c0281000c2d282c1500c00613184c0450b4001e0000b180c50103410100c18020007c4100b989544403864507420b030403548004180383d07544d850700c0c0c9000d02440503408030705a40462400300321100c0d2a14186801f6801080f909a00ea8040c00d1508803605290054540c5c0035032400140801e004034010503510b8031801c4801760300b69072041e0b020540d64075a04543d0019103003442500c055441006044150458546 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 468616429 1250 468615179 468615223
    0xe15040308070e3709022113080313050c030d05030103020f010c0203030a030c030603020d14070b09030304050603071b060c020d050f121008010603030804143c071205 73
    0x1280300d42e0410703200142005a0003004860030b05001c1c1024400410b0040003e41d01d885244100e412400f03841e0740001002d01f030400c0001d2240303070060600201ca603089041180b131f5881c4d98102d901580c69011003a64940710b040180c0c0642c1d1000c0041820b086451b0355040d449505520400040c0070b08212590304128040601402503900801241d010a0f1a41800164401e43d90003d0340948200d030302c040d504c00400301c040c00a002807019403040e103070f1310030081e1001d0985889051100c0d009a259050f0507920a010901050820000458010303803141850240400360a0356052800b07101c5c04101e0708191039007000000309030100700e21075403074046041041c2401e000c0354043c0d005000f500100c21448641da00401c0e0721700700f031a6202e406001c800c0020703c0001c2d202e0034080d080f50710642d030460f81071304803162a003500b11000c244881c0c164140c0350b01090303000e000380c4038141d40200801410050900c244010007200400c108220040c4290721204a4503019420540d0801014156904001c90004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 468617679 1250 468616429 468616459
    0xc1502010c1e020a0b10080c120d0507080d020313050705061c0b1807050c100908031614070f020418030212070804090f0b210a03030e15040308070e 65
    0x20000058120782000e030078218182e004a1610b0002180a400f00404c00240480c2426081440c0c0a40744030000719a540852101407203108068841d06000503080017009401d2070b4030580091000ca801008224182030f004d0198000b00d80c020350b117580e482d40c4080500f1080040c1402441e004143c1107420504011030741203590405170f964074100403c59640d072200d144a503900d0f1038030460792041e02e00c81d044038542100050010b50041c0044140b0740b142d101c0d00c0c18514200c0c0510601c1503444a422415916800d52110549401c034440d0818402c0c403c0483d0381d41c7c40b03141c000d40b05060164040115029aa00520084a08622176030720410402204400466000148881503510388080d2550380c201a0030206420300654100b5140b00b41004501001445203070408402508202c9006a866042103010000e01198461040d5541c1060803001c002c24042d90206000d9409142940d0031614800151074008000f11021030103d40944280041654005243d600180081e01d041003032001c41 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 468618929 1250 468617679 468617687
    0x70e030114150409050f0607020a1407180f110c010c170108030403150219031b0903051b0307050607060510090504081e07060e030405041515050a090e040c1502010c 72
    0x1c01c44090140d81c07501814000c0210412030041c4140146c0141d03080e6040c2004025207620361180c050700e80900c44404081c102074040b130260304031345143d014088812800003004014001010005212507969881008040e031aa40204594001c1000008006404941c050202c1d460558100300e030117400c200602c915400001282d0070f89412094901310701141c0c1c03003807001038450840d219030941401e0159006039905a00480c0d03490200401c2d12066070b500c4078045427030b1051844050f02c3c80e8848203408a0304014445807003004c6101400755848581c40744007086140c3e0044030121010780d560b50401100c080c003040300341c006e00f000760410310844c10640c030354412600401e200d142e00d00e0b41c1800f49500c468210000c9602d0254044002d10400007240100c03501ca4105215850003030381041000005120342c020307590203a8080c100366181d1108179030811500707600500c1423101070240b81e00c80410728525202c8003602c6075200d41d0b10301e2105410244c4c5000c1261922185009581c1031407505600283c01c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 468620179 1250 468618929 468618961
    0x40306020f04090e010507140909010302190317040609080f0607080a020d05090c0f0a030b130c030b0a0509010c05040608070806040b0418050705031f23070e030114 72
    0x900241e240c1100e503900000d103129a40c032801c0d00c0307450b11006440c841010340015100f100070341c540365440320803c44000035520880d8440766010704441c1c011300040c84c126002400c40c440300442680d000d5240da0340d0500924880e0742400c3e403500086420001243e01c0030580d400f50600b4400340211400e584019595480080d284c10709010f9600001200851294165026542d0072041440541807854029848540c40f41020380100800740404046040015412085030391107040c110f120b5a82040b0315442d101084c604607201001c5410000202c0d004582441c055018030900041e282413401038282101c14200035a010302000303000810489412203030643d842405030401c40ca6a54410300058001c18201c1d00040c1d00903e0103820355042d00c4002c0440030041d108104941c0c509407542d00b01a90f41103865040424101c2c800d41d0560700c01815000180700060000a0301c0158046000080749940c0031108a40000d05904c54000c4074602409401c407918408088030000741003200301c201d00010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 468621429 1250 468620179 468620183
    0xa0605040b0a1812050106051f050313050a0c0f060f0e060307110d0c021e030604170c1e01051623070503070c051203030f43140702060403 61
    0x14041030032811640260150b68869285518600b00141c48064a4644602407802902c0c21b40c6072280c0800c03e8105901174560400002d80c2c914120850850110703844d60005040b8061000782142101c00100d040041d80400d62040e01440e1a0781c0c20002e12510001d2181c0c041420005040150142e50350040b00c840d61aa2f1f00f40c031800e075244c1d00c00c0403d540200720a01644101d100f5000e1042078a9481600304560502c2258070100c50110452400040b12100c12070035419000707140468005400414415280034401c10141d05110300d8005071800d065481c14200320345841c2003000c09049000b03214144d40318240c4284004e4803501e50500401d1000701100c40d800d480440c40441e05c4480c03404050704c8031254420102c035685c09161801e01c051400c0c0380b00c2d960090707178440b85001c200b05005c0140e030321800708120504d180381c0c0c680307580210820060300c81c0c1600d40641c042c3c9000300c0651709102104810403120031382c500e0b825040002c0069007044001c440d1190103120030300040c0c1d03401d02110102e035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 468622679 1250 468621429 468621449
    0xa0f030504110d1e050303071824090b0c0304091d120306041509020703090b0307022107151413050c190b030412170f0604090c05031009050c0a060504 66
    0xa281032a00e00f00c044548001143c400c81d41c601c1386010007400000452241e001031351050200d104020744960001418083e20013914920754900230340c02581070441d105110546000954a507941810740c10503400512232000f95000014180106c1e92a40518170402c0341c2441c094200003406000c8945400070f207000301c48800800004503401e5a5290099059428100e0410030f1442c1d440000304001e51004400300e011806d0f03141c0000d0301c0d25040c1c05480c1b0602498014020700d001d410100c0c98400180c0000082c09181440740f68080385084c800c29402002440300020080b10351726800c4c2c2c1c603c0004204081c42103020b100100064800300302c0d0082240c0c10f41d400400d0b1100720041d20f81c07000b0300e5003109507203150100130081030045d1070100401395030298545200340e00c0a42c07040c218200707080f2880b000d821044e00104900c2d05096004048040c015503402c81090f45500002e4280744240320380c209103503182c01a00c41488400e10040782c1c0c0040880e03c646c0241d2074504080c226000d01d11a02000c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 468623929 1250 468622679 468622699
    0x70201020d0809030d2d1d01200c010f020c010207020a08070513180b0403020619060e04020d050a08030703090507090506010c021908030a030c0206070206010308090d0213020304080a0f03050411 85
    0xb800d07043e4014201200c409030702d107001103040c80c2090007804a02160103640416544d800c0c0442010721880014000304118449e14400d40c004184140d03201d101245204d40d42c5900000206000d48041c0c105001c0700300002d41d80c0c03070481c0104500c414594121283d00e80201000f04040d43e00c1104a240602c040380010412110466040340144c42c1c196014081d00e207024100300c00c0684c04260b040c85160460b000d1183c0314100c0f100441182e045005e8401e440280e0350100f809880c0040285006038480d00403074400300c0c201e40d25144290015545c0700c4c0440c0d1640001c40030040c003449a0000b804001c0001c0016251040009040708005c0034040d004007001e40b00d2015520340f969441000d00045400c82e035842d001840003e0091512800c42c000500a40011581079032012421034102c0350089052400c01c14130b002040300002489500b280e01800c4042c40e140903444c01d0029500c940e004078001c03038a420420001800707000c08141c1d41010580b40004200000706000440d5507012001c3e41e087c110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 468625179 1250 468623929 468623951
    0x1050f010e040207120807051201120819110d080603100b060f04030b0601080a0b010e0603181b010e0a030c0b160203030d0507111f0f02160305070201020d0809030d 72
    0x41c0000c006031481c0c00a000207101c030107114880088501d214056030700d1132096565510202e446008011403139a001c2c8041c3e0040000da0941c0c600c5180c01400741019178030780800d401e0300300d002540e10800ba0000c10b1101e018104c4e40070052000310049010b0341040801032521000107501c1d00c2c28903860524003030b525844407100703849480668004010b00d01100d99140e03201d007442d420044045905500040034a40010030751034490145115007081a115118034944000400ca85504024a0710500d020700c40502c280c01c02c810420f802818446500c294114100075000401000003030000c2d034040c8044000800000d035003c0517180460300050003182c1c4030700c50380030030364140191668065858400404c042c60040030503406a8000c020703a48400300f85660b20440241c40c1e80d450019081c034601c10080042d692081504141261000c2d01001450b0480180c2d03030001c0c40e58110340603400100d000c1002e400710350b010004903c0c81651030400842c5071134254241c40d9a840b1b005110010345231a2449208 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 468626429 1250 468625179 468625187
    0x2121e0901141306140c07020f0a0e0a09212706140d0f020f030a05090f1e07030212061503060105061c09061b0201050c07020105030601082203030204060e030f030301050f01 76
    0xc1c654000e0303117400d8a00c0c100020740720040d8100070800d9115080042050b5100d01e030020001c0e04684000c40300d50541da0750755000d04c0090010910035580d100b4540c1c14004c407511000c540300e03816103440d16070b952000c4081c4070381180030800c022160707410301602806101251700720350004a00c0e00c00248440d6603103c10302625000e41880c1c140341d01742900124a444000c4c1d91000a1440b411501d0b008100c1a0b98149049a9401007650484095001501004690346d01c0a18041c1d84040c4401240c600c103a40383d01199202c805092a480c007a003000043c01140790420040342408a000c5004041c2075040c000085c1661040e01560b051801e040e440060b40c4e9144c07030300802408c58010100300945a41d0042070040c0c9601c0001200c019440c140004a0003080c01c1c050740d27815501a550b1a085580b154019550034802402c2548401780110440803a1b00c0c001c0070a10426109613030160320f0b40c0c80e026000d071040110315001740c840c0d0000214071701c80400000a07281100e0048400e00d0101d002c00005035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 468627679 1250 468626429 468626441
    0xc07030c0b0c0708040b04170d0905041a12030a08100501050313150609060609060c080d0e0304090c09060e01021c212f12010605030a02121e0901141306 67
    0x240341e203034085000503003248410040d00880d0340305503401c8c1c0c150300c281ca00d0540320402c450a50020640e403030028406803d0551100b200d2002e40b61080094008040000d4042d804140034131905600006401802650140c00650004091040060401e08020007e07015010041c601565280000304160610080d0a0240303078040c07000000300710a0380c4410070780c0040d0015000b65000b059846200240c914801c1458500c50303078010100c1800d10900072000740141442922141c0c01d44400d000c0441c54116510407450313040043e841e00040e85290040c0504500020840d00307055401550700c100c01401c1d1030480c0055944a4600341407024001c200100d00c01e5080c2d5441c000c1c0342d2614104903000c44680c014082c09254041c0c08a0406403801d2914100703104008141e5100026400100301c40381c0140040c6405c940201c3d00503051136070008101e818800102e900041040d070405400c0c14102c08481241e0300504003200a100c0306880b1102a1809003015109200c503903400d000c50010700c90366504c41c07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 468628929 1250 468627679 468627683
    0x31202041707091109030a06090204021306051905090904140f160305011113090c1b1a220f300305150a0902090d05010501090906050c07030c0b0c07 65
    0x50400c55080c949107564803090f01584000030f2814580c3e0303000b0b0b181802500e8005400800900159030983c2e101d1010706002c0340100d802070740900015511445082d5881e02401d100e40e20f85807540784554802c414002103003070b85c5042c0300d000c01c00d0030069161212035907030058000c124507a042c0000b0a00524120804009000b40d0264805050000e0108030a40c0101c1c4e000d203000b848004055408415584110040130038044460fa07000c01c521551500411507102c01414166105d01e0a00c0f499040308000c1501292020580312014000d1500018881d82201d0440a4035102c155111101000903a1a203000390100ca115600390041014002900b543c00c07801000071100d021080410084035082c960388880824103200004a16105214040c8020440103044000c07803480c00c0f000c040254003c042107600100d49501c03031750100d4000d0007031074001d0070481000a00420641801000c445001d003da0f103a0f044108203020100e544031520b5442160807000d0400c05490300120341009114000e00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 468630179 1250 468628929 468628949
    0x302131505091f0801060c050f060403051207181e050310090317090601061409030a05160f351005190c090b2d040f05180403120204 58
    0x191031036107940900544070382c4105030750b6980a40d042480501855119400d0400001c0d0345000420225202e0b1001e02d0700e15000d903007030341c680c9a0714200c0b003414100101c5007900821800141c04c6000b00415222550040c0c40d440e01542e481d00308510202415600d11824640f80303464880060100e03040c190b94002000000c080316596811103000e00301a011002040c0e0129189925405800040c00b0009102c0c0d0f511801600c6140e0074400c0c1036616210142c0d624818541c1480201166103017000442c2d2824000c0f030040a00c200341206c901e038130840b0340d001200e80c0000700c40d041000b207803018900050950341c0d400102c4000e10404e00200c1d40540c0f034010708054400c0c00004203110060703501090065480c81c044080034041d84802c0416969000344e01130010301c501c50200143d220b2500500f11541e10101451003076800c40071a8008001d00c1540c0718002480050100300011042c01c0c400010401503466140d0380e40c01900032466090014409000d01c50381101e0b400c138850720351341154003510b40084 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 468631429 1250 468630179 468630209
    0x906020c091b0d0f091e03081f030206121f06050403020d0203031e0702011706010c061a10030506040e071212051306020a050d09051507021206011e051f030213 70
    0xf1114000d0f0980300000c2d60881c030f541504845d0780c144101091551601078030303501c0e0345450340041027031003405480000743c028a0702180400103035140b00051829025110790300246081c00d42800c100030002c0030310703080c801c001761604008198100c020388040b2501124080010052230020a04600c1164800c109a0030762190301c0d5801014040541421030007a80d50308032844611000d6000e9031415103000d80030541140c8900c000803215004509124155071040c40140d1590300403404000c017000780000483e0b2280200700076410248036a544034060180180001e5107080100c458079210001d0240c00381e11700c1e0b984d4295481c0903c084448160103c4051900e007603807610300070b444501c403601c01c50f9580210302c1000e66481c4161040c2064034002450340c0031400982c026410700350f02901d003c03604540500c035440003540d800c0c48074500811034045101e100180d6880742140f203000a8000702d20071b481c10900000038060180c6000800c03903290400603a42c100c80103140204a0f000c0d4880035024a103e5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 468632679 1250 468631429 468631451
    0xa080c011b0f0206090102070f0b0642030408040e070207030c030c031a0c03071116030317070206100501080403050c100c120e030906070201050d060e04030906020c091b0d 75
    0x5500000c29510741d01381c880680f5030341704039801e0b4070401501030079414038004008041010184101c6c0c1000c401000d4010414020480c12003035184c10134440501040e040604095005520100f210011031100562851800781c2d00c1ca8594003e41c003907110840307000c80024400c580200502409075420208584001d0340e28a00881104c0007070004490207006880c00710206400444440d0003014001c1f10141196268041100d500c498031407a40c03501d1180b03503e040702c2c886122408d80e000d180203a0b160404030f22548241c2808a0000c1c6c40d03003085601880401c92140c42920851041c0ca1091a0402250321981400c0303c540c052800c660301c150244041003218140f0b640e00c40400502180c94140c1e40f00e10218125040310088000c0034501d8104128031056440c00000030301040b4814140b0302e042001800c50710b01160b48c190840c116074039150080c8801d00d81c0200140c07000740103502c0100036405146001c154441030141050018100c502d01002200219400303640090503044003c02c00c5200c96 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 468633929 1250 468632679 468632687
    0x8030c06040611091008060a0e0f0603010e0610121103010212070e0109060206010302060d0e06010311130203070e010c051014010f141e061308030a080105040e0a080c011b 75
    0x950742200c00303501c0c140c0350780c850300e403000c0030303903101c8100200a80207042c1218400d683c142e000501480c4c0c0400c4940000c288100c0300144540140c02015880c8000d06d001000e03d421116041240c0200b6031200c01004804652051020199200020340da0100105458071028108042201d15419400800c9164141da54407113040d20500641e607601c400780c1c1a4000640d100340040c000c000041e0001d000600140c20614000c1c48d10703824882c000150119206001e5007041d80c01c1e0403c5403060295040d41d40030345044c4c0041d4554100c00c210451450800b01e80103841011039205813418028040318800510074140044a203145820300d041c0a00101c040440c0d152260900801c5901c004111020840c1d40c1190780c200c00c2340c9806000095655200c0e529404074a0400c8459680048200001641100402c40850040200702c00540e25466021809068040c05030000303400f8902e090140d0001c01c400180c0d15460f940c210113915520707862091424058103002d40c2e000c00c9010b48940900c0e1440d80 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 468635179 1250 468633929 468633931
    0xc080d0c051c09020906010519080c0d020f0711090c0d0f0b060a0e15340f0803060420181906020a0516050f0f0415030c080f01110304120908030c06 65
    0x1017103e0120311951800010b6580d0701540e21050140b00304403000b07050660241300b4503a08010400f000b58100000c0104a9060784d120740c806031200030020031b2200401042d06400b00c00c10307000700d840c4241031402d400e070b160081c0550a2918030707164803020071401c56802540113198501018154560381c030342900b00941030403040e06165008240001201c84411aa0002c1c1c500e60400364003c2c401012082c180c1c0c0004441550030507405900201a03100081d00588443d000c8034416480d158980c0707400c200300320488456040186040c0c4903500203406c40d0710840c3c03c48003034151441080b1922455880440c80c030102107444403100901d000d4001c01c4c115000103060400030321440c116603110b60542080600c0d125240b05e2607801265881c0f5500d85440c10145a101024015000242d03030341001600041c1d00718554800d50b26501c22203003c0c05560400d10103100c00d40e440400901036400c00e4030807030a00b4400140b01410501c0508868620b45100d0192000105101822291100603140794591141c2e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 468636429 1250 468635179 468635183
    0xa0b0403170c04180902060406031d060a0c0801080a02092716030209071106010b0d0f02031305070b09030a080306040b030703051605040e030d0f0e100e0c010c080d0c051c09 76
    0x20b9a96041d611244ca580281126180d02610440c10a440d281c030650103464540f03080b501d15454010f000d44041001c0003446c1c49031503c00c00c0071440c50351b101c00207029040d040e041b20f01c054101d282d82c0400360311505080380c0c00c46030001441e4070401c01200112032002680700340300c600d401502c0d90f5034409412a111038050368000c840e91324680c0c4550400f039415981e403002d2100c03a504510010046102141c0c05400c880f0b445003408506000100c6c690003c07a4411140300340d6003006540d2400a00900300501005440c4404505182c240d203840007a0f51900035950040c0311400001c00152951584e4000d1800214040c003118500ca46034038026813121040080358a1744060070000050074906806150300c2c084071503001c1e5180403135910361500079108080e502140541c4842080f10603d2042208156509920f00c00060040911700e0040c20004000c1c2101d0400800903c000081010b0303074111020300c0586c110015068070751041c1500e0502610540e03418000b40f410292034000c4058218200c03141c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 468637679 1250 468636429 468636449
    0x30f0109050109150b0d060b010c14010e0d091805090a0b04150f0506010503060906120d0c05070e06300a0b1e0417220617010f03050a0b0403170c04 65
    0x1c1004542e440032a40e651040740e910018040100c004600c848c3c0c0546408074040c9010b007621041501c445112003150000043c207a90744100c1182e0140c81484120465a014502500c2d2a0b02e8040c00000f0003c2d0032100040c60341c0d503038010800c403843c100880700c86146c0c40100c250151034141844030441d080c5e00b01402c8940e0800c1c05c0c0701080402c46c4111485020161542c90440e2580028040c41010051690f0b40000d02002110040003041246081024141c2d44160381c0040c10318040e803c015055100250007070b410f009000b81fa5860400c1c84000210602d002d00041c81e000441e090345005100c60307460700b801005100000d2000c81c1440520403044071400b40420602400c81d02640c840c2210f01034220180410601024028000242061384c10152070201c0152440011580350865a000e140464580c0b02c06040c03003a89030601d240140b80400c1680ca10600d92384920343c840c00030742c070000c2040880e640040d0070107000c1c812007e6026581c580500043c80c243c2c1c0304005560103030043d10200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 468638929 1250 468637679 468637703
    0x504080601080c100c1104050f01090c080103020904020108070212031603060e0609060103020309070314010c03140f132f1c080f0c0c1203030609010b0702011706030f0109050109 78
    0x40c00b40021194003414000e00702030036100340c80004845248210354100c403c8045a1b00400300c3e40c0e50380c01464020040c0b0044802d20b94500740c2d12404a034000c058400c1032004e0f6800410259640d4614107074401d4080c206040d00b6a140001242480812100100303840d82c04002d01010b580d00100085d80745806403810000143c54402c13495200904a1b000c80e4000c203420b0000d002940f007034024540000c0d000003103074007880c0c80e552444014503803040e405410341c0d5141015417a103a414094100c3c402032056501a560030004c10740510303144020101d20b8003411620a00040255200d02d0011040c80016040c0c4115003001c58a0785a007a18102030740b044210301c4040b1070012241403d0031003142d1000080749011070100d91040d03103400600283c0e443e4080e40039034000503165581602c450305246c001035662482c0c61030411440c084103806c0521303550420b006080050341c22801900100c2ca024894403202d564000c006841c0c0a10029a01015420708941808000701500581c0740c80d44200240703091 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 468640179 1250 468638929 468638939
    0xd2417060a0203041e02030c0303041823040f080d0606021e01060807030311030403020918060a092003010b0310090308010b0a200106030f0c170c0307051509030105070504080601 78
    0xba03020644d80a4008a4021210ba04102c240301c215031020348040d090f920300000740c00c006400e641141e444201d000700280c1000c040002144241400c42c9121000c144106007040d403c403000c070200400c010304040801c20000c0901010701d044e501b0b4403504035400d120840e110440252159404000782549980101240c501850180120f400b500c8108000f00b898502e03544046400491078288020103000400c4044056150480356501c250b490049095904010130b0340185441c5000788011111860103d0100c002a50389500c2c041200392058201c81c50040c140000c2d0061200940c1070f035151144401c10003804003203420101c1554041d489501e6143c1e40c404000c03d0902c40d071441c820000b14140c07046800701c4180c52410f441c05010f0700000880d07544965910b02d20340e103c42025900110040810004c2508004e1445d458a0070132024010381e00d024400309503110b54a0040b18802c00100ca00000300c050fa14003a80c1002c000240240700d54200324001804681c0240600380c0d60f4040d031000415 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 468641429 1250 468640179 468640181
    0x503041e03050c01050601021c0e180f010501020d030b030606012f0c13050903070b07020f030708090a120c0b0d0b060d050f0f0420061606060612060b0d2417060a 71
    0xc04190349c05e0303e0200c108042d045404950b40d44400750300002c108203030050b0040c5c480002c0e02c5101101810313510381d41400e00285c90403ca03151008100f60a02208807001e0302e010030700f039401840c2800c0c04c034480080c20b1600c000c0c00d000346441e03855420107182d600004220008480c05049000c2d1807039580c0a49c102a26815a10308403084d0301203901c10440f41d4006003026007003a034410101c0c8180e44001034005105403d42e840002d0540b8004c5000c00c208499144c00091000140300322131981d110150a65920070000d0714a2060f01d101c4500403c01840344010340d040003c02400043c900da64444540c4900c0300241020784c3c020f080d6031540350001e0b104140240d0340c5805a07810a00050000040001101c900454040841d0700a40280a0740c4140c081103401003410611480c004182d40b401d02c0d0009000c51035035088440414141002040460101c1c01107918a090018001c13a46034121500b080440c8010b8081112044070b075540001e10100d0b00c004007403d4a01d05c010780d0065245c40f52042c1c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 468642679 1250 468641429 468641443
    0x6050115020303040206030705120c040e280b0f0a2d061b051606050703080a051b18190e0a09030e040c0207030b100503010f0204150503041e03050c0105060102 70
    0x32015030b008102181c094034129001e964000300134689949094030b200303403147c40c00d03005a52210041c2d101141c10301100a036000030f150700a61034031004101d0f0743c00043c0d050044840400d18050aa942d0070403030141d80351100e41c0e03264104044c110a01030303607503824003004200c10412090380c03d42c2e0002100101b0f01d21454201c1c100d840319500d135601144004d0032000e5020011000b1645c41c418120110000c0c0040c440a00c000c142070345a031510380c0030030704016040c3c072030041146c6001e5280004102c01d0503829002c281240c0703015007500d91248a10a01e00b0381c00d00d1b0711b00f4195444030403000d506890381c201d5040c1c00c0596070010542c180030303101d0302f030041c0c191041c0d0b10780200451174080e1a03810780d003069130040110401920498505907900c1d190707404680410b0340d466580600200083c082801c003401090b1109007000c0e8110b1900d03140100d05400000c0340d2024000b002400408034040c0851100e840c059580c040c0c0042d05081400d21300580710790300c0403407401c03101e5003004000b486c0c44d070000c1005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 468643929 1250 468642679 468642719
    0x9080c030d05271c03020d0f0f0507060b03010501080c0a0b090a15121113050f090109150b0a08010e0a1b0e03100f09021206010f060e151303060501 65
    0x201d0308080003202a00c403c42507281e050580700c6080b141001040d0f89404001e401c50b10303070315034614000240b420001d061a603445048414480d9085200258070350011070000301301c90031b00d0450b880d071010f86040b1001d8561003e00d954550b00700000071a00007808503404e044101d00b21851855a07070b44280780356140c0107030301006900c01c1005508000080204100300c61022462515414040c2c82c250854201c44042107030303140d450b00110340301d20890140f0580304060301007102c844030b0800384e00b80095001c041c140151325100d619281d030640c4940740c2c40602c402408002c80120b4813002c040000814542003407041501a004490201c2ea0002031807040e00440803038007014000d400e40601d0250b9501007164070300e079014464078641c40040341740d601c00c230070301c800b880d09010420034003600411900b1f4040010846c2241c000c6c10040010180c074078a60011031b0718505000c080150b0700d00c00140c8a820300700b030401c054080054005852400204030405480c40750074108490398072580d030800039030341c81c000c2c0e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 468645179 1250 468643929 468643937
    0x1204060315080d0e0a1d0103051204050303030408090a03050f0312070e030a060e1905060901060504020306030601031b0902030106210c1d130c0f14070b0606071502040609080c030d 79
    0x180c010413803103a0311440001e10050b1001c110903584100440c10781217800710350321003d0841c10050041010510000c88040c070b46480207820181000006a168400500004c1180b42c001400094940303401101d0b030700454018042c2e91901100000c41900c81e03210030b43c410383c0701c00c0000c001a40075004100044406401034010010070500d40d84e00b400600d644941017500740325903004000740d69100340c5003100f0340d4812009050541400d007a940c0c03d449194001c0e6200e980103000f002403607100050b0a41c112030f08285042001d00d4420034210369200b5541200c1c920900000020070748580003000c1c844140001702198070407145215030881264410308966001441e50040d080150b151050341d1034210310018000e00e81d41c40180c103810102e55102801038081400d00d80441d50281c0c10003c541540788444032030310725140071543c45220074080100402d101c0e4001091307800912005e28408000c0e1070507190f0441d0f42d0798171a41c003e03000c2d0f20944160291841000c0b551000303424040340c28000760401e616 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 468646429 1250 468645179 468645193
    0x20c0102210a031e0f06050d0308040b07090e04080a020f0d1d031614090c130e0702010b030601060e120109080409020c0a080d0204090b1207140a0305120406031508 72
    0xd08a59250701071142c840805440d8005881c021891805925410580120002d900350000c82c401040d1100c1c0d910152160380200c61340404640c1022407141d20a602c0a903000d007554610400b41c4e51007829170410440c0c20300360800c00041140e01d000903c10f2660680884583c00c83c0701301d00b140e4071083c2098907400680c289d440046824002c01200c84070000c0241035030020b440701c0c41d4140e00000346600880301c41c5552881090702c0c1c201903401c40c1c2c00c503000c00e0b580c925001d000d410644103040580300746400d503501c80000030050b91003980040e00c1078100609541607969100703c020107508409260710300c50541030b000b16843ca081489240619940600e940342094907080442c40290489203011a242c001d0182400014400d80000e0201c00307020b01c00103880301d0816100340100c44041e9080b5004002c0c0b010304010350000007550744c080b01e034404030180f0f0200c5803e0100740413900d203600007001c1e4031031440380360006107202001d803055415580e000c001c071440100030580c01086138842c503031030303038000007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 468647679 1250 468646429 468646483
    0x11061911092206031e0c050102070f05010f03090b130c0b07110907021921090305060a0b0406170715020c010815010323041211030904020c0c030304080d020c0102 71
    0x15200d00c1ca88400c202c0041c6140c0d59464581c4004020000c10300c41581d0b5170250020030402018900140c070b402c0c030042901c01d0030424460b42505070307405500c1c140501040c403005410320940210504650007110581c01e07050a0340d0358003040d540d0442c1216a400500c0001c02c0c1d4400d0034007034901858105011118081e11003040c011004405000401103020720300c0f20184080c507101c04c0c04075140c031030000950b290004540d6211a01458000c070001c22100702d6042000c0b840000d120fa410244c150f200143c01d0340c82600140050900754442d0900492a070050f006446000c111a0100e6000340d0b2098084223000500703d03152101c88007110301041c100008039140b140d002902000844041c140011448250500361147c060800250f0b400519500704200411110b410702440c403007a903041c003001c00813810140c191240114195a4040c0b030340441d102810840401448000d04406006e0704e130741c1c0da02e4110080c1c550b0001c00952001d4424184481d24a510019864003040244070b01c00d00721841c19 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 468648929 1250 468647679 468647719
    0x50607230f070501050403050703080615030c221508010b0903060403052212030f02060405121c0501060804170f030402010509030123060a08060f070e011106191109 72
    0xc0c400918400c9814000c010000f042440b446026500a0f1101e81c0c83d20418580100301e40c1e0b0050040b405100e0340d6070440d5820321400c0c162a00b02031202a842c3d212500440c000500c04e11540203943c5000c00c0070000200f800701420101c42640c2e080d03072600c01503031701d40010004510601c070841d501540a000083c012a11660103008100302c000d0741c03001c3d03070300c01801c8043c01c070301c0290010710b4041d1178250072104043d0050420ba043c454640050061803605489554954061040350706980340000780080041100744c44a0107180540f800030461944c461000614140c0122002c0300d822840302012103c0c51080ca0544542c00c4400e2070503840d6564941c0115800c0c0c0181c04040e8243d92517004100360180c46140d800390300c200480001d100ca16040040100445040d0700c1010030f40c03c000d00340800d003061481c0d0258040103c0c1804881081001c0c01240c1c250003d049900d0036021303420600c4056040c4905601036002020428865030a02403000c00306031107840d46817940115070310750180d00d038545 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 468650179 1250 468648929 468648937
    0xf030316080418020405090106020f0a2604140405010b0721050f03070804021e1f02070f1e06052703030d09050c040f060e07031a061605060723 63
    0x1c114010760806681d1904540d0356a1250a40040c5030703000b00c0c0c14003a0b4280032101c40d0050a040c8003d00401005001d03040d11807a00305009007034100040c104160f004018244104548400b0101c195110b50701d003100500100d41448003032086091200000c0d914801e0300584070030070b41040a1134801515001c038a01c0440b0510254000d125085c490705541c0101c4101446c072481841d100ca007010315103441001603d80c81c00080440481d00c00d4480740d01c944031030241000100c405600c0503119106c00c034050b454440e00d54805003220f0700c000804660700c1b10910304001519040c8604021143c1c40340419113040c09044410a10342c5040074031502c116004041c1020f20703001c0a81a285062685400101a215082006e5440e03502040610889090900c43c0c03982c0c0e803c40704000c019171030401e2101c3c5149034010b84410201501c61120a84105961144a02e04440205206d03540d030b05456511000346d0354020140d815014000c0080d0500d0700526201c5500c42d240d191002061141c000c86480c5908 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 468651429 1250 468650179 468650183
    0x503010e09011512050d03060f0b07060902121e03040303050a081f0b09120303222d02010f02010c0504060c0c0302060a0306081e060708060103141f050f030316 70
    0x24a406040d43e5090704032a0602c050030a9401c01401e20341035081c0180340c186e5000c2c4100405280103000c1080c0c2500c0107030041a00c7c407050300607507a4040c0d4104980078200600b4084d41c8100340c5c44c3c0a05010100080705580d801c000302c0c0503680e21485001c40c5882c0e011b984800b6010401c1002004d0a41c1d100b00b11842e40000801c21007400c41c5050020260307691081c0d042038025080008481c00c00745014601c00701c04e40705e2403000314650302c1c3c507000c4054203c005030800042e81e410400204108a400369108800220f80004480e0034a80195032135025005500243e012800e81a0740762600c4e031045c00f80e038450700c9481e140c052415182c40400c1350038012103903050707031410704903000800181c5d40c00004040d007d0103960003181060808100508180c20243c40d00803034503428a4000c68002c011841c42d030310017024100250141d407041c0c01a8007030025100081c158555a4007045601ca9485208211600c42800340e0030fa800d442c2e41c1441a16031410b0540760f456402030210429403071014a483c0a00c40c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 468652679 1250 468651429 468651431
    0x16120206030a091407080f0c120a0602030601110a0602120c03041a1e01080706110307050604061508010c02011d0a080d0218031e0d08130f020102010b1302090306070c030503010e0901 80
    0x2040c44c4602402e009030383c5c20451145d0404118000440350070000605808411903012040c2d900c0201c07070300c0e541c0300c500800819191f00400003500c1d6a000c0d9a40385d014811090a555031080149002c40080d4450000c40e9044081c18010940c02502c0f001601d104a44c03054a585198043c0ca40c0102000c800800800b040c3c1441000d02c040020070904250080c0480c1004141080c10007001070f14591008140d440c1951040c0400740c082140050002d0300950054800504900004c02e0305440580c02c2e000142150b003030600c40c804469056000142c00580018450340301500c4202d10f03600c4410581e00508602020f101640154105500030308036000007800c04c03414006a100401c2c241900c331840b100d04880d082c1014441da600a01c00c0c0c40c3c817224245420111441d141045880c0700c1c2803502c0240c00030300406070341c00459000b58094580140014036070100010303005000c00203035020090550003401248003140c20b043c050803071745144136890340300c10b800c507070901c4101d11200b0fa00410422881d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 468653929 1250 468652679 468652703
    0x9080a02120f011401080c1f031e06120b0901020301050102100b0307030209010303090f080d08040f03020a050304120c050303160b0424020301030b0f01030210030e03070c0816120206030a09 83
    0x100909115200031308804041c000782940c90014028201219828081d01a01200380100408a1030442d10024010b103424002044c603007030303511103846500c110300340002a8030303040001c9000f02e818041c0e1160766216481388040c954403012881e00b40e00007840745501503032000d440c4404055503a04560300c2c454004c1c0c1150081982da0300060b92070442a030094011804a071340c14000c0d03c409000300c601800302c590080451004041c4000c00c019030080029100d20308002c614020580709008c0102655000710480740c44a0b100c1c070b40101c0d4038506030307801ca40c0700c201440c0c00155410048165900d8014401d03205c0301d50445038448840f401d800900440e01c0c4403103803a000c0d0701c04442c1625010b10f42030b240c000684a6045140c01e0040f8030740509140c060110140040005075148201e04a0041e914903010803950100341c1790600c0d5018104000301100c10108010488010015182e40660039000400801c41c0c3d540c09149641e15040d44041d4020380c08000081d0b4241180e000307040e00a1054040c0044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 468655179 1250 468653929 468653953
    0x606080601120f0504030905010233041410022502030a0b04021f0e0103060501080402210f0a080904141504020f090415030c05220e01110d09060c09080a0212 69
    0x316113080300c0480110f0700d2103406100b6541e040203040b070b03041020302036280c8200848503c95039501c8d00d05540d2807070720f041d000003404004900c40c0c26100020b0780d0302260301c582e41048070301000e90423480300c04100c43d8908030f0080d00900d13032100459010780c0290103003400c5001a05c0b205510382c40240180d1304286100802c000e902d80c500c1e810380100040d81e50307041494040c1c400050941d6083d41c04641000442c0050101607a103a42c0c07494800003a5029000009070036a028505011504490303440340d02503010200e0620540310014403100d5821641000301c0462084901210314003501e4481c605d41106440b8030f45810103030700134001c0003030495182e4200240d031000501541c10003050349004c0c1c02d00d000700b0400c009850102c2d50150804548103981d0740d12290009030940040340903001c040d501d131040491500d00079400007488003c140b050030755540c1e1b049140c201902092000b1103c0500e031408404c60340e0b11030a00c00055444003009400c80201940800143c10303d1003071411800d009000000e01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 468656429 1250 468655179 468655181
    0x7030c0813140d0b070c151d0f19060e0c0a03060207050105160203070807020406030210020a1704050f040b130510051c030215190c080a050a0606080601120f 69
    0x1004214111a41021a0504400300150350200c0250b9010700d8580c0c01d02e40010381203100c079503841139003450302c482062458140041c9a010305030141c5070035454800791000e81170300301001c0750710f81721404d040303582d0130444101503545c410028400d9020156010103280000711070340c1100c0425052541244c0d803000001d00060074003145a4401c84400d507002551400f081000c0c0507081d0f101c40495401d80e004c00003a01c01079124803032020010aa4800040e10404556590303101303602544d0081c1c90b00400090b4003001a50312481540b00740d03944014981e00c445002c00c0101220280d80700542041100460700d028000607009243c440d0350302c5841c0c4296010484024070500d0711944a800c44100781c0da2a01c1c080c041c0c05038051406071000c075081405a4080790300051510758403001e214502e00030307507100b0302001c2d00102040503545003103080040018a4940c0f090600780150521031042015407606003450040715905d00c250404a80c080d000250158001d6609140154a032400401c0341c80381e9210b0300d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 468657679 1250 468656429 468656437
    0x40b090108070302121513110906010207090906060e09030309060f0105060f0a031d03040501030e0303130809030f0d08010f14091b070503070b04031b0510020d0b03010c020d020f030a080c07030c08 86
    0x806c02047c56042d80107100d03681c0d4801c000d440003943c02c40900c5c1003d0303000075190440d50141510007038503960720350200907044d440702c00280400c010300e900300c0c144103d1864503a0b0040e20280340501c0b9510101d003a802101190b94100c52005019a1602c42440141152500042e1190301415501c120b5100d030089060520004440c20101840c2c3e5941484009021144610342d4a0320591041c0308206442114101c0701e500550803100442c1c890b45036500183c50107501c00c20b40020303070048403100070000c0c2d085120315047c1c5035003844c1c150f165a00c80051407440407801002c550312400d81c40200c0d10060340d42c0c0344518590b00c0c5101d02c80c58a081031311035038034603030112004030380803280c00080205060323210380d0a041c100c46104084910044c1e540760b080d95944123459065515500041c101c0d0301c01101da005076182000500280301c811003811029460f00034141e21500035000e00c1c1c150030740c0b80c1c20200c00c9410400c2c680c2c9583c5a940c940c1250503c0a4000780c0d4200c0c107020101c80305c08007054245001d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 468658929 1250 468657679 468657691
    0x1315142503020a02060a20040303180909020105030718080304060c1506050a0b0310052101063503040f0e150d0b0f060f090a0902040b0901080703021215 67
    0x18103028852811011003034032184905108140c81400318610311507001c640c51780c101138075650210705081c0b0802c85105103101c0440982011100260001c10076401c0382d07188508285035543c0078590b0f035550103c2c00554110020082c0054010000210024040c00402d40c14aa1500b06940c00340c0e1502c50240c07440c0c0c042d811000115910344000c104210408603c490800c4180200740003940c40c02003c02d2040215000c3e0f50704034240840054981441c2c8404100107242c02032140b00b51a51404011487da520740004100650a0440c0880c03816601014012140b0440c1c06260f0038400200d9000211071040303021000d240420080061050045141140907083c4461510568100880c982c4114040503150ba4007031210501404e0124900c441c625900812040b1041119a80d00c0e00080f22800c149000d0303680102901c06100500034980c1c0305800e000e2090383c003080880041020004070440c24070a0104c90384c0951424001410b0418400318150002e408a896a032100340505814040840784 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 468660179 1250 468658929 468658951
    0x2120d24080a0b130c150201020c0303010308040302011b170d0f1b08070c080a050f090312030603011d0c01050c030d050a05060a152708060109090201080f131514 71
    0x504001d002e114540160030507a0102c000d0740410f40360396000c000381c03014401d135401b5a444402c0442c08600030b404948901c2608030641e940d03580c4a250501c1140c005000680c0040c001c0a110380c402130342d8560500340c0c0d07170f00710a0300c10904898002e010782c039a011500041300300e40caa00c04503014100d580200054004000101008010083c43c001c1c0315031001007840d0300700000748000304c0c0481e050724111000c0e840700d40391107a41c3d680300e100400321307078450003407116010700c1045200084e842040c4c000e03600512044009004d0000040c010052050b5000d59501c03541c0c000c0780c0009407235800344c00140724414034401070344e00303008111032880300311002110400300054840c0f04201c0c0314036000e14190041d10800910b10024a5a5000104803516490208000188580500a201f445c0001000c01814034008550b0a0341e15000604003071701c5104000c0780860032070808034020b248905621841500241d05603415800035444414403040b00b06462541e955440c0a800352011400469902c90340105003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 468661429 1250 468660179 468660193
    0x30c0f23072f1f0c0309150923130b041410090c080f060f01050c12041401030e0a1106072f040b030706080c0d0212090d02120d2408 58
    0x5884908580c081007507a10034004001000404204000f0b0046403950614001c0b494114a140a44511255401000c10f84880d90301080c0401c0d400324204042d00c0503082d040f0642c07031038155181084070207a100d156010048009503090100c0c5581b00b60f11910004202003484044104820807003801558483c210388400142480a401140100d25450441e0701e00003100d072500381110724004001a0005200355041203d1204603840b410948211001403c00e8540743d05a46041000b694007a01c560011000c0c8140c0d541415806407282c03c1d50821514090311074020350b5642d4401d981d0080000e150b02c020b00340114030120b03030303400c1d0000049409502c07450412660010380034a8802c2503050b10b8421030512201a10a4401080c1c200031074106040c5240c003500c409407425414003031000c2c128420352020440140d4249401e001c503000303500b01400e90f40c0d8002c0415040362910318403e99800c510104220248618800b030b0320184014840811000034041c403601210001512680300e501c0700d0340000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 468662679 1250 468661429 468661493
    0x901030e190309060e0f0619090b0c0f1207020d080a020102040b130915031106070201031b02011401120b061302090409050606130b030c12150f07030c0f2307 69
    0x4118482c007400481b1009108200c000003d620351145450729001141e2904291110b64042c044c1d440103030407032481194480070507100c1c550352144c20107410300d8179106280c03562100811302e8089a0103e074000d018080c0350712180d103602034240d100050b8802150740c20000066140162000b5140001daa030707904036500c0385000745010a03140710800c040290f080303058081001940041ea0303c001060191242d030340716a03150005800501350b21460303054071a802d541c082007071641036201e0454403040d2408141940d13214580903040103039058000740507c1b0201d0225400c0d14192000401d160a480c1016140030001c10124050300d000b81c6045401c2d521203810b126003032030504001d03400031513200360811404a02c0e0740040c0c1e84445e01151319020380c0c81c1640408006000b40030b1280c0b071300004d00b40d80c82c8909001d01c415000d8042200da52000924000b45000d9440c4540030150742c0140d59234034102c00d440501c4d11140f60301020400140d547c842002a00001101a200714140c00e45504144024120711 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 468663929 1250 468662679 468662687
    0xc0e0c071202060712050a0209040e071d190b06090d05070501080114010504050d080403020a030503071514040b06060d0f1d150708090c041a0f030d050901030e19030906 74
    0x150341001503400507400c100030180e05c50754207501c000380da0070040b84076100c00010000a102d08417207160060b0134099114450b003000503200d8200c071642080920380c0325003a01034032058001510407003009404c248403490303a07144a42040c0403d000040003a032404030504002084640400002c131803036040010208002d41e0411070150041290310340c0d22284410603c0020301da40321b2400703124840c50300404240b091042d01300940c0d0185030b0280c08982100e44a003866170b41c907001068221031407410840345548a201a0003861030b044036014207100c0644950b611200428801041281c0120f0144070b0300707011300d04600500042500c0420006590308401e80030a141c0c0d0707410010482e42d03070311800183d07141801c40d20440358005a14507000b000d83e150100d03084d0814009440c400d501a0a014840034030100b010000030550a040318061000600c04080c1500c500145c1c1021020500c2072091401c05e5000f030b0010380700c044c02c1c28281d0fa1490100104c070945505200303003d60000c0c0102005101160b04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 468665179 1250 468663929 468663953
    0x110907200712030305090a050a05030d0606090e0c1c0203070f1106010807120309080318041a0a060f2c03060114060406030e1519110f0a0302070c0e0c07 67
    0x3040d01030200a4200082d401c00e4210100c0003c0c10996164000f40f000d01c000d10448403e603a10800340c68111070f05060169481e005500001522031a003c00003510078025802c2000700d07001038103d0300055413103014610300b5800440c00800240b01d544202c41e070048161006505c2a00d80d916090120f00889070700900001e4001006012540f01d03034014488000d001680c0c4c01103648036029440c3c0002c043ca400c495142c0390b03034480440c0c1d11000c6807092004a4100010480000c00e03074041001c411620003d0012003040c10b02260081da0b170381e41c00d0001c544030700407200d55040d09041040f42c9151810024007403103085041031840070148001c008851905101c000d0041001c68071076030f5001c54140c00030794240300c1c501c81c400606541d2100c00703000400610080c0021480b83c003a03451140f61142d0b1f401d020b041c8101c1e0070540b151512425000340d00c00360090b10002d44210320350500700154584180e000390300191083e01c0c00c0c5040000003c0c0c145480c1500d520801500490a850b44840e01d0b1015440ca0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 468666429 1250 468665179 468665237
    0x909090715020309060306040c021005010e060f0f24091e0f0603091902150c010e0106122a03020a09090b06180402101803080403050712150504110907 66
    0x400c015881485d51500305481c2c00c1002101e002032a1803600c81c0c00c3e8a03000d1140e003030040c000d04180000400c2c014100d40300d441010151003a0f01020141010000300380c3e60806034541c400315001e4555040100d9440c206002641e880c082440c140781c603000a03055108400940140d60100302010019060140500003c0303241910418210b040000c0519112a60080c0120140d985815441c040d50346035101c451104484209a959640c8080a8039020340000c04502216600700640001c5030b44129907044202074210302c03180813940d241c020b00070200d14458007001c2e64000c403d4010002d603440011000040c08e804000050039412440d00d00000e4030004c0841d0710420070105d5100800a403000703510781c0503a0485094075502c42900d800c0c0c03440f0031141d0340d40c42100e5050f5000b1081040d90f800034019680030340c00300c480316036403084240759041c510f010003400385110251603181c0046d50b8104a801a101e00d000c4c000086d21b40d0007050900d0b078211104000204a031030800882a100248011000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 468667679 1250 468666429 468666433
    0x311206050a060b090a03150f050109090b09030f041202040b1c0b1003020109031103150c0406110105070e01050706180305090405070903080a2a06140703020703120f02090909071502 79
    0xc6034001500134500c900c1b01a092502c00b40d00881c0e41c09882d40002640c40c1c280600b000f131940c460300c80000519140004558440081001ca950140d000040d42e60306090300c1c81c480d14040c02c0c424185640a0800022070b002922011400d12542d03c00ca84281c88004182e080c000c1da449034100b0780114100074080b0007108220752411300c0540d034840d10000a50f40c00c8034880b66003422080220303180107142c0d0344111181d01d440e4240310500c00b01c030f0011b000310b80c85955503541d031010300d038009400c80b0415100d440109040e9845905954040c07000b91103d20b00a542c00140354991844080072a031044d00e0450000324005081c04491529114242d000241d9180c40c604c078034115a90b1159611070380381d420342840074500480080d580301610300001c40620302c0e4103030305224440c03130090040c114a05551480c0e03a01d910004404510910035102c00a4050b600d010400505032100c0d001040440401c80c0c105408201400f402e444e071044c4a400341100900408202c2e01e400c5110551101c01d1921000319 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 468668929 1250 468667679 468667687
    0x2011e0605130c1b0302060702160e04021909020c030409230406021b1203040308010608070203070b04140613030305060312040b0f0c0f0f0106050105311206050a060b 73
    0xa9240c2c0d4004a445540300b03040000c2044160000b603c44810443c118070300c80340300c82c1c0c16000f0140e000c01c03060b0040650b034007150422081c5000c42ca083d07940c0c50182440f010340302800200589011958031a0a4040d103103011611a251801d0304140d92005a107171485a00008080003e4061403268070b600e1748a14001c0309060141050300e40c400c500c042c0c0084c00c1250080f400e100b185c282594040510000c0c03000721032020b0842ea807000c0350343c2c004860039008608100f00000b8164003540e85076100b411154084c41c0303800036944e40c0001c240009003041c0ca0b80764000b01d101c0175400b0304001072030240b503030303602a194207000918000b0250b1740002c2c103a5000f40c001d4030090945801c5041600c05072890303107000c03d40390304003000c06800310b0051040340c0c40e051182014805440c0000703e8040e030040ba120009021182d10b40300152501c0c46a407603240507440106120200f201201900c00b4162090701b490340d100a0303960360010920007490743c0c00f80d801d16921010b000504041384110700051944108203420 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 468670179 1250 468668929 468668939
    0x615162d21080f0606040f06020c0405010807030305040e071205151905211006271802041805030c0f210f0a0309060207080c0d020f2a0306040302011e06 67
    0x64403024050b20002c07040803010135201d9036018250b4001d44503a204507411030303607074883c020b5071a10040132041c040c0e0300d00380012034802004181c0e00107030303038241c2c94103413405180c20043c40346200002c052004200020b9504c00800c00640186401107000306088003403480690204001d401c820f100604182110351000c1085445900800c05815103030425000c801141400032420b05084e40d0501e5503c138a86003010540d10303108030b900343c518180c40101c0c0910b1f440c0b10035940101c0d03450004180d00341398000584001441c05400c101041c5000c12282c6c1c4070891340b59245480d603003142d500414aa0852a045000c0803070401058907039134419032030404c6080f8500051070b0382d80b00d0004140020900005c074041024000d8008103035040c1c2c41603045582b891581020320300c9030030180e14050680191036035a240f40d440042d43c581d030b05400102505043c1059161071040040d407400041c1c1c0050315140402c2c10b598188002c9119034040e4001189600380d0129240c110354400c5c1481003131502d08003080c09 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 468671429 1250 468670179 468670187
    0xf04030f2a0609210c1205100b060d05060d0204050c09010f0e0a05060f190201140702030307090509060d051005060406080601060c03051612030f050615162d21 70
    0x440701c0c03c07004146204011000c12902d040746013000390221200c9480060701003c1d031185d03000803034041c909031103480e00701403043d0054401d000061584810103001c1414507102c1c0f98046500300d03000520101b0300c400e0f00d42c00700b41590343c101c1c1e40310480b68020500c940c0558010200c502c00425910303004128824850001d40d20003024050300780151408180c0e800e01041c403c045540d0646c0c07401c070055103000920f4000307000e8554115100c130145020000b103108140000b0030b13a0300894180c1c03200c2000d00e0038101405400900180440d42c0507401c0c3c44902c0c080ba009003d182400340041401264a2130148144011ba40f4158440c10b800e50007070f40100001940a101c0084c000c0e890725100d65207400001c07040d5600e00700184090036850001024100560309584145c191085800b010b000550311442004074a00c45041880b29142c0d04000340d406400410340802c0c8003611402e51010307124454400411190318000e19160b0100380a80703100d05000000c4900007602c00c40d080c2552000a070468014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 468672679 1250 468671429 468671447
    0x90102070b090f0333090d0309060f06030b0f0f07270e0c1e09010203040603090501140c1201091e0b12010c0e12030c03030c0f04030f2a06 61
    0x604403401c0811003041a070b44088124101400003000c4034040c440d8030700f0f5a858200704034000c10007000c440b62900354403401000524401d2180801404582c0082801a07010302256001210110340c1d865807150404003c6c8501d0010758002d2442c50210b2a01003240c1c0c5210101400d100c1f20600031404120110b580002c10400d0000144180040d2010381d06c10030340d20b11030a400813411942e444040003c89410200035043e0070b6105072000c20302100041001000c1e2203008412070050f0801c010034071016001e41c01020300c11b8882e0000044c02500c00d141401855010703a0702981711680000e43c201501810b030341990140941400801c110f01480c0180d0f034a102c0c40665011005403142c00c540c00315074800703070300e00c001c40401380080c0080a65500000e15120988507003e1203908000580d031000000001500d403410300d110003d620b9500c07941e4601109802c0a201c5407004603003040088000307408560b00030b01c01c522503221000d400300200c0e041e503105540114082211190309004124070b50340000c44c6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 468673929 1250 468672679 468672689
    0xe0106091b050f0403060c120b010e13110d020d0b10020c060714030d09030306080f070f260d050d0c0e030c0603090f0a0b060a0b0414131b0c0606050609010207 70
    0xb466a450090700101414095a44007404080c50034088106858205420700d5000041540400c22840c800c00156003024002501729000b11800804c015001c00d07940c4146000d0081c548d00038140721000c136031042039900444035014969140d14126000382081d121426600d0842d0000d098035182312000f0442a00038001c02421001c440c2600840d180e40600480302e6101010106000038903213410082c000c0d00c07840c0704440c45841017414003540050701203140001d0361044825030300840d10740025080640d104801a90401c0301541b2802e2803140204002450921a912416114013204009100300c440c400001d1040c40007a18401e0490380d8045101e1891103000c5540c01d44a4a07441c403002d150a244100c03400b102d120b5144810180b02008180030701c101c0c0129000004c161316821000300034000c0e4420140107004400d43c000c458580030042c8000001910400102207105090039400c29072182ca8900120f0209030342c80c41071000030701910024040c00c0d11064a0310652a0000750340b0001c522035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 468675179 1250 468673929 468673937
    0xb041b09081c0f0306080a03091a0c06131a0106030f050c09010c0b04051006030c032003070e071b03030e07080f0709091103010204170c0307030b0606031003150e0106091b 75
    0xc0f404251340a6800040a8074104044403d060000c6c030b4040c194103103034010400547c04520410a0401c8050200d6030081d80540103441140c454001e04a030b07122004804680b980c0d040264504403080d602e0010703000b010255004600c00417040e01c071108444014101c0496800c04015101050740c0220601030219404030010f0507559403402c0c0942049060120100400c2c241800081401043c40c08101a28018080c041c8003890106800c1e1260709860212034150300135180400480880b5480d80d60311001c41d00340b6407401c05a29004c1e6528078508030040300441c2d6a459081d064403400c01c280c50140c9142c00042007201a0490744030380e2a6154818078050300e41722485402084101c0d8007440301108040c00039034403941c492400444411044d0382441035031043c00d0000800d8500003c84100b2241c11460040680c0c03602004c0c080150310040035411603140900c1e000002840d03000349840c04100001c40014954020300505094541d603034018081c507402c11b540005905650602c2c0085411030703080c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 468676429 1250 468675179 468675197
    0x3020d020909010f0204090e070806070813030c06140106020c030601051f050c07060507020924010305220507050a09020408060a02090d051c03110703020601060e03010b041b09081c 79
    0x10b81c0c14090f03c4c100c039401c1601e50020070002415071217500f007031078407158010541e90203a49500b040ca0392280b04840b4200010b100b44003040c0c80c0d048a003428250700b40246403d030602c2542c1d441e04419190300f40860034038a1701c08030041016aa043c0198020f01d40d0031000340096502d0900000c0360710740c01200441e1100b80351403010344001c0c004c0c422078400e00201010785000075550b00c0060b2131600b01400c10303802034400c0b60000d00104140c00130200c01410042200d98602c501034011002054004c1c8104161168215494004c3c81443c40813401244203100070301d04c450500d0309200d4642200da0003050810300501081c44042c00201e42c840d170180e840000181c903a43d100d0009400240403420241203070140320099a071000d40011214230900030b5807814022803291103901c8000d03114a543c0a40141c1002c001401b00a01c5001c00d4440b41e0401400403030700c0101100054120b90424460144080c001903882c522540c001c079107040108050b0001d8001d0b9496065031081c142d4221102c18100400c0390 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 468677679 1250 468676429 468676441
    0x80102070f15150306050f0708040f120c140a03021207020d021203070b090f210307121e06031505070906181d091c05040306020702150f1207080103020d0209 69
    0x1034050f2807684060403600c002907540e400d201d00200000d544440180d060f0500080d441030140007040e004684c00980d101c0c84090a451f414944900b0741034401c1001004400d40d40458981d41d0f00d440c0d038800c0c5002512200f601d03494003038a00111421000c8084070140008405651001c80000c40c80790141c8540b00c003003200c0800c1d5410b620614000824000c10b8030148000e10310000303a0701a002d07440c5412101441441c141b122044000700d5007012030f0700e20400024260b60320803981c80c030340d20000c8400802d406001009404881d011006000440c0350313505003c2081c041d01c102c90034030985c1900000c10007418412070007004608c560103424280304124602c07a1881480c661000024080715051410200521031100880402922044500d101d8060261020000d0038200f1040340410740307410749011706c1c554686020f504031b401c00366404600c0c0d0900300d440811030301c010080710482400c003e075507564080b0790881e03100000d40048100220300c40144010780f030305060000070f036404648040c0140d9481c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 468678929 1250 468677679 468677681
    0xb10030b090d02010b01050301320627060903030a140c0304140f09090d1b021504051f0509010809101d0d0503101412060f0a0501080102070f15 63
    0x55200601008102042100d0444082000c0d0382d840079982c000e1044280344070044038640006e00030558507a0480041c44052940c3d422401c41244540076240100f054000006030207801c6590001d915442c41249170445005000003d0350240d000c0760428201055440031036070340d000d00a1060140701c4085454030481403804180e61018100c01d003101d0b0344648609100c0f000c50664000c440c05154002d007012410700c0d01c140528850201c6c0780042c04401c104180c220b9100d0b01e0020406022041d00d680b02003d6243d00e810b0603819000541140e82e22440d04040c07040e241c1d03200111180304800041089003290340b1104130b5411000c2480c001d036071500e9413003c00c1d04213030b01c4231100d00c2e0842c03801100560000c50400c2100500f10070b14280c6a000301020030030f403038511044406030701918905070148003041281c140888503580281031507000086810f102842c00100b03440c1032410018143c208100045140101d50140c03030b00c88002d40c100f90043e0755807031120f800d1080007052028541c150130582c40b01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 468680179 1250 468678929 468678961
    0xf060c030203121e09010207030c031d04020f091c050303010e0612010c03050109291504030c0e16030204032003010b131a010903030f0c081306210501050d0b 69
    0x400c10a8219007052500c1e0001284c80b00395150000d002500000d0003514188251154960180c64074502d89043e640c0c220344084000901d41c1c440050a6030b0103405484500c06000140f042842e10340c1e9130541c0c038040290f502c0d50b204054561b8040040401c000400120580f411203903142e03135110050f29640d0000382c0d92040001007104541c0f8004040c0380c02c540c035810045c122400180100505001e221126204164198207151541e4070908260343e141040e485410110019520f800d00306612581c07944050111988040400b0700d0020070b01c10000410074034280042c10f0380c2003c5250614664496600e06032441d00e00c0c0c0c0d54100c5001032891500c082d0000400440010030740d1410a000340c5510000300400301c914280701310924101c010650280c0c4000b420b99405490b88111040312001c100c0b0700a00e1983c0896210780c0500c4040c8440e01413819a2019080c7e40e15004000186140e40c035105080c1d58401c09429810300e001044591140070501c0c1c03003203400405181d600c0d6900e421041120030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 468681429 1250 468680179 468680197
    0x103030c080903010207020d030315051504050904050f2506090e0703090f0b07030618020903190503041d04060509010b09010b13080304030803101706060103090311060f100603060f060c030203 84
    0xd908607230300c1d04269066010000514105214802031921942888081c400041075000300f00c1e400c010510a519000c0c0990751710038820800c03100d050501c020100d0034500c20819114040780040e116071103d40410960780054600e40c6401e060441c5000d10844c00010b011b0034a10034165078070414002d215050352054943d98024018030325504028034018010f08042c80341003811b05010400c03c61183e880e00884480c40300040040201e0300b00810500f002c0903014001300ca139844200400610014610018102c100020039003048520f011705089080e1540201240c00c135903d001056031065031002c0000f415114444803050322011140040c0000c2510340d00100940d1001140000c00c20664400540c400c5d85006000400340c1d03503030701c2007201e82180c08001481d03a401501c0064120351003580804042406498000b000d600d80d418054201f10099400110640c801d4007007001c03603032180300544000c000c9490104601840d0240b401d00b50951801044e04001d031810341002818420010b42e50407030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 468682679 1250 468681429 468681439
    0x902010e220b060f030103030f0c050a030507060e06040b0129040f06090503070806191e090501180b06131418100203070e2407050f060606030103030c08090301020702 73
    0x84030301d401481c0c072103540046605080b4100b444201e80381c2451000e8946020a0b2000b40d410b50342166401d6600ba00c0b40a28901000307003052404c1c0c04100c0c100020400d190213902c40f01da9a081c64205401516940040000540d1240051000107140036241c103045410910181e52045920407510700000002c07001d101d06244042000f00d5611b0b04d40c140003044a40b00e40b039800d0059a60030505480f035407a8480d0704c5098010f42c0000b001580c0c0030321034003000800b0040014813030082c2c085005150400a500700302041e40c51001c601044070901c0f0707440d1000b1104070000e418594682d47d07100e005e04010112401a6126032000d45608000d410a034441448420110703801d160040082000710584540001644501c100712100d0350180d00c2201d004070320680d1a10800c00c070103000e11030b21500d80852442c0018015880c00c179069100c4c0060040503202c7e00107010300c048d404030311924005001d000140302d0f00c406c100410000b6004080c07000541c0d44100380c5901e40242e0f00000e1300a00405402941103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 468683929 1250 468682679 468682699
    0x31b010b04060e01050306070f0f050d020f031617010f03020f0301090b0c1c0204051c0f32010b212103070f110c010c020d0f0507030c0e0702060a0902010e 68
    0x3198102d440f00303050b00c10030703811241b49a0720b0003000c0713072171100c04c074501f07804500c2048a00d242c0603c0b4000400c00407030000d1015141546016860010f9803080341d0801d1991041c600c03500c02c00b0ba000b582503100c036806801c01c880710f5040401c5000100c02e42e1100038800c0d10349448040386914290409080c035500700762032903940d2030910046103480e884800e4600300c0c510440540d1589000328801d850a98502500307055002141041440d011503020600351000214003255a001445490650b07a11005001208661b60304a2800201609040c00030b81d580c2e90601d0081c2d007454541c0b00d6100103045043e00800e404c2d0a9140c0d155050030908414800b444100341001c03070701d4034500001035004902694a4a001040b503550450300100c00310b1581d1540c0c0c02080c240b1465600c06c0000295860009040c00ca8003a0690754110725198000c3d8101c1c0c05400808013003060000c2245400001d00c80742620300308034a0800c10081d100c03480108002421a6242c2514080da40300d03a032500340f8220040c00401d21 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 468685179 1250 468683929 468683939
    0x503030d05041a071b2102010e010614090c070f0606060203130504090c091d010615080903040608010902030a020904020a1205070c1a0c13090212010e09031b010b0406 73
    0x2804040b40c003602e41402511030300e181444100d02662140f6541d40c0c5040071800200002402014407000030744140c100042c40c0c1101c00032944009050094540000035281c881c4d41d05182510060b5100c42e140e60550000b191094441903080c641c880b000c002004e82e220520300e03000301c00c08111039015042034646000030800f1900000201100c841185580c4451950b940401c400d88010f030200401c03103195403808000c0300006170400e542c05030a8903195005103250f109041e085990170392004942d4041005616040da400c0100140c11040c0400510300e0a4100314000d0f00021062003a400350759030000003d081c10000d9410b8540d0704000130010340d80d0341a03035800209040900b2960706416841c08000c204054000d846084050307910250804204e5001c031807031203950100034a80c01d00030a08012a0030386148c17038140000500800d900040c0c0b641c04041d801003c0b40f10503002920b1841c400b205000034503100105542d18003004099900b101d041030b850983c054280781200e43c0d00a8201800071607 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 468686429 1250 468685179 468685181
    0xc0b060d1a2d06010e061801030b010e030f0303040b0108010b09150307120b04060b010302160809030115032001030c09090209041d010b120303070c0201080c09060316030b0a0f06050a090503030d 85
    0x40122402d988000d817807030100e020044144640e01560000307050017500207185500079000308801c11380505222101700300c3d480102e4140700e01402c1d045e4003600008100030400942e50605805010103000800c80d4a44401c04180342100143c14418000e424070400c0d500c90703600704032000242c80e0354450303070140003518644000d04c46801d030b408850950901012520b20b51103482175400c50528650600036000305a1564034050f489110025019501c1d030600d403402111900d140b10040d44910075040d11001414a862640c2c0d541c0e030032007810541410048082070340d005a00308140d0300d1102006036a01010300011b00201692000c603400070000c1444030008200c198420f9441034001d59041617000c000001c0c168903407000712103c1010502d200300740e00155105903240c50f030241a5401480c40c041012000076401d400481e150043e110904002422003681401922a03141080d160b0000d07150504a20241b11500b074014042040008608c120b10b2074842ca41d9200100f0024094a41d50700c40400390790 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 468687679 1250 468686429 468686431
    0x60e0106020f0a051e0c090103052a01020c060a0e0d060c020d0201050402060304080307020709020c0604110111070b0d0902040603050a020a0f0e0105040f1b0c0b060d1a2d 75
    0x400980240034090710108400300b02c2e00c100981c408082c0a50f1980d9449411003102c2008031708000344036040c0241c8480d10365090715802395006c0c900a0800454103045d051307103481c00e20740920700185178240920481e40c0010741da0b46000d2040310415117413014424200d483d51040b91078180e100700791070034003001c1c01410360203620788004590175500b0324880200240d090740e40a0b100250008810400540407848a2003d03542044031071041e281c0040e510087e080907a040f242c7e114030550004c10901080107155a080b007602202801c0c115168546920402d464101a220b004010366002600d01d1040d1000c0e4031100800d94014404c000041e180d0030a40d03035501604608038043c0080316004641800c141699204940c03070005110000d03070030301040c400540b1521402c42c0d0810784540c1011940654041941c40c0700806545903c0c00000300c5c1080c0c1034120029151703500542c010320342031022603258040d42903009012a40c03e24940c451140b5250355001c0b01005888821a0454201c0380700900c2c4002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 468688929 1250 468687679 468687689
    0x18270d0f080a06060203070807020316060e100e0102190201030b030a06051801020304150207110637090603330801200304020d060f050a020702010839070501060e01 72
    0x5a5290340c610002e035080718a103010300d030f01603481070207a400002d4044008040f03442c030150584007040040782c48a803565400b50001f00100d000d15070000058200740c40b00d29900829840c2c6018003240000020351520189072545000b00980780c4c1c50f44c01d59019400801d040300018040b110303820350760b00b404401401e080c0c0b1800042c244241000000d81d8050003500d004a800a5082c0000203002c01c000f00207520400044501d5412080714000302d907900710107003401c003140c64540400705280c00089c000c0154454062400c1020361074101c440035601080c0001603c60b6810700180911080407407421907116140600c40c0b500710440d056102a01c0d074103c500c22a61413900a0022526005074810340300600c0040d96000381050001a01520300511520801c6d03001c0c41e000141c1c03d010304410780c00d44404503041c1100f0342e00058030718210f5a00c108069030022181c8209111005a0320800d1803000a9001201c0e080d80b0400c1d00e01302d4040900110f88501d58400d008011095446500d010b00c42000d10035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 468690179 1250 468688929 468688937
    0x120a020307060b0d02030d1d0a0f1701140c071a09010204150e060d05060d060c09060f08060a060c05030d050406060317120705030c0f120a0b18270d0f 66
    0x102a444d080c500c0031400d51316401006031026450310601191145201c0c151510100182101d00000b9110007843e44082c01c00a0900318039507040c802c0d4481c5203603030140d03407190390380c0340010280510444100541d00b00662224840c0e42da4032509010100c8030415011009284804d03082c401c10b210154000c0040314080036101c201182c038410305907410651040080e0300100108600d40c1c801c512640015030101c1e000b0400e60307181159480c0d9070210380ca0041d041e0003081d5240030078400c1a811045103030017490300749069100d51511002180030b06140344140003e101d95440c0c40b10800400740244d603500d1003805002c0113146020b080c150041c00c0c0d103100642d01064910700b410550388a02003140c2810005c07401c482c0c00e54840d12011036003588000c0148915410030b0004da084036080000501c01c1c1c0101710004600e0341000c0e4106000c44e458495102c0c0728403660300d05008032070fa60490742503000480059901c1710304021005002c41040c6404200031501840085a007a26040541d000f0f03152901d0b60307 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 468691429 1250 468690179 468690191
    0xc102d050907080d020c1009120308040b01050406030f0b060a120602250210111e01140c07210c0204060b07030311090f0d06020c120403170304020609060c120a02030706 74
    0xe1510341d25820314180068124885004550a01f4410b1a4102aa42c0fa01c141d440d6601c070124210b01207402002c500280c042c2040c88148504032402a0152108541c104690b52641c0c5c0c0e002c0c4070202c00c5000403d41c030022000503071240e0b140140d03134000f0704a05043d003440d85110f1170301c0d1000b94000800500c03441c921408008202c003420451170000ca80c003900ba4054020f81c15000e030b80d2910411764422140c4182542141e4800444140004000a0800101da00d407110354040c40790303600c0180a001040400d01030b08000c9242000809414400c025840380d94582c004001c66280f44d0800b8080d404c1401c14000040e4192094000d0440c01c0c002e64041000d81080e0031404150320031140410750003c0032085000c010b141440314000120f00c144001072414185042c4503080a0800d00068001032000c40c08005201ca50500f400c104012030302414a9031505500060081c002c1c0c028072401180e0101c0d02400cad4150401401000c40c1240c0045a164084148025070380e50242004817045030601d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 468692679 1250 468691429 468691439
    0x1b070c031709010804020f0301200d180309150201230a0c082716060305010302190f140102011508030a1101150509040813120b07050c102d050907 64
    0x100742e40650005039640f41c85500c9603000c1040014281c03021036410f56a441c1422001110400c01c5001c400341031050588a210043c41e0f00c003280c01218681080000c03078a1a0342c00260300c42a444155210359002d094030401041c012070041c2441021400c45060000c42a11141c51001e111071195031050400c0c0906802c07060220360211040e941008a4220001c1401d00d120203042000c2030f00c15401c0c01c0382c8420003441e0541d8001491a800300d404656180018801e40c2800e8401c20781464000d03805080c21072074043d4400d200c4055100b40300c0c51907640c3e1040b4009a2003034010f5401401e15a06000d100c135150003030315481c1c4d80515054408980c1c00f94035903200d48010701a17a1507021101c051200c1c858501003e04c0ba448c071004004440500082045c0076541480d0090a0702410030406100384200301441c0c01d024030314000e88070381d00303012041c0091900300b180003406480038501000049444540c1a81604040100c0c50384902500d0030789905007428034040d4842440340c0000005c40320000d03a28 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 468693929 1250 468692679 468692723
    0x40312020f071512090b060a05030f030d0507050d05091b0f010203030c0703172a04030203061b04090f09022e0e0f1203070b060406080a03081b070c03 66
    0x4501d803052035044144204101003030107040380c000100d1820b100f9807202c001c04000e01180c002d00c10444a111780d0b80140420781c10201c0400e8090030090b03005244003030801d18025501d0088090b8180702c0b0b5240c4e030004800911a03029030b0480d044c0d401d802e101900700206a9130700e80c003114a4058140f9921030b10201c552a051400310701080c41a00510310319198901441404c4d880410203034103101c003444071100141c2003c00541d1190b00704500c0442c004900e65100081c0d9030048e403400100c203809002c00e10260341c01241d080d41202480342c0584071000204c1d20000240155403000c0466880c0c0307003603041000d0441d001146014030131950311a01300ca4112032150141e03147c2c29a104108407110400e800c144c015034060343c1d20b000082100c2203800c82200000c1d031070300411082007015000400d446040003a079400c1d00c4c0e0071141c1101d00740030240c03c04030101c0d0b60f48010b04004d002c000700907011401198010300444004804013018998030801400c0c201346030211071008a500d213000300712400103500d00d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 468695179 1250 468693929 468693943
    0x1a010e010503100308090f060703020303070207091a01121e0941030c01060609210b1f0302100522080a02060c0f2a041107020d030c120504031202 64
    0xf020a100280030f0540e15500011b410071807100c0e4100402d00f14038406039441e40c014040880c4241c1c015641d914003800c1c000d04100442c1d0041e2403050400b075428107107540540803409039050038070b4045103030303044031400001801c000000d004000e520328400d480340d283c95070071007010795025204100c0043d03011112043c0134004045280350750b9245114082c0001d40807030044074901c400c0e0040700d082034503640c1154212503640e4043c101083c4a400e0410440035424070f5002c00c94000d01740841c0340112926690091140200f206c2264200c405201c885004000703403240185401810702c1000c1e020440d800f40031644084030500038400e02e0341d560a400944032525405480415010f015225110f50074880250042005117031a805070107118001c0980130404e214012814080384c2210352101c26080e000ea80715400c2040c005d900340312080e46d5210420b8110b0b4409541918501a00e1204d4242281c20712442d610042c001c0c0070300d00500c80b005900c4806041a2030003860440c0c801101141306907074801d2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 468696429 1250 468695179 468695191
    0x90c1401032a030504141519090b0c0906120a0504420e0d18050f01081b0c030309061e0f04120504091104030c083d1a010e010503 57
    0x25002c50800d2440d0b2081d0415078119200d1000310b0f15186010365801d040c0001c040e01204003074000030410240c1040c1c00b800d02a480080f48007005941c00700d490306883d8140003004c0c0b00c440c00000910102d5a00c80b43e0482302d03408001c440362119810400404005050207550980b00c0b8490b06544040c00112403500003640748160a540c24141500d41c88508807082c090f080301986c03135803a22003c0c0014000d00000c508000e00e0343d1416000340003000400600c1d010b5401c80e03401002a40340350500341c0d811017420758218101400762001e86084102c1401a0f104441145903980000b0007480580720001445500401c2d003011120500c80c05507c1464407124111801d16812170144040b80100388200c080d448248203070714049182a0b05c4095000c181d0b07501041114900d00c000408006106c0c00240302c1c40585422030191810031503903005045030282e00d000c40211500070742c4d0303171a81101d240e02e0340c503e61090b050000d01440700001940c500e940a806a0140860500040b14079035610078021648505 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 468697679 1250 468696429 468696491
    0x121e010b1207090506012d020d0201060b09060c010608151014100507050a0c1203140a0905060a0918050a0506040b01080a09020a1d04050f01021303110301090c140103 73
    0x70b1410882c40f014100142500c2d040c401c500a8101031016120181503101c080d201403d6095407255070300074a8289200c00e084216450004e060048070041c1003150341487d41160b045031201103024605005000c1c0d0352000b038aa101d079401c0d9284840d040c2080d00d00c250110700344ca200540c1c1d074043e00c162a42411101560151313016907060b502c20702610250080900840448107a100c8594880e0801d000603007280711446040c00d407860800da404108101e041c3c034005c0c003250030b02461980180600d01310740a038501c0341c031000c1420b650061103400100021b010b07000400c0910340d02e6813141c034006c01c41911a5101d0600f02000a0024209401403d00508040c2e41d13200c4181d444804040080505c1e110407030380410304c05000500c0f110000c4403c02507440e0b10f0003090079410a45005840c2c50f0880125141c241d00501214104004600d41c50044980145440c1b0390221000002401802c074040020034603202400080780300c4491842c202c50306142a01c041040c0040764407061202c0500c109245020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 468698929 1250 468697679 468697693
    0x5100617011a130807080d0302090a061103130905041509020a0611030c03030a050f010609030b0c030403300605150702061e0304030f0206010f0e070e121e010b12 71
    0x100b55444015401201c0c2c038a003041c208000b940304400caa14043c0d00c044000c0e4000203003881524028400d0249040060404500d03006400f004600c1400c2a0303c07801040c0039201021104101c801d208540c03880c040080f0000f1902c0d115119000140029217040d1034581420040724503209281c400c003009150010320708100186407110880d0710100300c080140c0315000900600803029001c0001d103001c0c00c4590070111703162809400303061a9880503848803040100340f4008001040d002821650050030101ca06642c0c0d0381d55040a071000000c03414008000070f030700c0f00caa40f51f450b17030200c00708910100610180f120950391810031020035150b05800c446454200824001850010020700803020101c030001c0f0712940c21600b6110582084405402148080d09100310341a0706001d214007601a20505808003414190b0001481343c0080c0031609100460000b49209d5540e0380820f00d007624620116048526640c2c070f01030b0a525080650641ca600346050302c807580c50b000c000b4040384903400340103102d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 468700179 1250 468698929 468698939
    0xc080c01091d040c120309030b0a051b09010e0907020d0210150603150306060617010902031b031519030302010e0307240f0f090b15091f0504060602010510061701 71
    0x2034000140c804c5401d00008a030004000d480f2100c0c0c842c02e00c0c040d886d40c015103455402c4c010020400100400e031203924200c20050700725201004014858003c0c0c0101e47c0302c01c000d0005940850b01039507035941c491902c1d405c10080c55030001d900e118042d0540e00b920307400050100d0080c1901c52202e60404103100b82ca80034000144264000020400145d1207003810300e0b501e48070340c0c0031246aa04800000f41020083c0e00070303c00126001ca004001c035800452031131400300c2c00c89140d00740860201a1841c000000324159815055100400d0b60005115240d45280340c403101446111512080700507500701742c201d03842da04020059942e015000640303032050b6201c500810340d001800d244071002c80fa03503908800344015600e1282d02c58507920300d0800902900700381040b01c49080003c1040065050954070b90006840c0c0480b440d0704040005010060f15010100f403071b020404541100c0d4201e4134004001440303a40c150080c0d40141201d125400207992244821115044403030740c4084520a55001045 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 468701429 1250 468700179 468700229
    0x1b020a2301110a0315120305090906060904060b09010f090b0f1c020315040b0904030c02090705120903040509010e010e010b090609041b12021813020c06040c080c0109 73
    0x305000003000003071845880040d944403a0420003600c80080c2d603e5801e10840902c15200360040c140300890b020180319650380c010828800e61202c64084c4001c00c0105085403580c40640f07079140d100501c01c0c0b05003a01c1d107030490016040400440c4c00140340c01c00c01d40902c0d009100c4101170b1118071132820f00e001407444800340c02c0e90014810359030320400c500300c80340084520301c00b840c00b54401004000c82400810108010f0714041e0710b00328071400c4c41006010010340c1049000c1110780c1d041d500380080d80d03200903064907180a03240141c0c00101d602d40c10025140c4002c402007090707440c00c0341d01501e5170340c84101c0b074403003c142405240031080d100001845000081405081d9806000317084078a080c40e01c10204007603456400281c0b500da0390240d00c40200f160050305d50760048120040450411000003400d82e00c4001c210b1856008141219180043c4000342e012100201c0310b0004995841c1400d14010090710810322408405019403241e0b102107601c00c41000d001c9440010805502c17801440d8104 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 468702679 1250 468701429 468701483
    0x10b040f030f0219060503041b06020a061d070603020418020403150509070f15121112190e0d08060405070e121606030212130309030318050a091b020a 66
    0x20381d00582c0113940101c4d000d6034818a0001d0806a95181e4590605250a01081c0c654160345000c132020500b0034001e003680091810a01504200e01054444c80344501b0074200001400d6101140a61513012038460740640051048a4040103002540003607113041004074000c0303010040501c0c41884200180e00c1c0d464204a41102a88040d6403515550b460310352042d5540313601c5205014911059a05a00d410008000800078426800e00135007681c00394001282c400ca5500d46024070000000c200c0c1040100f000480964030b0400c100b108240701c4e50352070b50b0703000008002000030b41c0c5040004c000d4241030080034000d04a41d110818000b0014081022025204089614500c10a803064455110780b0001d00020003c40c4ca0069449005a07144001e28100514119054110780a00710000e603100f1521030450b90503151038110390401c0007004004507095405030354420001c51000c16851500c2c1c1c031983c44110550340403c007885080d0400c1e0b845402c40d100244c52070901ea440c100262241009078 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 468703929 1250 468702679 468702683
    0x803030c0423090a050906060102060c04061d0910030209160504030f021c1523071b05011e05060103051e07030f02030a06060f021606030b060c060703090209010b040f030f 75
    0xb05071800e5014040381038584200c89114515031901c042c0440700034148480c0da0000360070300c040e040310703d8072640701d5205120781e204240421080000701118480310505000c2d4641d4010000352060400ca003024603880c085000c00e910552900020031152080c4e109000c1c0c20b00c0c003d071540ca0030246151500070b244a0081c1c42a41c00900071280c1d66450060205903c940350700c90040c1900b8030713140755050821078100e00311f2403445050000e400d1141400107100756a200009181c00b03c2041000c40200007030324032052000b4015800c01c4125090070005002000e40220364032000c2001d80d80b11401107060322000c6e10316600c42c01c3e0080400440405003d0380580c000b030f1500303000c190390420f074261030120b034011a440c021855840780180482c9a0006940003801c4c0188000c1c0818081020800c142002504c070705420326544804003441178a40c07500743c6d031004144500b60781180c50005e07006000352030003400480c801c41d1601c0011031120203440540e41554090f01040030740f141150344030500e40c0606041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 468705035 1106 468703929 468703979
    0x70309170f0309060304030311030f0915010302060702040f02130e0907052205090a0f0b070207060228020a0801060f03030e03190f020a0803030a150803030c04 70
    0x140c40454a0403989130399a9141c61070103900814041a807009035090200c00c001c443c0015540151003036480c0f02c21f40c1daa060360000b452810b1202400300035400070080c011035000d401c041d0f01004407103a0848005181442401c844030040c403040d405450086800000c10000c20000c2c4285030080409440f4505182c4a40000c0707009101d085000110103030365000010000300c01082003050b60703608100c0c90045003642c1e00f41308001000c1260004094410360500150b102d20029100344134002d802c46c9100310400e08200003005460303a0000740e90084070030a02144a800a100d00402030880314090110703680795142c060301141c4810b0109200f604640340d400c408004000040b26450341c003084030f050711381181c0f0000707a00d6041078100050320b200200070807910075003590000d40202c1c00710f2010001c8664408509a4901c0116049070034000e081c00704125040340120707290038100305126 = true := by decide +kernel

theorem cover : BRFrame.Cov 468525179 468705035 := by
  have h0 := BRFrame.cov_init 468525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 468525179 ≤ n) (h2 : n < 468705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
