-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4361
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:22:31.953932+00:00
-- url     : https://prove2.me/submissions/6273cd83-d5fc-4388-8bab-4cca6b4a2549

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 784172661 ≤ n < 784352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 784173911 1250 784172661 784172671
    0x50628030b011d01331112030603060f0a0209031b010e030f0601061d030303040c0614070302031902010b1519020303090a0f030c0507030c1a18100e0a1701050105060f040e 75
    0x2c04a403003407800e80301c100c68080c103030980580b078030a84804410781a520705514441c52108101f828030034401e00d035a0120300035030429048020200c282e10b40203050002480340303120f02903052003110799041801d1915420100d00d108241c84440f140c40400c010306455000c001141c1d01c072600401d005210481c058502c1181d80d110160000304000346500200c0d240d03501c1514192414425900c3c2040310305c1e800000d8100d01000c0c102104c1c180750300703503402a64a01a4400710101c1c07101d10001c08903118400d500c02e40c4c0040c1c00911301ca1098040c15840425540807a800c2c2c0840b8011041c0c550b1504c2c00002224050321001e40184800740080d02e426070b440c002220120100300b4071000b00d6011860070030082000d10700071280300c00524a0301f018074410711001050512000f800344a804002c007801d0b080105464425a40c2d080c3c101c200e0fa508840d10140301380c0495000741c40e40760220329200384000c14031030040c10348020042662030744104001e84c01108410314030080e003017005002400c01010169008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 784175161 1250 784173911 784173959
    0x37060f0c1110180b0c0d11030d0b0607050303130203011d06010e092401090c0c02011d0f0d050a1202010e06040f05070504050a020c0709020f0409050628030b011d01 72
    0x748000c01610f0b000f4400039030040c0035580011440300204201840a0030b01c0c000681003840c1e043c100c040e8255240e00905440040a030740d00e10340c0c140b0300c0d200c5c00e0495040300e82c0034042d42d90380c0c58880f5122410300404401a4002c2d0320b001d00d8501c5400c030000780048142d141c90b00800e4660318080c01d01d0901d0790006d0544005000300844450640412418040d5000744828508255814814100100d50443e4038503420007a2520818003d82d0300880310000c011000400001c08060410115211910301c0a529400034503a010030300600c0b4002c580e1494603840b44009080c02c01c40208128280c0d103021a40f41e8180d04000003080009100400240c40380303110704192088199540000b80c101d4400f01c2d19801065000608685034403c10301c00c0d0385c00307040d0f4080c0c21030034510803100b419100d00503401000d0b0080c0d90350f00401d0595130390103c1c02c01038410344614692005400d440e1800400040d1104036690400321001241900349622110284058140d070041e29a2900344c4002c01d4016020840e545 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 784176411 1250 784175161 784175177
    0x1a0708160f0b040302060603030f03060d020d21140705030306010c050c0414010611120409020f04080610030218040f061a10090815090c37060f0c1110 66
    0x840c100e515285442c010b116001d81d500e02820007a00700a40140564031907001000180b16800d0408160380d0441c40c265080c1145414510100d5070794101a81c003d02142d070011007440c460705400b041500044810782e14284070b089600030300c0c0f901c1e0094000080541e007061001400c3e82d4071490984004c00c0c040d030210b41c525214440424100c4040c4040318445035603005c018020150404080505801e10f10002c00f074004901b01c207440b09000f00c1c016401c01e181c0000d40015540c5920041c0c801911101d0f0546005040200707900880b80854401240180700d02c119217180d51422180d941d11840d00540415400200c50b940d06000b0300703000141042450070940560307410384a03403444003903000286d26001c0d0f507070b8204000a4940811000704900a0409404000f214800464031904041041e01c4552000c00d0350410a4081d4030801401d07580345940110181e4241c07092503011040f6804c0d3b4072800c0000e22079010841e10210664405461442da00300c2000c44c0b411701c0b24502951500a241c83c00e6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 784177661 1250 784176411 784176413
    0xb030c0a030210172a030609070e03150901020c1501231203211305030702040207060b030a1b0b0901170709051c05010605010f080a0f0219020f06011a070816 69
    0x139103800103540c0028411140e044010b8002807114200c40e4802104002900750301c0d103040001d040b924010485400c00000440c1e90110380c408000700300424043c42c08121903440d210144034001d410006c800c1100c1c3c442e14038003d00c989015540c444c140c41c40c98010064003552441310010101240010342d0700180c030002c40c0b00b1b11407028000383c801d0040120350411a0008910031080050000d020200b00d002e44201c1d440000c0d400004459601d80c0c141c070050307114010703428408003c0900aa40319054054804500100880346860380392074000c089110071751039150a420300341c0e400755803009404a0741405a800640008100f102e034080c200b440c00701c0402d0748540105107107c844100000a0b91100354148042100038003602c40640001e10380061582c94008008004039006002001210754a441c1590200b410b0f030100c035107070003281d01e842905090360070000795100c520a44c49030b4540926800400c0f244214802c10b0f10442c540790703959003060525114240298440c0d00d400391144aa403698078 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 784178911 1250 784177661 784177697
    0xf061e09050d060b1f05070b13020907020a030807020610120213060f09230c0a020111031008010c0e0f190306090506190209010903120e1f030b030c0a030210 69
    0x10704148207803800300b0324404c003a0601c80080141070314509a0001d044103d5a004d41c0942620116038010110185d10b4403070564030941c90418001c0030b500000000c0070024501d80005500300454030a5840c1d0000d6034039807408a80b9000d0039075500d00281c000c1d280821841c41d800b0300380801180010b02403e0507401740204102291f40903031000c0e0360411101f6003009140100d100c1e0864024a00186410075090308414004840c3c000700400380031540800d128036003a20075449800340f1995170a03080e989040280b805902e501031b52184004a60803c50001185d52040d000860305040140c503040c40700203000104818501c00801e03006038401a1000000801c03004e001d50b00c0c00b03a00800103402e02c0d041040300e809015142c0040050310390300421200e00180d034824075481c00c4030b40001c03d4030074003d480748040311000054480750740d014800344107200b00705d00c50031000c1c000c68210740c82c1000202c50b058241030b141c00d821402a9840084000200090b05014004210f42041494040b1450f80c0706000a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 784180161 1250 784178911 784178929
    0x240d060f0509070512010203010e01090504050a060207061d01140a050c090d1101020d300204030209090601061e0c080f0f04080102030403020613050c0d051f05040c0f061e0905 77
    0xd042d82d03018042c00c10450078072030b40b1103c080c08602c00943c5550305220f040000604107204000700c0300d5580001509005042c400c400c42e165004030255a201c0300c50a148010340070310313034041c0400c0c6441c0b10070140c00c00c41445824440395254030485090399880c01c4640c000c0074014901004620100320003010381d52517003043d00030503114950303180702a003000d800289404010400d140501c040c118a003403402c9031103030112881800c2e2a441e0380910400030708000c040c1c012544000e40254482d814011194800314040d4142e810980c0e501140380c2d030010040c1804507800c2d0300f00000c540d1541541c0007086540b0300800300d07110b102c4911490141c04401c5250b0b264020741c8411010395020040c0070801d5418040305402c440f212100341400c051685400c0d17280d01f50305151520560607a5801804c2080520a03140160603000364101d180003100450b0780904002c690032a42c040d00100040340b0043c000c0d8101c0259426503690802403000d0b03031050190101c480d0000420f0003200300c40010542e03115541 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 784181411 1250 784180161 784180171
    0x14040b04090b090f272d0610031b09050a020c2107020409020a0f08030d060b2127100f02070302030a0818070b0a0206100302131109030f03070209240d060f05 69
    0x45070403001c00c2d0701c0d042c1b2012a848039640026800ca40301f4010702c0d0219041c08426a90005609424014480e0100c0c1100d500c1ea8041202181030100700000b424581d409019030507442000e56a1800b0514140015031130b421128220501c81071165001505003523002034103843c405403c090315940c42c0c034000300c07810b18554861005540006040003015141d405410014442c000d43c0c903003042a210047e8000145081080403211400000216403e410b8808801100b10101900140c0f60007841c03074580700c001120548000364200845d48500d14030078400c8448031501a8080d40c18101003d0003154000c10240c0344a907840e0001002812062003440f80000911503400e5441d40c03065880006800d12000404c003c41200c0c11100c1000507850311186403c40c040c4040c1e00040f858540101e14600307009000020740c241c414a42c4c9206680d01c000300a0200e14000c44107a41e46544207110309001600d64880e0078001c40400d4ad40040904000741d1607c1414420f440102d040031908100380103c0340c0c01c80b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 784182661 1250 784181411 784181443
    0x2130b0403060e1504050d120b090403020705040606260702071809060b1002150a0213030804060e0a1d0403030e1510060f020c0f0114040b04090b090f27 67
    0xc03050245038401c10801c42ca020407031404d03200e50720301034817101e882c0d04001600303009014101248098500656004000d82c40b001002840305040c10b003002951340d41c581c0200c5000b207203001408215103000c2c2a030b1404515060b428900d42069000c1010304104001d4113200c1544624603011400311280115505000010080015180040e05280044d101d042680d075009240d0340c04090900c907800b00d81d00000042400e004000c0c0d4580c0341c50326000380b04808110320b4540c01c80b0000710400009a0080080301c082d0b80d906003110740c0c00400c110b64003002c0d100d51074071800407074046400003d81255896100d8002d050004882115144e001c3c1004116402c4602e604010010002ca6411554144029000c68900b12094000038200030b90f84200c10300c4840d102d800409400074841c4e00c01c2281c00d40301e0440f01400354960b0365615041079903401901070b54015904001d05406903041c0303980e41034850070156074642c1040c5c41d03401c401600100801c00fa03800c3c08549262492503080204101d401e1096000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 784183911 1250 784182661 784182671
    0x103031205010f0e0a052701091419030c080405040617010606030527031909080120031302150318060a020a0e060a020724020c04090b070302130b040306 67
    0x2030510012500143c016001241403581c0600c0149903001c3c1032540030100322400600350702c03a03004a020112002c00c403130100d10000100c00c44c141c90706401022002e481041194408040b80d543c0340c0d1035130a200d041c228250400140b14021920440071031030158083c0c030203035140c56110b401103030584803103411151810b02400f0512031881c0f801d1203080c00924441c070b03003003009051007001c00140981d825052121106e030000d140300c034014144104c0d5210260406083e140c00c0000300040c02c16900303440380003000d500e0101103c001411700a2910b001d2401540d801d03280d551000c0d000c0001400c000401e03238202d22403501048580d00b1100045005640c200301c2d000b5406c00c51540e035440c24000402140aa40c018043c0b10b82080d04800014020301040b100369440724103000040f40b506007607500c400c003100c040d0312030b000c9819003107a0701503040e506503800d030368814044d003080c04107850300c07004018019415400000c0c4058440c2c1d018000c0c0d2800059a080d01d26a02c4460b400075420540055076070954030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 784185161 1250 784183911 784183937
    0x715050c0a110a08031515031e0108070b0d0c020c0316050f01211e0f0b270f06040207080304060b120f0c090408040806160320070f050f06010303 64
    0x456007000480b52080000d001426440d9103a000b02d002c05890039681020f403c0c01d1118903a01d00304d151451640c4203003039a40b28980b01e05032007111041c0028090300c0000220021603078240205282050310902c0803903520700901200e09900903d06901890700318011100a4074003544c081c86000c85540006e510801c0441c240010441d003c0d64050659060120042400b100c030034000c61801444c0c043e0b030b03000050146031000312420360040d18400c50342503440e0004002205a40341d1011203542d0055480078605510100c101c68507850107004940105904000a100400d0707e218041e8080d4000d440542400c0e02c43c0c0c2e61103d190401e5600b12501c54581c0007290300350820040003481c103080d181c000c01d482c02c1211b00a40d112031110904c075006128800c0050305004032481181c0c000c00420085a040f0301d00200315600207105410745500003410801a14a040002c10a90b1a40302800e82c6030361508059994040348a02d45078030441d82806494140c0d00819000d0043c54000e6000e0380300e4004082c92 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 784186411 1250 784185161 784185167
    0x31b02060403120b0a0308092106041e2102030d020a05030612010603030512070c0f05010b0414063006011203170403170405070b03190f0608030703050715050c0a 71
    0x1280d6071500c0400e00d044c6500312650340c1c0c070401c2d8084039002200b00d5034a42d15200450a10b40301c5441543c0320f559002400030303c035140000c4c0b103403013a80510342c80025440300606241c03444040540141c480240a1501140c480084842c82103044903801141d2230080712894a509a0f0841341b0064042000071003002994213000381c00c040500b441d07800804c95181103070342c09065402180351802c0740b0320751000081c051600070020045402e801c03a4101c580110385190007806850f0301d10110b8002c9040c04603101c000c03c1030b61103850294030010681c0705100d1022505401030500f80340e0380111a51540c80d4200220b0091212030b010381005441c100e42d03241d490030040c00d401c00411115809600c40c904000c0802e034010b80041200444c81400c0907640c5480c101245044000d4001840c840d000100f8880c1c158841c0300344846460743d0000a0100e010361415810807108075210f40c04441e002007101d000044d01c90002000600d1294102d40105540c0b40885130072600c0440e0940006140000c1072460780350 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 784187661 1250 784186411 784186427
    0x302070b010506041a030c091f020c0f090a18020d03110f031306050d02071b090e01051003030e0333090c031b040f0906320610031b02060403 62
    0x2901c0f600d141519154400e140340240e21110640b401c404000305003800c0070001161a2041c00500001d1401c0e22400000401811213202c50302512131480440c9882c10050b541d0781c0030321001007800c20550344070780c5403002400c01d1510107006030741c1d003008032001a528070107903204a038020783d1180307802d940c00c0c41d001e8645000034640e00308a61050004400c81100140c1900030b886580ca00562160001031400f00a0301035024020440c1305008814a50917840181c0d01d021a82401382c10301603292800c0c90f01d401c0380e03030654040300c5c8002480c4042c40032034013407280c80e0400c000c045c044404003900d031ba12039400c26040440400141c010b2074104241c40d50020103554100d65180d0241a460004400083e0b1300d100d01700344000300e03220807042041c1642e07840e4456882000c5a1500784510001460b011004040d45c0b818074402603050711406a814140b48440c4c220000c03078614070301c4251610700070000006c55001c1040c0400d41c0780e4150b00d03c0d10242d10501205a007240c1c00505041c03c1624010304049 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 784188911 1250 784187661 784187669
    0x209010b120403030b06040506121005010c0b011a0702090f040b070519181508010807090b100305040c0306020c0c030d0f05071403090d0c061b0f1b080d0302070b01 72
    0x56007030068061010000c807240390420307450700300064061020030200703d042c0915404168001004603a4410701d040060300c0b2440b13150281d4001c440d0a8a403001510764031105c2c180589144240801880040d50425403240448034225115040c020180d00141d0010400c41e170842d001c032000810300c020449480b100e00d030442d0039170419600708481c070700c0c0141c085002140c004040146a18108001c681058000c00181902103903c8489013001d1200be0251082071007803c50f0761160078030019900d18940308180411100070010714607070010030300071005010003030300a0311040030007100003002641c14030007070004e100c0000185c43c080c01c4c40345c10182000082c46031001803180720840400480c0d4814100e0341d01d260f02800c02da00c000860741d1200e143d1f004065006401a5608401a05010079118084201c82c85603440015070340c40c00e440c03041c3c80402030700700070321459041580e003000400503200e0000784820002c480760300707980d00c0c0d03800c518003503101e80210046540022002e043c0020400e002d0f0241c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 784190161 1250 784188911 784188929
    0x203070501180f06022212020a05030a0512070503040503031201140915010c140111041e05010f050a021908030603070902090306131403040806070e01020d09060f09031707020901 78
    0x124505849012001d0302c0e00fa0020a46580011102c126140d559400500c42296070511540c003034545000018034210180140d11600401200082c0c034900003540c003074055032003405064225802d0368264040c0e0001a01151180001e1002180540b0204050311a60280888c00c11103545004404076001c5c45134681d0754014018a000c21a0b458400c8085810801c02071804602c480141d0401950046072031640390250350030041c506104403400c1c0e018006503040300114020070400c503818a134594006225a40c0840c0c1300d0880810034a029401138040c0e108240141c0c5c129544046540503080500c0c0811034124001005000a03030904004041c0a04511141107140c034803040d0010f0b6880c03100401903080a10b2a010705000c01c4810282003a0703070340804040760317101d549130801030f5110102210f45c1d00004d81414010002984001294141c02d20143c4a4480b82ca081042c100c440d00c004034481c10a012442d03900100284480d54040c9620303010040380c0b03440d10080d104003c40050180c1c418410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 784191411 1250 784190161 784190201
    0x70801050f030607120906020d0509010509030310060c030306090c0201090c080703020d14030702270f04020d0204050c090613030c080d0815030a06050903030a1119051e0a0203070501 80
    0x1040e1000580c3c10341250345820080ba04a1280b0145006088010402403801d0700224174243e1038181508020300411114009000300c3d504d03014895130700d0008441842c5001010362080200d02c2c06950300540d61802490081010358813550920180e1f440640e0800c0180c2d51000316070f0600100580c008041d1003220041c040071803542e000600c9038a900800906280c40f049840d010030a42007003200c0e040c0d580988840604c0e01003103030388440b41164140b00052204e0000014403600c1c8040c1c49148107590091110544805030b03001d00c4001c0800034901605200c04112409082d540c21020703200c038031241c5411038030850035458404c5568000764840e4015503c903054520100b6008942998052030400e012802c41d440000041d00c1d003510310b03101034805894981071004521003c8000c5201d070f4008502407000a40300304018446100e40e00d4010041c81c80181c0f0680b000e849074004280c20a0791721000039901002c03083c003c1d200e41c86944a42c015910000b89101004001e004640c00c9030968515080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 784192661 1250 784191411 784191439
    0x14120d090b1803010516080901090209040305031e0c0901180807170309090709091b1b1a0903191b03121e0b010207050301271a0a0507080105 62
    0x1003582140640d807401640810040e07184940048800940600200240018103200645400b02e4900c040800c002405080000c2d500210502506040c2980a0003413411607440d9281180d044d040605184140c022800d01c101c141d07000015407038042d000542c0c19540c2c4802c201c1c00544041010000c00c021040306007003c004040000c01c4803c100c1d03040d4100c1840030542c02048509502c144100d041d84012410140301d842944000c86000b40d0f84007250070040c40e002c025000700118001804940040d070135207114444601150340045034540f09d242410100032101d03201e2240740200301d07884111940045607600741c2c2c0c0e14526100006051a042c00c0045228010b42d00342082c640343d001800380302000a00c0081c10711075500c58003440b90705002c1307518103c00c078207080f002401c016441c4038014801d4900c082500d28061144400c002801c4070540c00302040103088071141401f804d030580340385280c2d00b25200c18180301d60070544119903642000640d45003600b405040e0603010780115000f4031454030121 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 784193911 1250 784192661 784192667
    0x180c0307110708072706060504150c1104020f1c05040201020c240315100c0219060c15020c0609330708250305040204060b03090601030b06060d0614120d 67
    0x100940701010711100c2050380e40717000314040003e40d4032440341c41352611701c000031415400009807054400c0d012100d000c0c6064002c0881351030390800c6003d030448070040c29000c030520f8542c0c010302111110b02805410244180000d8480c250620245214661034000304411581c2c140403184c1481c60031690140411341d9902c00d0354402c400c0b01040500c04a000001c0b8200dc000031041c0e104030b00d002455141c1a02c40668000c12840701c40008070300441c0603002c02d4540b60b04101000c4241c95603a81d41d01807240040c0c80300107840d480f4622a42c1003581c00c110303c420300007041c03044078403855658004204101095030b4507600080d1100700303482d03824104010f54400005142e213540d0001d080e41f5003265691603845070050080d4044c1d200200311803030a04501074450b05504030b18803a500807101002620b03030f41c15002c0c0709031008035a0304155412500c010301c000b4855030075460700480d010701920b0800000903400000c41d03c3c61b03040310340462101259007041e0b150003c404c070191030300c0402410000128207805 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 784195161 1250 784193911 784193923
    0x50402030709140303070f1511031b0d02040e04031d09010302010507020108060f03030313031d03150c07020603040b091c1b1707030302130911030c09180c0307110708 73
    0xc108200c40f00200c80055408109a4104a400900070040c050561070b003502c1000c2010340742000301d800d009500324404181003c0d01d202d4001144500b1240500c51000401da40c00004c803c401141e0901010a0b41098000881d114900c2707034030340c04d800c14101805030001c0c15a072582c40307118512a000610050f40c0c080142c038013550382070070301c4125911440000341d440d25120002d25094440881001201d071000004400110b00a440d07015140c42c0441116401c5410600f10ba0b806501040380b2a01507055030701950760020028607254140703105039000645a91007a5801c0d00d10210100c14007001240500201e09000070400380c940c1c0805008402400f4881e0203040041d01001e4a1a0b81d02030121700e81501000519440381a96620620720380600290480c0000120501c1c1030b0780080341d51070301c500c540c0d54110700b2046007505690f43c2001b44107041e400182a16002008604070000851810740080e000b5083c1c0034082d0389078604100001c2c000741650706034402c15484a0002c001042c000302e00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 784196411 1250 784195161 784195169
    0x2030708190203071523090409032c031203040c2c161d04090b0405010c0e0102030a080408130b0a020a03030f060b030a0902030a050d08010501020709110904151208040f050402030709 80
    0x2921034003190084000650040c0c1c0216234000e824008140300b01541310070000b0411494000041c0d480740d5581099100003414a5003035011340c0400d02c190322400140c00503507070003031083c1044103040e40c54041c4a11484500030400c02075901c8071100b40302c4020b034900f45590001c032001c00134415604a500043c80d000f419809101c140101d1422000030ba100da400154080350405c22601b49404e241c40c200d4002c0c002102c5030800130300c0c1c1d1100c00d0600d45c4041b0403144640c45d0303030395140015221a204c2c0402c981c01a0040c0300050784002d00065144001009001401c81d50b4004d0f2650040e02c0c20050203980e16010745056072443d1002c00c0c004810b1100645e0b811040040300050070100f203102107490a070001d10b000e05580302d802e800304600c41e403004107a41070381d8080e803d45420a541c3d20303848060740c002001c0107100481c2484a50741504056111561480744e000c10610400d86d5204ca0403d503407146003040c2c8490500090502204c18054940380081800791403c51840c500168001d1281c145801 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 784197661 1250 784196411 784196447
    0x60f1b0503040f0f0509070c0b0f1e19050a060510050c010f0e030a0219031d190b040503250e04030509060d051f21020307081902030715 60
    0x14442889800c0050720301603e604501401001c2e01c4550445061055115139846400e010b03001403c0903119055152600384d00c00301030070507074031141010100d03035200606503000090301c500c440c050450801000d60252805144008505240e000c81030305550b00103106242c0306040200405c800e4544a40c080442d107130b14a401c07501e440305004003501414841511003001030805801060014021000707021244003502114011325101e042d00d0301442074544003501103082c4130002a0610303810024881c65003c01000240c11070b600e20101202240c03503030884101c04134082402c1c4040c0c02d08102d060010007007880340c1e16035009101c00b9108480da103801180d03081800c2001103810140260250b07002590003c141da500c0d809803046100040c201103401d00f1352848a6a00384222140d2080c0311020f5030342c2d0301100d420310202d40c0c0c00c04551041880c2c08036018811303800c000640d0079040c0201c240070341c98222031418030201030042510b040781a0f0014070761a40d642020030314a5800c000d038440b4201d8404 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 784198911 1250 784197661 784197707
    0x11509020c100203041110090f03080906310501050c07060302090a08150411040e0d030209010210050405070806060612011413090f0c0906050a05040908130e0907060f 73
    0x19400760a180d114015000748a00210500040081740f18010810724410740b0f4103004003006100440d407010a900c1081c1c03400444010a1012929150050003e140040c0485140c004541484490309500c3c1401105160061014010565250103884020074091901a0524000000d029220340302441441c040c540d00003800d00a03a240c006094004000840c1910100b400307400d185030000008440440340428a89082c1006d442e06100d14030401110300018000448034500580003036020107044c505603c03c07c0d803032154551407400303041e01c1503100300041c0546074a4280a68900700d0040c0c9090321918050008024104101020034119284507201049858040c40451401d074003030a09800c0483c20608a8014045d00032030084410b0321036184000035540e0b41503480d0886015000e05940040c801808103d1490070390044107507180203114032850039000c1300f01c3c0100c0c00303156802a9003469804c0200a10650180301d641c00030006400d054009841090009211121420041044030f00c40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 784200161 1250 784198911 784198927
    0x40b0126010536060f03060c0a082d0c0d24060e1c1e0803060907020309030c010c020414100905070c02010c0210230d110c03070b04050307060f1b0201150902 69
    0x20302260b42001c00d011b01507800505000e202480380782d00c1514400d01260440d004030b0b4400515a16444600d0305541803141801c601c00c2a46d00392010240000c008018140815103500f00d140c400c080f41060818014590003045802c0c0155040790b541c400c170f00703111741032074070014903101c46080e02c043c0b1030b2000b521499528a0702d40014142010060f101010320391848090030027000c440198000c50048880305d511b582d07011406c9039240304501c1405c0d0580c00086e40010705500078a200b0312110310051000c9002030f0420a2200f04401c00c60b4461114124000208100192032241300d401c1441481e089090310307800d0300042c0681300c8000001780541e60120000c00d00610565080341840081c1c00c0c8054001d2450290611a800c4907152034001d0b49003131484803081050000300c41001c02c00402440c1080c01a0326110100e0400810035078860204100c5403001601d28421400311311402c41c0300251303803284807489815402080c1c450300250f80c03502080c56580c01715031240000300c0d5054400580d0b038100e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 784201411 1250 784200161 784200169
    0x3090314030c1507170412030c020f0f0304031208060d0b060f04090302010501081905060c0927151008061003060e0f2a0702040b012601053606 63
    0x341d45001411400f07642c0180d2503022288001500494499171841088040101d1861081000741c50080c4004425020318070058001e4000d00b4015030340340150350382018003103400360411140d600d2200700f5410025042c01001f8a44008a241812034605a440341c540f28003c26084500282c0c0980071940a13000203241d555400000e585040b8040c5c81400120034a281c042d0291100b070081c41400e0061510160111210443c00b01606400500510b90383e00c03a14856211342d40b211100503009198189122071301000c0520041d0580c44080b02c19542e45425111030a1014540b85002e1090f035030300c2e0501c02070641c0701c2000c1da00004103c46c18900b10001d40760a8004001aa21244484001c2d100304a00c1d600040d01c504e110343d115000d41080340140011813280c04415080da00505d030030501002e40582041d502200908a041c1848521800c50810356071100ca03998a40384903446105006100d142440013402611011140e181142515041340d40484020030804604100c1075020008840d0383e2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 784202661 1250 784201411 784201417
    0x70c170403080c1b150706050705040f0320040b01053406090210030b09041202030f2206030203010f09050402040b0a08030c06061f031e0f1401050402070309031403 72
    0x15125009603070300c40c16858080d4541d4090384081c00040e0801c040c003019030511903a00d103d45e05200000500e0709000d99510b0008140c007612200402a0900011924150405c0300d1000307540602d00c8a403c603c82d000900c00c2d00c50702d402c01203000c1e9040012124060f60801c098840d040035a000c3d000c4054031400800d0103a800a0410703502031b82101c0c0c980818481c5a91201200034029518881c1c18004104242e080e1041c501c101e54010b50702000280100e204210030074840041031064928040e000e800700031440d0440e0780000101081c0210500d0050030100d01b80d001001035040c00c0d42103602d4047e400080620501c0381c081103644801c005821907845900c890000000146494003903a00c403503503580e8035001035084241034400e0b2000300d0b0243c58407040b025080e101c0c40c00c900d1a903105510f0220b0107003240c503401200c0800c0151001e14000510f0080d11490359800d000064401a40c6540354075544069202c0c40c0564410000c00c1c000c00c1d401a890004c0c0c2c0d4000038a003014214455030741745144 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 784203911 1250 784202661 784202663
    0x80d0f090602220906030b06010f030902060417060a141b041706061e060a0507050a1205090301060906140607150203151302091e01090305031303051203070c170403 72
    0x10320000e44001d003401031000c3c0400d841030000d909204682c840c18120200d998900014010000d1800040c802d58030920b002c030318152a92502203a5401694003094480d04640c1141c40c001d605d40080c00000720701000110303030010780d420080c0a01d90620707400c6d04030000098103191039440d0a44049040862000031140100b12404802c0062107180300313800d4407100240c400611464a040806c3c069070070016228461510042a0600d010410b06056501e90301084040703d10303025900722100410710b10101d03d80d03544d03483e1700d50990391040141010300f11031843d0006003d00345064030500151400c0c00340e240c1c210310251003507035450b411703401d10800f4150302c110b82140c00d074000000c00c600c00303084c50001a100b03c000c1d14401e0220845200348404c3e400381d40400747d0010b0b0340901118001c868812100000c10040c1000000240c0f04d483c0d1a065511103100a40780352041c41003041001020030402c01801d50003c83c040c250300705a84018814074a0b00e0010749010741e00340440b040110120304480c021 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 784205161 1250 784203911 784203923
    0x3070806100e0910090501120b0c0721020a05011803021903050c1f0b0d0308060d0c150203070c1410050d0f05010311010e0a14040f0209030a0f0c12080d0f09 69
    0x5891310b100b070190000264080e8260507414600001050740a10703895900882e44180c440442d41e4980000846641180005a484100f8031044481c100f40328849088030512541c0a0481044203007010350075248460202184084e881d2400e002095010a070300e40b0744c50700c0c503c0c0110002081d080446050096410b00d441500658000e0b401e00341d044800c41292000c03681c014401c440000d01000a0040702a10140124030900009040380c5040c42108015900c640400001d1503252803002c40c90f0100a4800005030b400051564180a16100400000c040e1204c21111542c02c100c04184d201040900b843e0a000c0081f918540044c1581c0203000a19000241005503607502d0800c0002d031016501d643d07010071058007106059007440e100c288180c8114507402c05211822506200040840c2c07240f24803d107a09011401e010b03034090080880d244c0c003405541d0a0303800c0904001a52030034a82c030000d460880b04400100050084040d9a8140041e000008840000410040240010300700041403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 784206411 1250 784205161 784205179
    0x3010b0405130e071e092c01063c0b09060c0708060709060816050316030209030307060e12190309020103090209070306081605060417101a040b0603070806100e 70
    0x400007440449503d0382c82080c400880c0d160f612103440044a10387d180c83c10703020740c000103989a40314522000d58819100c4500016503a0350303968091061369261424400c40400300000035400000c07815402168070342412600c1c00d59480c01c450b00000303100c1d41c01c00c18051003002c680751402d03810070b100c040b00030008a020744003c0c0c684404014210350050140901049011001c2050000d16000300c190484150704c400c0e181d6103481003141100002690003800f050f800300841e40e81c03900e00b4400b400c2114072901c004178400d980761515500301091741040c90341495050101c04003044004000c24480591802d00050f038051f2400100d002d0008854080d400041050900081c01da0607400031040700c10600c10741d0351401e024040d60036005818442c1c6d561261003804144026030302c10714040000701c0c41c1d10881c1c08441502c141d001c152210032211080d00200d140d103054407402c01d8000d070071509a007110040c1c034501e44107a02400200e0054081402003400d50103d58a141c05021010036141c0001c00d4800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 784207661 1250 784206411 784206419
    0x70506010605190e033f0405030d0221070213091b06090b09090c130f090b0f0117070201230a110a17090a021c060c0503010b0405130e07 60
    0x400c1d031150128024401200400619140c480c544c21518400b0040103000310300398002204080300741507907100c41c0c1000c0d40d4011440c1550001982c200c0310703052034040340e20b461030041050f007002d110410b118199007006010f50310714401145000c00410142003d181c580c04e0b107002154007404060131141c56149800144011b00c8204400c0c500140918954080e0b21030711554111806130032442456088041400342e01e56138617000d00c00f0f561120b0301902440c20102d01041c0f0709140225680450343e00d080002c41440140454002c0300000903042d03c4007080040030b03900080c8030307408060813004e589058a02240c0344610030741000c241016140340c17503003100c0780811804045400c1507902d60709291402600b0907002c80c800041d03403240075450702c0f0b00c000e420781c0a0500d0b41c03540c8000c2070704030240038284031440165243c07000d03034480c215404884034400e0564035091048441a0510006004080c801040480c0b000c00442c0c098800a440304000484c040c0f019101605200403080f0440c000c02c00081 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 784208911 1250 784207661 784207667
    0x30316350f1c14010b041406071b290405010801060c020112290301060b09012709020c2b030b03011404050307020109060f0c020f06070c0305010c12110d110705060106 73
    0xd0030503185110621a2a640da4170092880c0c4100e200340140c0060307030b401d00b003568609078015254040c01050548160b291166240b0700f040d000780c0101c2a16001c0000c0842d10701c44125001c140d641c90502c1240c6003d007050000303444150148211405c109505031400110b901c51441d524003030084040620030b04088501e0004122600d0799000d411035110420b01403146414050b143c103d692100f0303541d1030b00000d28011940c01401e0f403100c1d444203d03068020100080c07042c5501006250baa84016140c40310701010394108070959012108a00c0103003020764982071500b01c1c05c01c505410b410300149420004010074050226551404083c124002c2000244100071000b000c2d424400daa42014664484206482d02003071a0301510024000344d85110042c100300111201d00d900082032541449080d990391a41380840c0c1d0011121651100800d00e1a260080c03c240c2d41c06001e00740c00c2c0582c80c00310f010100140a44240360f1116512a003014940342c086a0803142003a410100b91915581c65113009 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 784210161 1250 784208911 784208921
    0x913051515010806100c170406020d03060816050907020c1207080706180302040f0902060a0905040c02070614160807050a0201122f09030316350f1c 65
    0x211410064400c5201c0301984940b480700d10a030001485003115609030741086502c2c0d074811400b00d652084071b1000c034040390340d02009800100300c241c3c000c0c40c03943c01d2640c0040c00d81c2c440c0c3e0300c00390a541c0a2448280c0b00640034110754282c03581581c002402d903494000880c5070071201025241c120300d0001802003c240f001c0f44c81c001351803045c022200119070300c0800301e402d00d40aa258602c001c40c8401c3c1800186065008803082c10300348580410700341410340009140c1e40c41800c0990220781010307420415814a03000d44015500d02d80003030500103192003006405020313410340e880d05580001600321003a003100c070500000e00e500322910a071208041c1c50030551310315486400780d0100302c0d45210305a03208158082d080904201d00d4000100c0100f060001c4050b07564050380300c000d6442030005001e00e450070400f078901c2c0c120394030b030006001000d41810607490100a08090f030001056000c2e1a45d007032030081c1c000c0d10590034010741d030b40d42020444540706400341c10f540010340401a000351355030110b40c0d005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 784211411 1250 784210161 784210171
    0x30e010f0e0a140f0d050a0c02060f030a0c140f09031e0313080c06040308161e02120303040305030112030e03070303200c03070612060504110307111b09130515 70
    0xf00200c3c80d0910400d541e01822090790029500250550203011b100b2005003035008150b0038034000540450f80080d000e6041441d04100b0200088108000f070b0303d85000d81680708072070381810041d140882804c000907201d40340000c05240000200800107031002c000c80e600c0d207200306855107202030240007030b82c0e22944401042c0030042c03441040801d0071070010890881656000302040c1c0f030507140d580c0b540400c2d004004520025040710b500b0b1404030b1074400b05601030200c01e01c103207942410300d0720400140740301030003d0044a900c10710800c00001d402404483c1910945034004401d043c00c0d240450f03004a81e060001e8140c010040b00004045d081030440050750882c07020341941d004402e001998038040040e1780c40d4035900c100c40401009025278004000c00b039841d000400d5554842002c40c0c26110348a50800b807a280000170400e8540c0d1194010b945842030070040d101501100082c40c0084442000383c62181c07084038042003203900124221715850781d1100c1554850030420081c940c4130501207407 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 784212661 1250 784211411 784211423
    0x408100c09080c03030909150a030302010c021b15090d081602090c130603200403110a0e01080a202d04060308030a02030a06180b0103110910030e010f0e0a 68
    0x1051800b40882e60480510b00a4021410302d000c0408200e45103c0c0a402240714541c200b10f849850340700c0d10044000b1718002c1d00049440000808001e2822456400030650101a20141b4590740d5441b030116603414411811103440302000d00000b003a0b01c0580c28000d00358000020070401c24650b46403401c82e001d008840e82c0710309039980320208049125224820003980b62180c0700f0f002032806035001d203141050241203489283c0c89500c90511a5106e82c100347c481c2404a010300c2e420b03140c0039039400007920544030003101c2075141441b225984d18011100820f081d80207801004051104036821448030801080b00c0000d00c015000420201d03400c690042100f6522022040c4a00741401510308a99210541d2450b590340c0d144070000035007000e00b80b05046603d13100d0014048201604044902002c000000794658a480c009400c445400500ca4440c00c0c00784400e6200c4d03601c600b61190842e0a509011442c01388020782c2500401091000500f014507054850490403400505c10a40300d110308 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 784213911 1250 784212661 784212677
    0x2090609040206030609041704031a010503010c0f0e060904110d1b17061f05041e050d150b0a120b0f0f07050a0c0c060837020c030408100c 61
    0x250510002000031035002e0341098082000c5402420704030742440d07000b80148a00328080b46009100d90310303503100d640203440600b0010404003144101c0e40d122401041d0450003000701c07140390700000d03041910030f840c040b05103e4619114403c0e078540a08a45110707070010001c00ca55880100c0718110b5801c10446900e0407840c05420100e8201510082c91160b051a29a411814443c0d503402075544001010340340c00c5a0506007a00c50f0016800107241d1001040c0c0718280c503a424a00c0f00d01074840c218000c40810b900102040040303881e024926000c07160400301c1401c1d401c2480c036907000942600d8880613000781400d4000200c2030400000f500440d071181c010341080785c6074540d183d00c0f5003600303903044800859880e010503207103070042c401007040884905029940c0182901c4400b40000258480c0700410035850030130200c0b40d100c400c49050200525805440152849030350001c270302e903541301e8448017540080c0d0a40510000c1055800500c2d128086682c0140e80011403c0980010749040004c20541 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 784215161 1250 784213911 784213921
    0xf010503042105180a060503012601090803011d010b071515030c0911031905090a060204030605010e16141305060d0b01030b090c0304020409020d0b040c03030f110601050402070c080604030c0209 85
    0x410f03407242186e00725680d203815a401d1220b55903045802000014094209510b03104115000303001380d4040600a2401d180c03298908201d00300046100b0400500c42c620140c0103120386001c01060b40c110640000304031101d4942c0b0401c02c0b000705203010a80c01614a07003400001000b81208000c0c042e180081010320103540c0030700e25001c1c0c0d0301013683e26003103480001210040030b0405520580d40000010102c42c0711800580341ca0080340c1c030030b41080c0c5115840d08018040314840700e1009403c144203041c41500c80021070343c01481c440c140e025080900c04009506a080e0f100c40f01c503c2c01410000300300c159100c402c000c2c1c01000344102d01c000c0d07020030304206040b800d0746804130b1603500c5102290704540c0b441e40c946d42044000d2446040480e4401c4840c0b11140c00301d81410840c40c8601d2003a8600801035086040c09480f00421201c0b500c200001141c003081407410100e1158110746050b1070250302c0d0380861824802108a075005405184074010420050580c00b00c47d0000da00d0003a58007000f26211 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 784216411 1250 784215161 784215169
    0x100e09010f0e0a150207030c0f0803041a04020d030c020a090c09170d08041101050d181416030318240e030105130b060d0c0627050f01050304210518 65
    0x10348500642004440d520501c80300482c2e800406c03c0c00d101e07242c4030401900503518008020416130099030180e41c00320030041041070400c806540ba88410607003035010700d0b05600299602c51041002010006084000302c2151500701103c000303418501c1060280344070080006003064003e111b021580c0192400c2003207440b401140c01d07a5400803664881c1401c0c0d03950380320f800c6140e030380704081810484104200d4500440900c1640000100301d14018010203050a00c3d04081e8071050300c0703040c150007000ca90400c4000008401c011250f05041180f402040c400f802418035130f480d8400414040075070440708000340b1041204d0048040b5440b0b440b16014038105040c01c07a0340403a41c204040500811170f40204c2c400c10710030b0754040c1c4000c0101d0100f03a501d0f0745040b48201c450703000b0400300e2280c020100f0307400021000440020460140b4105451503c00000c0e5407400450ba12414450300002003010701102200041b120882d9a000550403458010000c1c0b80781e10100d560354001070a103950b501a031070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 784217661 1250 784216411 784216423
    0x901090b0a081605070221062503110c01020301120201110a05120d0b0a080d090803071208041511090a0605030f06010e04200409060b0a1205100e09010f0e 68
    0x4615941c40c01d02da80d40306455201d00ca0741d44903500a006007401280016070700c1c8a41d65840c10b03512440a01d0115802c103803a45000806040c400030118001c004601085191503c13042807001c524012568540e51350a85c64644115868440700354000400400c1d200700e40800d03407442d140300782e96001c0582e040184803a04c802c00110020f00e2070f00811404030442c10ba801c00f806031010074038000079a0454802c0000c4524016900c00d10841e0850030f5030000064100408200612000019500d00140360b903406442000c0661108148a65030000c2014040501e104007182c086807c0c0400510b00c11201303640c2c46030054203089114100541e40499882e1040040d83e024125940a40d0400d480c0e8800646100804801c4260050703a5035410909506808005180da80545110103079180d0a1080c041c00b5154281c00c5849045820441c0c0340340c15500513400b85d01d20840d02e00000d403d03100c0350188040400e80c0e0b800700b00d0301c41d8950b0600c91403450651081d00b000b05600c000f085400c3c1204940d0391140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 784218911 1250 784217661 784217677
    0x515150901081c0518191503050a0b030d0503011517010e090c0109060806010c050f07090509071d0f0402031504030206190501080a0f150207031e050f18040b03120901090b 75
    0x1001240c00c0c20340c2c46c10030600c50320b80e901d00070304829001a00c0b0f26032112811072608005d00001d0716041031201c0950640314040e1701c0d54090300a004c08820741034000c2d00c2d038801032080452001c00d148100d1026481940350030b21a00800c0200c3c4c2c000e51350f6940401183c1801d0780c49034890b020b40907820895600031051141110b000c0d4603002560360752a001514080f81310f08003a2190300486d008401158418840c04000d0724aa840c00940b80c10318296035807500129070051402c44040d9408800c95070b03509940240c0c0b00c580d043d50004c10350380d00d101003810b10380c03c5204180001d88107020711041540114605210b000c00c0380328403040d4250146048d0075250288100d00d0b45410070a814004641d001c408041c40700d0080380403005003105204400100e0b4018001900024226418006000c0ca07500d42c00f11480e505240060070b2104240c000d0030701d8070910904000603803500d401e0301c0158a540d01310301c40140e002401d50b0014402070408520681c48450028002101d015011600c0004102528190 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 784220161 1250 784218911 784218937
    0x914070f14100503061f0906020c03010203040b1902070203060f01050f0409030905010c081b060103170306090628180609180807051e070e06030a0515150901081c05 72
    0x300d0742e94005845560002d041c0030f80200c038510342c02e03160303101801c80059508140c5d560700040b640b0b400303c001e041c05030030444030340700e41d00400c14030000c80c1e00c41e20250340002d84840203074607201c4200310141c028400d0010080d01800b0b51800c01c1158415008802c1c100e0364151498060b10303200c01c0c108000c81d641c09d5002000f2030341c0c007141442254481e2241d083d04030711444010345010380550340003107102101030200800b940600014010040c400041403d00c4680d04000c605600301034000500c038020080c0484d0103800a100000b60a680d2441c0d021142240329044085440e01da006d00c045640103002d400c83c0c440d0400000152081191145a1000c8051080e4410740d1489039102100356010071010385051140f210340091480690701d190b107001080000500c203881c6000c8403844180303002421140300741c01c80c92009020070070204000c480041d0038420800b041c1c0c0d1303007602600100c60000b03400b40c00c02412000410b00c02c20000702e88210f0b000b1300c8641d0110a02c4030200712000c0c4140c0700e0400c18 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 784221411 1250 784220161 784220179
    0x170702150c0a090f03060605010311190c0c0b19020705060705030304080d06080f010219031802040903140d06030b06030c0a0e06030309270603060c070b09010914070f14 74
    0x410400c18002d80350103500c614040e04000d588140c0503110314500d800c140c42c0290741d031130200480e40c0c15214590410403100c0752581001c4d03880c03848944141c84050070302d052006411882d42082800d0050f070014241d0181025150769501c01c1d440360b050f4600840d40c025201303298022619140080036108030950080040d45940e407180d986d9811500b040c1440c010b440d40324400031071744210034841c03615048458000161170303840c9460040704100c9806040e50a151920080950151101c614006099010707180030482d000249004c684040514010740c0303503904c002c592400403803030b95084482128000d194000b02c6842da20101600c03101e01a06060744661140010400d400422225940c0200e000b0140d0703090132036000105152080c4002d103801c01031044d461044140803041c5030b00cdc0c1c100d036054008040d64a0711050b600344512030340704c015041c44800d10005800150035000003440540c0109002c08102ca0f07010202e80d2113055004520030110900f0010503404041040c00c017201000604c1006 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 784222661 1250 784221411 784221421
    0x6080c0f09100b1b01050c0d151206051306110d0608030903030a2a0609051e1f060b0a02071802071e062a0306060c201f17070215 57
    0x5140c0d8024440c003052000f0300c800310540c002c4c0a00c41d8500c41c0d8072500965a4030050b030700e5143c00320ba41542c40182c40880c4010244564620300d610305203601c0d03200c040050f403521010840c0c0a1090301d1403004192a05006407608242003060143c00ca90801c400180840d544460144e03031640500302105405610511405005620843c142c3e2040003828446003440000d40c1c81c81518074591100c00e481d42e5131038a0303414041080822000c00c4150560320002206501c40840c04e40f0b9001109190002111800d18500ca042243c1d00440060407480c004a5540c1c0d600c1601946544180c45810700301500c40d03120b8000c4150b01d000b02c40e00b280c3c2c00031000c448644445260b0300d0102600d2001c2e02d55540c0e03400c01d000c10310008240262140c0e045452a0a48010018000d080e10303a6504800d08000810070001c0c0010000921008520441d4000c0310b40c0f5102240814005c0040d1a0468007103102440d252421680104000b0403001402a005140d80d46190080e66201d8503c11200c04848081c80014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 784223911 1250 784222661 784222679
    0x14060306030d0c0f060f060f1418360601061103040b1b1e0609121e1c0204030203061024021905010204140904210507020406080c0f0910 60
    0x702d81504c04d55440c01310001a032214000c842002c00d03a0741c02d01e0b58070384c014041c8240c550881d50040480403150018116010003080680e2803a083d07403070790040c19402081d078980428510020980f00d02600200b01c01c01c00d012958094031055079a00c0c280107910011800e640b007203840007000c0d114980110300d0076107031071540122035200d500e20441c1c00d094802c0b1a08008410b02603490400425408044001100b9090908003c0042c048410641c40700c0051210000d6007070990300c0410600c0d40802c4a205519081d1a00e8414490031f4402000303ca00e1030f14030300c0308903405401501d0007075044550f0f550741c01d10702c41400e0029001d5500447c40185550b140d21030041c40c4000106100d10545100103000b015170702c05e00003c00c038200c581d40d4000c102800b1980880a54500d0300c4003c40d5440e03582e09203500c0ea40c00c00c5180440c100c00b80d901032044010000d010300d040b6207002d43d02030f20400c050b41e942c0c02003070b0312002000c482920400010340d542c8840c1c80c106c0b6038640140112040c0d110800d10f024181 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 784225161 1250 784223911 784223927
    0x2d050601020307032a0809030d0e01022104080610180507052208070f06080a1a10020a1a0403032004050f03070b041707080a1a060d1b14060306030d 65
    0x2007420500ca4a20804252a107510841659105000f040c0d26406207d040606101c54007a900d010404109540c1c452a07900081d03074001d28038a10001c41003000507c60304080c911460f00305942501c031301c00c10302110540c0d80c4601d004541d0110001100e10701101c210030280c03403098911038000f4200344520101c03016180c1c0e00d860000c0c41031004003070f26552030035140d0512145511841ca00d12000e40308100d000c4c1c20800032640003070803c1040002c032034040e0b424101c264103404414003a014149034822014020001c204e13019412620303000e584280c40308180136881007110b0403000641440c0101d80701001015804605401c0301241c039041030b08000c1170280c043c16491040368180320700003000916000810080003c1c1048100769004d400304920b02c5485c242d0b840c0e12031000303a400342e44041d021504640348561003001d51010110191500b02c0041d00003c02500d003e09480080502c5510803800401c843c01114000002d0a800e02c1c1c00304100002408102c403502d4240e00003400340482140300d6850 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 784226411 1250 784225161 784225187
    0x204091b2904050f041e02090f030f1005220f12180e060604090515100f080417040b0a2a241407090302130501061b030e042d05060102030703 62
    0x1000030603400d04031110107180b0346c010062483e540e0014540c00b10742420b00050300900390650080c246142c0201500f5950340c10001c0c080415a13890010540e0070081c00d4074070445811103000c00071109064208020000520a003c0350004040d4045c41160b42c01801c160650028070700c0c1c0542c4883c9032403160440e080d070040206074413910402c00440c00016034070901380206e00c465011005603070381c0410300408501e0b049194041c0140c1c03114400a00b03600c000440c6d0720a42c44001c4554034030f22801e04045a01403070f000131450640111328190fa685e40003d20281d00c03503200082c04e2010b0324a04e150740420355503a1002c0d0807039400008510310341c070034400841c255000b815000103041c1205111007501442c140c41c544009010154208290b15244401c02088480d1440801c1154075000e4040c0105c20807694155054205100080c00d241c02050343c0300e42c00320090024490700103500e460380c1c0e140b0f02c51002001d000c5800c0956081e600102c0c85100d10601060700190f190001688041d21454880a5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 784227661 1250 784226411 784226419
    0x3041401200c0c041b050a021f020c0c01080106020a08071a01032006030c09100c150b130b060f03190c0c02090609060109060c0204091b2904050f 64
    0x201405100068002000705041d000150b9190081116801d05012080c542c061181c3d04111a222002e0300b115140360310201c041c2803195940d003d000041c1e01300b4210241d5500305c0e4030152010541450f980e0001c1c07200d0f0301d00005450421606d100151800d0100f030044100681c0b02c61068000202e0941c028068070b4050960540700302d10340107004034440026082142c43c0d01c9100d14040341c1c071050381e46030050118101d600301e041d480e010800312828041c0704511442000182014100c490040b141c1400d81600300080200c0c0c010f08400440291454000a0340501c40740b070180d01000c0168402c04003003a10061041e0b28050254034500030700d0b0800707003174909800901140c4c0100c02c076280c4240c0e2151500e40e2120729103441c803401041343d8024020001030281e446d030010003042e80e0703015281c081580c58908105c4881c1203140007040060409100003820305000c0c0c01403040001c1001e885d84101c560300c2503c00c00109000e68110000c600300b02e032074000e56000303101c18085440c040340c1760b90607030101030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 784228911 1250 784227661 784227671
    0x510110d0228020c010206100506070f0f0b0901020c0f16090213150f1b02090a050714070f0c050d050c0114090d0c0905060409050a06090317070816030e0303041401 72
    0x8a10240b055101884200c05130f44120710071501940c051100960180059412110b005e00d00301c08617032140b050040050a88905803131060070000e24800040040350024807010052400484c102c1c000d501c8a80003080c10310540d2200b400d040000201d0395003a08961450b0041c481c5081c942202135088003140c0038858442230004102000703140000b00e00c60b9003640d00c41000b40c0340c0c07500203804c21804002c07030807240c40520a000051788540b00c0d50391704420494800151541c80c410300b160100039441c0120700742e09002503450103002c6038044007203a1b2380c00782d10301b451000c1d035510802030200701d00300c030041807600000b5000d00303958040c0c042d800c0d441944181c0c2c58504002080050b41c550050304003180c80d1404600280544007075445031a40c003ea0965081040c420729440f000e60340d103403840006180c56240e11100741054410b1481d180c0c0c0860100c5120300f5801c004501034121001291024030f204400103540c1d04e40780c46030250344a16001c0070082d600d1501c86031907030343c22046d07494540602c0e50340351 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 784230161 1250 784228911 784228957
    0xc0a060b03011b0306030303060b09060702010c1b17010b010c05100504030207051002100b03030c150a0b0415030501050604091716050d0f180602030901200a0308040510110d02 77
    0x2683c0d11100904165400051303403410342c607026007120400e411507910080180140784a948880040310103080c2c0900304a01189a03610704008540d8001a200400401e200000640c1410308000800c070b49898400074000345403600c00456151554050141c51350703125182c0340d9a81d200035406030741c019000f0700c169101c1d292a800440d54501c01d2203094001030703203c0d00740200c0026491003030701e00008084028510b481d900c0d4074107070b94908802c1e00c42c06030b10581d0404109242c100e0340c80b0300344902c0c0183c4140010100000d0309440183c03035200035201c550a000c009140c83c1351602c560360301c0d55444040700f03034140b1010601030000d03000403003021003021424000e8004913900300070481440c0748681d503485d079105151000505048070500d1350401c000a1480900c1340c41d03000b000741d68507001c0a18000004002c0041003840c0b101c0c0f9881030628501900c41d1340c800f03141e40074042620550189080741d0351090b004e070b0444215400110503c1c00e1000922042250305001c3d0000c00126011103941010b201003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 784231411 1250 784230161 784230191
    0x90b16051e070615050102030a030b040b1f02190b0412121508070b040f0e060d0803090a14030306010806010503060a05041404052a010509010908032d0c0a060b0301 72
    0x508600c0201c07036040459904200009401207440a5015800010340c4030301e8070740041c0d80d03801741c2400541419151a00c0c0c4d074158407180d214555046c40107012545103078503145120140c007103600700e0718018098484119800041040c0e05000d95a210701c05440d29503480d1103410241c0c0c4201749680400007a0001c030307015540c1d6401003030844110f83c02d03190700d51442c00323085070300e040c3c05039100b541300000c203100802601814140780401c0315068801542c00da074a5100249032030401c020001c040702404010720070000400180018541d12682040c004000c00c5054a90ba0340411226540020204400580e065200c2d802860b0000006010000000c2c2ca40000400366040f075250340d45401046c20030042400003c200514503024558421019503100181d80b809401000b805103041c04000503911225910521700c900c010084041565200d10920025260303a90341c141041201d20300454912050004002c03c41d090481d10f0700c020040c084807075540174041d0121034001031b410b56865030211604c0207 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 784232661 1250 784231411 784231447
    0x3070c021e03060a0c0914010c0212060a050a060e041104110f030f0609040515040206040e01090b1201050c1b030c030723060105281e050112090b1605 66
    0x60240c0e849400311500c0050601c0c110004104021140c05d05244c800c285400c002030509a400b07644000a445000e500181c030300d9080c080c00207400c500e10048080030340901003002401205007000038411902ca880075039060310194082c028035500403a0105000441000c6440070224006d00b002c0344956144c100948036800145085200c1c002c00000c2003030b0650b0041c00964400c8040b1140a690f0500fa142c5c4c503694800c5001006500c0365210118040d9510501610000d00704c060544c0308540e100c40146015140c40c0c504940141101d65014051880601800d442103281c0e140b0f850904100303507110ba00044e600600280240400c101d0f81940500600040034418040d40e004042003141e050030b26480e2450b00d00140f96608040f005004956425800d040c00b40d0a4443c10500f02d500003c05042202960b44059080c0b00e10383e03024070b07801d203800d074180303044402c240c8511031803100c2c1e06a01e1060311000280180000b04180024001c83c3e550440d8000959980c60464101103410140280ea01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 784233911 1250 784232661 784232689
    0xf030f06060f141204080a0c0501061d0901090b13020a18091401020406050d020f0d05010303200f06130c09060608060a0b0909162715020a110603070c02 67
    0x41c1d841c5010a44294202d030418400c01c41d15030880d45070002000e140c00200c0c0c4e01400041601000040d00c145044c814100f188480741c12400801c5010344d510720f0322520b150040100c50b2282024000108826410322602090030303049061812039a5888090301d91502c00031008076072101e44003074041040982c0c1100c0002c0c4200713414000130095140c0c24141086052030305041e180360f0040200b440b840358007a042e070340d14a034044409131b1194040e40840003d8001c07000d818411510b80000001819404020f8150908800b507010a5035a002190f5584034030340740703144911503030020000c40e1607043d03d0240600305500134407072a00c000d0307100e204810030313100240c0c04038000403003510510059240c00e80ca40b41c001c04080e54002e1a044011006c10440c060043c0060750070041004002c002c0e1b80a0311145032100020304059811044125480d030400e4018020034050700c00a242003201e49000140354814140c01c03080c8602614011400c00c0056800109001c0c00c02120710611001a11020441d000780 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 784235161 1250 784233911 784233917
    0x5070c0320100504030323120114040204081b0d1406091501030f020d08090409050102180108010503070b030406110a0e0f06180607110d0308100608160f030f0606 71
    0x11456140209001680315441c0c41100b000070101c604581090460301201c3c0d040c1054400307504100504030803e242d8030145a407600f40081c1c030804042c10000c0c0607058402501075554200082d40a110880c0120300400720725034015038200f80f00a802d0206001800d1000b0910011450283d450b100d2204484865401503403180041c41005442030000039290640418900180c0d07140d5126120010070a00c8064000e5500800c46000e00c020201141c44c0d101014205001c00d1701c0c6440c1c507034001e40c4660490000081900850b00303031580700d0b140a5041703c100500400d4500c3c00c14402e141030307601c0a0000c507515079880460350f03040d003846400340104258584480300841644002d0111419180c0d00036841080c00b00722983c054a10140149500c1d0b44c280c3d1080e0301d580f02132401309108220103190550103652074844c1710070540c1c0a107016210343d5201659608031650341e00280c5000c1419528501c10201c4000501d0556108a402804041c0070349408a0034950103038490341200c4181e001130b800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 784236411 1250 784235161 784235183
    0x10e120a050f0c041104060e0111030f0403170a0c08033309070e09011203020c0a0902070c170c0904030e191508010503100c02031b0a0309170a0b0705070c03 69
    0x104000030f0256041c03080043d9000d0100100c00010f03808144105e01a110501405140144090f41b081d10001c10f101308803400c890341c076075003106482c40d15041488122140c80c1504201a611a91041070307511084494072800b50800305a07503002c8040e04010324a8418494085072207040c0d1000c54010904050460040e68140c04000240304010b0b45c003c216009101c030083d140c3d02036403144400300d411948400d034101950313012031a08900344400b00348031650084a00d00c2c0031800f2500740e03004083ca54820f125010115640e880c0509544070700340311a0305240c00405d4012000d050891704143d00c18880e01e803150b4038641131700c00500200903002000c0c0c2d00c1038400000f4440d030112800303840e0302c114450034800115894100002d41d501d0800185100c01c41d19100303450800d1b8001c105403050200e030100200b00c003103400700199075160b40d44c00341900040ea003010000b40e10003100030f4484580c103a6201a2081ca9000d4403071090451001e8441402c004040003040b0108021f0144000070b14030031008015 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 784237661 1250 784236411 784236433
    0x30209040f1b150e030c06400503070807090203060d080a080a0614090a020d0605150d05060402072604180501032123070c030b09100614010e120a05 65
    0x44500e156400507000e00090504100d19070345c001440c0c0701e2400c401c03501d103550390491610484a40385180884090145940c12002d003c0048020064002d04a01d2480d20b58a1303440c02019501c03225849550070f50b4010034000c3c8007610b00d58009582c0100301402c0c80d0100f0a299503004001d50001b5a034000088041f070900c16528002d01826000300b075152401c00700420304d40e001602609020b008868184e5002480301d40910807500981c000b008002c14168003c0c407031004c4034007a64026650501558501400103c8524040c400d9505483d0410300761240d00b10071070f65909800904880c0f00000720814040081d169000d0004d1040c10f01d12294003040d07039451071400c510b2492800ba40c0410403031403000800141c60f8083c20003010b0110405040d02c0741d0b1101786075000c5500c110b41015048200c4058040184034000e13102600820a200845200c0030070108203004543d82c41c040d500740b0358020351000782030398400d01c4111340090b8010119031300078076490402440d2243c000c0341154580c0080394201 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 784238911 1250 784237661 784237679
    0xa09030b01180e03031509060414130b0906010e0402010c030201060308130e10030f0b1005130603121817070e1e010e0c0403060e25090b0415030209040f1b 68
    0x5010020350004c606606100e440381454000c4603100d14010780455000610903500c41e00b1040b007803928130b40305400e00d041c0a84002440101801e0548520140001190f165000000e030a4101c0b0001604d1003455111030f40119143e0900e10b00a80866485403004401708410030000c0c00540c90401403141c0a511306111913402210007000d20b800012122410804030b185100500c502903030107044401d196460303418480d1072485580005402191181a40d0a00b6902e50301000580303005076010143d51141d031108035440480104c88404c441c8000f041000000e200d12050450820744000341c0b1074240e1150b0b580001c0d041c089640d0100130a65101e41c1c2201c00624510034054480683d03c41d41d40d1500c20000a85846144030040c500c82c0d0f109036615110b00188a02d014990880502000d080702660344c06e10050700320300680611518110020f201c0c4c0c9030178030458075910090420022090310f56002c0201142d80104241c6100001c416140c00281031354181184040d006d03500313014942e0800180c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 784240161 1250 784238911 784238921
    0x1c020415020307080a0305180304080307150b0a030b07110303090a060c0512040803040804121a150a0320030706030c09050108090c150d0903020c100f0807050a09030b0118 75
    0x424250b40081003444040fa0381c4008884400155080c003140d030762140340b1000081016107000030f940c0d00021602048400c0017200905401d80910f008000b481d070800065000c44200210b42507001c0e100030800c1002800d001c0c80d01d68490741e0303401c02c1600000104000b5003158011100d00d0019005900c2c00d404210f01803183c0026800c00d4540181480d10b1024a042440c002401c0581165004000102086000b0301101c02400c0000000000b100e080d01e4504d0400d041c0d40914070400c1112000240000000d1094183c080c20082039240003a2840d101c0d00c91808070440b910081e664840039555080c1c03410052a07000306940c0c5c0c0e00080b0441d07105c0d0024041100380d0440c41c100318041062000c0480001070305403103e102110061581e044400020000340b149848540d2007900702101c9205058000c2001c40d040a0241d40e0f0011454084200300d400d0441203402001283d14900032a002d540300b42e01900b0b0404490034078541c0f8076241c0c3c40d0f58220301c909901c1000020b201d042d002400810074010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 784241411 1250 784240161 784240199
    0x2090a0f15081b0c0703020d06020702120d0f0e040608030a2c010c060f15170f0109030503011208090d0804180903051e0403020a08060601021c0905010806061c0204 72
    0x101d1181d03070500e5100308030f0070004a0f0915464020118a00300e01c0301d018008000115401800322019004500c0c018000e5044008164424500c85028141c03040000c5411556003600e6521714602d60f11919040e40e1801090009541040d03803044040f6a0300c20420040103040e04c030351180c0002d200031000f82d222800750728149001072264190a000141d0b0040e01f074a03282e40d441000410307610760a44000009203044107450840c84117a480026a03040e04211208008075031406451a0300080c000301401d8a001005c010001401007004000800ca50040790494601c1344900c030340f80c4940400014841c02402e8810758202d880060204083c0340c500300c035055010350a42d020300804c801510084c09030300483c2d4080c86481c030001030704030b966003680d82160003565005101c0440c0c0e540307034541c140d80c0e41030450b0618058400d10640800c2088119000e5450f44096611020306a04220044400c1c0201504454121505210300a124107800b048a07211050038940182c40b6450030382c0c0d0707410351003403010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 784242661 1250 784241411 784241417
    0x18031605010512091603140c091509060a03150209040c080f04120c06140406060b190c150207050f0d210e070305031903061401120f02090a0f15 63
    0x110821490341c1241c2500c803650190300c0e006103180d0ba01318140d410500c016002101c1d28660081c0403080003240d80407000b66481600407101c0440c2c0d4a4180182e001c01034442054012801c0c0180149142034107030640e0200c000790001740929941c3c7e0315010000c004000e01c0301101e8020550707070240c0c105841000190641c03460710843c41e040c6081002000d004c00342000d0040e000400030260014040c1d0702007208150304c103004115984003800c404d00500c005440403140c8038107041c1c002851214038006c0d00c10000c440d4840740803060001c1d0040da000c9152113000c41c1c03212403400303d00760982c0d440d1002e00a1540030f0780151a00d03a8200c3d010900340b80c84445544280040f480c80c1401004045000130b0000740c45450028585140044880c034040751540000d02920001840c8080f40c3c0700e010310000d84c01d400b41c5040c015541c8550580208282c039081c0280001c04000451000c801c2c11707000040c0c00c001e5070390010700d48a10364000c5507040301c0301e8111040c0e40340301d028100a4242c01001c02c003041a0310349 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 784243911 1250 784242661 784242703
    0xe0705090405071b0f110d03170610050418060e09030307091e09050603120f1210240c0b150102060c0c15090106090c030b100c112101021803 62
    0x484c030500000d0000b10301070011407480c06032504100e6001004501001d00811014492a003460001c3c0340c003200300309810f8140a2131011664a040100c1004402686a19001e00303150828014981035400040764041c11a140d0000003004112004428010304803e00034545d03d00d403d44019081c00b00b158072866020383c19030144601200002200c9054699140d0041a41e07141c1c0d5001a1400340001074454441c480000c94036402950031004089030300c03000200c0c01440d0b4442101d061031040b544200c0c21414010000d03511111a22079070b41d042032840d414110303402c103455151040504004c441115150b4401c8108546640e0100034940e03001007100e8101d4038258895403c9500c500704c1d4404126a42c44910114000303040a41005025000b0014100240140713240010302501003120b80030300800c0a1000c802d4110301c0307000300745e02c80c5810600741d016490002040c0325110424003030140640c0501039404680c980207000030802207404440140c0b4801c540810141400751903500345005160071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 784245161 1250 784243911 784243937
    0xa090e161b0311030c0106030302060c070203120901032a02190203030403030c03020f0303040b060f010507032a0507030501020306011103070b0118021614070801020a09051203040e070509040507 85
    0x310182401c290714001062149141d1405840400700c6003640ca00703e00010420300c100d00d205601c2142181d0181e401c0b62140e8a031456044aa03221380741010303416820100403402498410402003080000c10725001071008030b10881000702c04480c4491506100d030042d0004021681041040704003034002d10000319040c107543c0000e69a1050348801400c0c00f240c00303450400c0c50700900078040d4004105095039628901460025400f900c01c03510140f06040d009001c0885512840c161340000340e143d129200807070740340c005020f524190300c5100c0a01d003000c0e140d410001042448064001c6114600140c2c0701d08043d400504400f22182001182c2d520911880380030034850b0356003504450007010f100300c28003030f503910344e074040d2003808540441c90040d0240c0200304101c890380070b07800980350010340b4011134603690800d0903031107032888101c00640310100900c100e14000d038550700d07103650b690112494650b03201480d6100740b40850328540400c0700490191038a08150045582c0030320355282c08101440c103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 784246411 1250 784245161 784245167
    0x17160c0b0f040302090c0f18031b060a18170f0c0609030a03030506010318050a200f12160f06090b0901090e1009110703170103052e020a090e16 63
    0x156200c041e10640c07001d80071450750403541080b07d0443c40001400d40c0c0d030f01c0302400326221140e0f0b40325495009200300d04a0b20850520004103021030703000140448d240100c2c8400c104c560217188510f10f0341510f2100400101c00f40c02c100091100c4500401500303a482c41c8191403420104414000e41c000e2034104004460390b40d02180c10185da070b5050a0014880e12210012001046080010207072100580031000a00c0310009004100c103200d0a080c40c240c6005d42c400141901c03030500d2803a00110862444240c500e00500f84e0300c41c4012a42c1100c100d28980e40343c00050010a0f4002a4080f048100034002c1c5a40816090050000603816610300300585000920640d0b41d441769400c0c005039607000c41c021440418040e401440b056a0a0200c600f40001c110510b40c010f0030120301040481c807520100c04400654281241c0e0884007800d20310141c2001166140200030038900c0505028040440c4182d452011742030000d040e89d00d44628500340381d0000819100903140d0184c00c0c2540c400000510740c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 784247661 1250 784246411 784246417
    0x11040c091a0721230c0d09080d0c02060909070c12030c05090f0d0b0106080105131413020604090c021501060e0a030206090a090915110c0c0d17160c0b0f 67
    0x74a43c40f032160311294980003110103200c44503802c1130b0714240111a460200704c4101070401000680c059170903440d20401d0070380303050000340704181d40e40d048a1400311400b80900201902c2d240007070641403414403041d0000e01c060780c04a8030314003c80c0c200d140c80c1081c0100602c12000c0701d00a401c0c20800040d40d00f4019009001d007118851113104410300010141e151141384020a17544142d405a90356107441c4098801202406424001c01c2c1d03180c1e150110781c4080c01807462000900300c01c40c1d801c2d100c0e459062155000a00700f40d17006401044001a5040588591140040d03950301602c111842010500c1c124901070344002c003042300e035040d8002c0c142e4428401348216581151000c0c0c3c0d1306003200c00724035803080316401321050902d0549802c0a1010b06c0301603101400e103c403002c000103000c180c02c2012500030418140015801a4503441c5142000840481e400340a40100c225011002c40072520503400342070b05074075201c00c0b40d801c00d0400c40c440400e100070306100101281003441000e2020340c2c0780 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 784248911 1250 784247661 784247693
    0xb090a0819050f0304060e0d0212070609020103020c030c0a03140c0c0906040f0f0f0c1814031501090e07050937111c0606050301030f11040c091a07 65
    0x5a484880d81c01d041c010011550354402c4410425101d1500d0b0415600034480300204038180d01414000f034a1543c40840d0f403200b201e60b5034035901d09050080d12030100414190030102d051503420003e031130807000104054505030005200a0662520501e0014401661443d807080302d20020310901c188000d000c1804101810b09990040b100d03030700d444c00100501141c42000403514036149100c10320840364bc000e40c01e500703560780c424802103812600441d0b5101c8060300d403000c400c0e01400244000c2200c0700152034076035401000c842140b49550501c01201800b030b8440349005644440280031510103202c07100c010401180c01450a241c07001c00f40141c121044103c981d510300502c0c14462801c903c0700100450301080300304105e1640e0801310700105a00c04003101261940c01d4411100034041801100706072502555214207503460742c3d4510009020207841195680350b1a0500542c98840c1d21a001d100e1843c0d5076003100e007928280d0500d140504080c2d102c000341c1d0040204002040c4140e013980441 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 784250161 1250 784248911 784248937
    0x3010f061e0f0c02060d0e0c0d05061612021201030614060303041a0c0d0906080a02031324050a0f06080102090d03320406030e0313060e040204091103040b090a08 71
    0x4040c02c25022210711405020095015501081c2203802809551241b0f4111864208444842c0580790403c03030010a400070003000c0703502030b50000d11443c0c81c50502150380d041900f41648055803505441080c0c0c4c00c203400b40340000342070074010018881c2d44d0089103034450010303c10781c070f0b94204440825228803450007480034820760703c8901588401100125003400d101c900648040c060038800c001c22000c1c0e01d2082c0c0d40040c0c2d2000205012254501c00c0741c2c047c4c1c0e03042c1e8140072000c039030340d41e80c2c0300e4184a030b004520003502c021b04500c803011141c02428450080180005948414034a0345812120503800004442c2c0c030600c0558000d071141d0014400301c641604000441324086840361039032061f4040c0f030b0380e926000171400a0040d50303040054000e0f16070300d403001c2c030288811f00b925543c2d900444000e00380860042808200c07244c05003240b01a1100080d0015240039111044e01050300d1075550181d60f03a010007c1040b090100029a0075044007100300540050350564450000780d000355070503a098 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 784251411 1250 784250161 784250177
    0xc05060f040b12041a01080a03080402180a050106020d020703080417070302060c0a12030902061c0e0f1c1b06180b0f09010c05130b0d0b030109050303010f061e 70
    0x8aa491142903074020041004225074881030b400204040030410703201102c0c3c2d0000d5400c1c048550042c0e00e242e60580d000d00004083d200b0b11524101c401810107442aa08400e0740d90055248150350418213100c0d0807210130100709540352681c002d1908021510201c11500b00e030100784000340130b041c11030302110702c00180007809a42c4c071a4204e0620000760b00c003d40c442c0c0000b5070503140810100359803c00c4c600a005900190285041c08e400307443c1030000080d0700190801901e48001020340c800003112000140004541c8486040185004402c140700b0380d031036000040d060002124140f5010050650723140c41402c034142010701c9004024a194021b00c8a9110000344210400c0651110342058004840c1021401c04000124070040b044e10140599400d012621211500480031110740319500b00c0b642290601d0b100e00d4464a0b0848403496001d6501c0b42d11401243e9802d00a00030b6a5000c0d10207180c0e25403401c06441002440ca81c80344e400d21041c0720848200d034840200e960810403403400c080c84 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 784252661 1250 784251411 784251427
    0xd0f0f09171903052e090b06090f090403031d0c0306012103050c01021207030e0c01022e1107081b010e0307020f0103140103080a090501020312070c030519030f060b070c0506 76
    0x21703a50303910b803034031003061403000407142c40300d42504207201e00b00c4188902c104402d1507200203000c2c0e01e00c2078415003a00b001021a440c07116007442d9500591203030080c5000103100d00d6180b802110b80c00d120307001c024290710101060800c1d1074280142401060b1000d05089025038181401c48601d0340388202405001c0007007105240e0450a4040b01d182008080d00c21007180392840010340100441c0038950746510984405e82941d5000040e00207944180c41c0703a0419600d0100785100c0180158200d0300c3e0b03c25120044c8021409101018084241c854107000d40ca82071540918044c016028000051680c1002d551814840e408001c1350211a010f803242841c00d8200343c01a406008105158100b9546640c00001030101c10f10141101507060307035441090719602c0d0b004a0350b0707005a08c03250b00903d80300404120f02a01a40100000c544a4101181402e4400040b010321000c03645010700825128038004509403441d2044c0c10180115071603032070a01c6031f503131940a031040f12030242ca8011440060242 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 784253911 1250 784252661 784252681
    0x40c05040317030c0c1c2c090910060308280806090403030618090203010605010f05042606130b01050d0b0412030e0703210e090406020d0f0f0917190305 67
    0x40c1c82c00210104a070195108060124086180540041b00080348060405e00b00c0390b11100c11072002e10413a502040081c4031100f00b00c4201c03805001f0264074410100300d03001c155024043d490065004242e80c075103484210703806c0d8290b210340c07042c0e14600c0210007990340e5a00d03420040041d040041950700c0100741d81e4618055008185a402451100400c0c0c0e220ba0681410740c0c00c023402c41d92081d4001e01481d5170721001500c9074112030715070380c0c082001800241700980c0100c881601034002c80310380e600d0704103004906a080c901e007510300b0784241c071302d40c3e001d401803004140c4036600405040e10300180405268591804004000c1e100405102c41c41d521420070314843d070404044621164103489009503a854400742003100c0303c100b801d45942050101c1c0809000d8410070a2800f03010307150240d0340e82c503903950700020341c0940c1000d00340030703070711000404400d010b403090309540c1941002c0010548683d0901301d2000c1004100101050010041075018401c032020031460400c1c1801c3c0420280c0340c02c0844 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 784255161 1250 784253911 784253917
    0x5180702030714061803160213020f0f03310b10080d020d0e0a0f06081003080f0304140a150b01020a08070809101403011809050d03050105040c05040317030c 69
    0xa0901408800e0982803041e01140b890302861400903000003800e4920351407a147e02134a0041111014040d041b080036050600302c2004203001d4403030040ca09a20495005019084500500390380c000100c104070020f6060914072002816495558403200040321403080741c04014540140b607146204049500341d007043c000e8078060840c64040c4c03841d171208203d009550b00c85250300c140c00500481d468041505200c00c118061701c1c0320303011000e003081c10b0940a407804c2e0000f404c03810f0b20b008616000008141c440c00a0499400030200c541d60324102401c1c20200c0c0c8070b04d24180740081d0041142d000005140803442450641e41c502c0228008481e640140e00340000c0d218050710200002030040100486600145a81c10f001c9a0340c218400b01d0240803146a90344024006514030100010b101e143d001d40e9500d0307802d1f00361800108501201c1c0d0346260800030303910418070120341c85000500c1a4a0507000314005c0030030740d18005041c1481c6403030b0300c800c2c8010104140d42c00c11000001c031320700034028412 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 784256411 1250 784255161 784255163
    0x309050c041e14090114040c060f020f0a050c100219060e0a051b0102060f010b25120c0c060302120a02180613080d26071e020105040219051807020307 66
    0x1042200e425602d50f040b0854100702c94000a6528102400451007107081800c1d004a0f00100c07008c070b4885c01c00708295000300d0822101d45c15803055000301c00c00c1520410080805600c01c2c0050030a24088000b031101403800c1c0803411040d9000798801d06902606d880800040c43d801020215903448200446828103e511030003815601031404010f40890300c90346080c1681800380e0840d003d035a520381a1000002d803e000d0682e801d03c1c2004485210b0780c004a8120050396544401000e4541e00d43c1c5000100e8000d0070300c0c20104048030300c2c032024088144940c00040043e401e0561501e500c65500b0200305030010f0691102c50f0740882e60710f420442c0020b1040643e400508281c0c0c0d548041450180303c10409d20440d14544030f11801050002e00c24040c5c1107807a5480d00a0751007803844207441c40041c440043c1900704122034240568408107802c0e044243c1d4032220f400015040c2003a006024208003c944101c0d000512428100030944902c4440c03c1d240c02000294002612a908101e0a51080c4c041c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 784257661 1250 784256411 784256471
    0x604050a06030209150717070302070b041503050916060c050c210c0301150302040c121104051e1c110d0312050906040512070503041a030103120309050c04 68
    0x4004140540c01d03034020708200b013007180c01480c0420b181c0d07880c003900e01c10050010810a141010400c101ca141d5000c0c1c5a407502c01c0c01900c942c1502c683d90f511094002d54840300c04210700c28540c2c0400d03905407103050f03000300f00030003d06080668104090603111040c8240c000304a118601082488000d1013906040ca000400c030302c011030104082164050b004211020882c050201900d02901e814840d51016014105450f802c0c14950740800004258260f100c00900003008040054003885200300742c21a440014450f45407424581480b8000128060710500600b208009400c3e0303560b60340f02034180c102000170402c1602a549010010300303001d9981c190300701360303461a1b400805070400e000a035501415001006039682e20000290380340005e0364041e1407600040c4003d0b5809880000924103d03008404503460584d45c1c0a040c030400410f40214180c2808c0880144104949200301d08116032407440c2c01e022001e000d450303094903229007c40241c4120383e00c001c04148680f200006140d0000086 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 784258911 1250 784257661 784257679
    0x210c03070303060f06020303101701180605010611030915031012060c0f26090a050a0c060f0f0215060a0504020a021f110d0522030c0b07030513020f060405 68
    0xc94082d0107007000740140481d0140d004000f2501c684000240c07441809a0030b914007026181c0200350286107114029010315540b5142c03159100700800ea4078030581481218000f4041d0725007803000f4115070107056190810b4008114140c1d0a41d541d5042c1c0224860810b5490350720f8031040308810a044440e880710100c0380d80360700414140319a690244010140540380d030440d003c6074220850707000c0701e580e000c840c0c0b03940135550901d95040304012459000042c4000c07105841c01c6600c03103900d0170344001000c9a1048500d01c2c184003243d80054030079103420b45410100e000c0d50380c00c64060b45411110220243d04085440043c9441d600e181d49c1c40010000035004643e0f031012004003e442d10000038888944008148020045002c58424910121403501000e410086091800310290101503c042100300087c08100001c03880381c8651084188261a034500c0e25110f49070aa5881030000c04071000c0c0b600c0c0c0070810001225428000300070642c1125040d142800d4100020380070b0113140c0040b03400000c81 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 784260161 1250 784258911 784258913
    0x161413120506040c0f06020a0f060213080307050706020c0102100b0607060509010c030518070902030c07021f0f020325030324030c14030a0f170315010e040608210c0307 74
    0x40340503801140038104010042d502c80c0c6021110040c680b00c0c0702c6c0142d101040c6030380030a2611079003407030f450701c151030240ca043e034440300420304810707a0b401c0b400642e00000b44900800100300424001080d00d40080c103a42050040040d4941e14048410b494403a00c4140c20b292598418080b00d101da84d00400c20082d82c03c141342e45038001c015001400c0042460320010a00f580100c50582c90021203c20090101c14200344c0d04d080070703403c040c00c8604164001e0002c2e90059a40d052000c1282c01c0001d20704030801f00140c03000b801b44102c0c0811200350b4100300b100080c40d1031001b4460300c5004828060010b000e8062034100c005059030010310750501d410405100b80200d0b5880300f402101d0060620000702905e030100c00c84403030010720703010b941948900100b10000d1902640d0603c418050b000c0850482403090b1003010960040741c480752114850401001d0359030b040034081d03403100c4081d50100250740c24441d01c155200e550688042c42038444c0c0f41d15a036120151800c48280c841c44d0025241c0320364403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 784261411 1250 784260161 784260163
    0xb040f0209060f090106030c050403020423010e0f040648050c2d0a0308040606080c0904200d080d061502030406031e090f05061614131205 61
    0x19000040744640444008500946086041d0030700505000b082240c0b03d901e0800150018000001e045051240038000080940d48610483c043c601a01d0000d850b60654107121026180c4140c00c5000d0194400050104130b00301c4c404c4113a880b80d4014070001d082c00100c1e03920703402c07107042c3c20b11000070003696010400100c00140b010b50403988040e145840c02d040032901034506005204c800d001c0c96100e1000103a80c003001d14800c00450704e01520401c00c0c40b01080b80103041018601e0103a002c07a100304288420484107220302070040121001070b09280b400a4002582c01f00301500181c4010401d040340d4461200e2824201c511040042c0076a03054085460403100607040052078140c00c62600c44002001d007403442a84005003020b501651a2908042c01079004007400110b544440500c45030741605000c0c14803a400200d070140d402006c84602070320380a4508000202101014074a404a020200c0e07044014642c0650b82d4001c015120a610501c40b00c0707029481d80f044046054000041c000d00c14 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 784262661 1250 784261411 784261433
    0x7061505040b1002030909100e010e070807050a0f0c0305190c060b0405100e04050721021009180203090a050607200a0206030105040213180209010e100c0b0a090b04 72
    0xc0503901803100b07414400421081c0c80782181001c000d6001000812851b151484030a5448803000350342450349034983c0d5003030007440c0c005d17006029800f02c00c2c0203003d8415000b003501e0368440080d02d0418504031014000900c254000312100092000f07140d03e4030109406041070714403402881c440200303005107128000788140c0d10305c4c60640f00e2600d04503c43d2500d08003030203610b00c540e105000c0054254509240c0160140e401403056030180145000842d14243e0f062201c1050310382417910040d0b0340000e004000d140152442c010051040f41c85e400c010040c08009a41c29884208a006890755903084400f400c24841c501d00401600034003040000c0030f504041407039141424615019800a05400300d980d0354010344101a5201905100420062078280c000b0051024860040082250b44448401c0b24072114016818501d401081403211540d00070107980681c2400c6440d0a82040d03e160301078008000080f000c0d011084840000e03001c00656040411555400361003d1103510b05418010f00c0a5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 784263911 1250 784262661 784262669
    0x8090c1f18031a130b16080901050106200f0f010204170705060306040f0905150a150b0d09031b08070b0901140c0309011116060605011e030f02070615 66
    0x15400908181480c4410018003080c1c030303400003061056000e40c0300c0f07070f0710307040300041581488404041d80e075400910542c80581c01580718828880c01400484030240440344000c08024490380340c24010051540d02030054680c801d0b41c00c10004440d82c803d0103c40c18401e03403d0300a14103101b80c0401c90750b8004154001c1c41100e00d01031007000c50103030040809440301e04500c1495803104090001c100365141ca80e20412089038010700c0050207162079541c940c00d10304403205400901091000f00f03e464a0b480c083e801e008940d582007211824285040c1801d86d0161130080010f050303480d102002058041c25040c103540010000000c10208181f60288450340985012104060200040b8407044c10502601c3c010b00a448040b41c0d581e66694180c0c00340b6040109400752641d01c078500352a041418100802e0078940c4052a20300c4200c2500b00312050f03d9290740840d041004058184c4090300d803400050320419424900480c880c20b00080d45006800b4108000d405580340c0340c00741001c43c1c1c285440303008071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 784265161 1250 784263911 784263917
    0x1403030f060a0602030d0b0a090c350c07020103060305101b030203011401110106050402042d0e0c1c06140102101a0f060409020705030c121908090c1f 66
    0x36540c0005102c0b007102d4038841d2802507030091060024800840e0400e0181c101d01a00c0c050351540d585040c1010703030341c00c00007002c0820f0510218070280210f85040b408101e80c0f0740d02c1d04964103040c0345c040701103560050003401503071000b2407800c04580c0300e0303000380e0000d42d00801200c0400100c40400380003071160b001903c0148160b104103000043c060300990381243d800740c0898144000e00c90042d2100c003000300e80f14400355a620000305159a940c80900044d0030440070102c070042408690360b400041c00d001052203c80c0c0b884007001142c911a05465010710805281910384c101514008850b403a00704103001c07118100b0310b01003141300362400c1c00b5511200980c00c51341c04003140c906003811183e42000c0070580c808480650201400c010140034550000542003920741550342c00e40758102d80101204403010f41002490030180d41c410002c684021908180751468a00d180c3c03002c104903a50b00825606220080001a604400038403690381100e8010707150500c0020310594241154460724504004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 784266411 1250 784265161 784265191
    0xc0a0f05150f07090b071403042303061005060a020f0d1101050f012301020a0b010b070c14010c12180b041a040311041e14010303171e060d140303 64
    0xca804241a524000d0f1860f4031108100c9003800c14265031a413003c40d0035151142c106800c40303030944081000b00010306071b81344019a07446015248042040b4000e80051090340108140480c040d103041c0f0a808a580441e11103a854205560a0781000000a807003080340c054940030002041e04600c9100702c400032100200a00d503540d0714180d141c41c8082c05907001660100c01d4005040e000c4213104240c1c808140115080014507590304211503109822000c64880c000c594142000b0406a5050161000780125220b0204580008002c1108120060000340c94005091001401102581440c1c01c1120380100c4243d165070501110364000c1c0300d0300701d81640364000700d00411107100580782941e41c0820300600c400c11610070031000c0d18001c44c00600c1144940010741c83e865840c85104010a803030465184a90b2443c01c000d000e003184119199840703800d8104200d410344020701c03480c500c1c00210009044030740f02e64010646071110321760000d0805000c003001c1d44108900101961150b22911103c3c40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 784267661 1250 784266411 784266421
    0x9060613020703080f1e100501020c011b0204051302120c0a0801090201120207032a2603060909010204120c05100507050d1d060d0b040f02090d080c0a0f0515 69
    0x42240b099082c0a4001000316010880301ca9400b0021500440c801109484001c09a1983d050144003a0381d40c05040070300b14020046540c06001414180c034090030544900e640c01040c041400750a000000d1046039118009100d80304074018407400b403a0082d1020b0610030003410381a5a07035058040c07003842403581020001c0d200c0c0e8140501c1d0100766040e0b64008407581400f41d05406904441411001e00441c21040e499442c4d12850300c4003429003001140d42c03010300d0b07410016155101120990012480da600c0d41c40c451880c001100d0300300c003043e00c201207140e61341d040c410300a001c1e58006981c00d070201c905000c1403090350f004040030b41c3d070216481c51008040a00c00d680d03520900000800682010711881422800384201e61020b4640440001c000700c880030015180740d0091861030300c03603070b0754006500442c01c09200d44200d0490040c2c6c11460100e0240024040500882004000400009482440500034040303140d805500040b182d40705440c603d0515141c0705034000c00c20403180d40c58000b039 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 784268911 1250 784267661 784267699
    0x150103030503190c1d04090210050703030e070f0612060305060c180d2d020306040b0a0f05060a09020f0d150612020f0a08131202210f0d051e090606 65
    0xc0e10140c0c01c3c1c0c49612140141941105c8050545080300760701c107984110080150b1220a900c4005903140ea03034687e650036942c80c003c1e0840d0703d690741840c09039014000c24040045040c45100070f550303881c00d2842401e140300c20544060915a0001081c60195074284078a00c0c4003c4080c14502c460b80b8244088444200c09100342c51601010240940040b0300c0c20211b40c4042d403d400500034250b8481f0610300020781c010918204081d1000c840c0300e240e00341080880345152240d420381854030041841a42080d40c0098a030780c80901414040b2a4009205003440b80208211105249515024000c1c140a194141c0107140306100d820003240031200744000541c0c4510840d8166400100031038185102d03281308581440d0024074032102c402e0710102001c0401c00c410704025007c00e940d40208100d07403404892800040c3c841d084040054020f11050b21403002c10015a555150203c00c00121030369001c200c2d002ca940e8840c00710340221800000d000303800102240b200e2003060240e4001c1c4486003030741d2002c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 784270161 1250 784268911 784268921
    0x51b100203161b151206060c0308070f12150e0708010f1a0c0a06060807050f030604061a1c1109060d030c0201050c010e010b030c1f050a0215010303050319 68
    0x202c040d0810b40101c403000140b070740b003840c1505118890038405041e00c6502044805101c0390304c41012a54045c1e0040100f11580140c00103040f13507103408280d1401940e405440b0800c060851700a0081c403400e00f41c03d1610810180b8650315000d00103101e0000703031007000340200746a40076030080e078141074000403605e50066040c02e0490340040f440c4902e03146440311315032102c141c80d86084074202e4100288206a0410818580410301400d0000b480514028080740740000d184e00c02801094400c080722016035000c103903284c0c031a400c10008901c3d072040f003024035040074403070610700e03031052000035001e45142c0440d0700e445260784034501c0b080f00004c4003010400707030540440700c140d44000190b9009000034440c0010007001c601c181882130030010303592072701400c1d6501c2d112040c0c007980d9500c90500b11072500304030b203c01a80090740c4a629004110105610f040c072031040c0c04040c0308000890b0400c02d81f00700810101c119401c0c4a01942d540c403458020721651055a0510860102181e54240c2150030f20038 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 784271411 1250 784270161 784270177
    0x380f0a0506030604080901050f0301180605010f050a0518100807020c010c12110c0a08010b0f0904020307170a0602030a140a0b0303030a090c08010e0604050f06010f0b0d09051b100203 80
    0x30315a965481d034500d803446d40708081c501d04100050211000261400015501a00b0003401c401c0104a44000507821901e5a034005e5041090b40c1070300076105500181200c41f900420b290041d500c14590f400c2102e4180200b5200c1c0e0441c6202040c2d0b001268060800c9010f00650340c01d981004d896880112006103000380b0240c2181203c0c122554101d0141d005601d80c0c0742e04009889038140702e0f00009003d6038003a4092031031a5164a003160581c070b4088070b0340401d18412590007085007480c0c0c0100369182c01502510b9143c6200392007866410b1020402011465070018007550750340360507100c0e20058511642e04064500c81d01012480425040c041d65a8040016008500b16038400c1500d41c06007030386540035501c4e40d45101c0003265a110a00842d10024001070080c01d1508091400b289000c20007030448290750403541c01031000c4205030b40b8450495100c0b08120391a20547c440f6000280000200140300e4899200034140d420001d0003017039000c0200300c41c0520740c0b500c10401a42c8078460118 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 784272661 1250 784271411 784271413
    0x1b090e0303060d051f24030c09150312120b0105161101120e0c010f11030301030f080c010507090e1f05120f160906090902060304380f0a050603 63
    0xc2c000d8281400b4441600d030045086458089100031003d020342038400c1548005c0f43c4400b00240c00c00c507100d4800c61070900400c107048100d03107035407900c0c0c40b4811140512440c00d42c941b007005a003142c560000074040c6800c2840e002046501400c01342200d84864a41c00745141458820380b0300791b020b10155044804e8510015500c0c042c00d55440d940c842c102c2d400c940c10303c01b8502c0c401460942c5031243c45518200e4400511410b50317040c001411812480c2e09000820003a080b14079400340c4040b041d00d0459600c0003a45940e42c2003031070204602d0140ca4480411980303000c040182840d030191a444c03c9455031404000b441d202c0204640700113404a002c1e1402d002d000c102001315040c0300c482030780c841e8030380800d407081503800d006694102814029011000c030600f44d41400703958000d10800000748041c040801044907168046030f6140002000030f400c40030300044c000c21003906442002501030690b0b0803149405615080380483c94825602c841ca426400000101c400600b44203c5018280041c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 784273911 1250 784272661 784272667
    0xc060f040b06010e15070c0f0905130809040216060b010e0108062404150f020c0604062c060f040801050c09010806270f04060f1109040906020c03071b090e03 69
    0x2100542e15018a124203c1d000080c8114858041c61202d003c0d028443c8201740001031f06180220708405a481500000c82d828035110900c000d807031550108407800341d84812126219460080000c009020705603401321800c000441510400c1071a0303229902d50766098031051311500614004440701c81084404981081062030110c00c4a0003551503d8401c419110413a403405864804a40c0c61105001890010548802c0e520a80703c1d01800046520f15058400e070741450715203100104021030070f081900c02c42c1164450380c1d2803000d00ea0741e02001d584002c0c0580da510f100420b40e00200b03900900c542030b5a9403030900800c00445102c0c3c01c0b01c8104805075180c030115180c0004001c0c1060405462000070f0010700080b40f03100400d0100c247c4280030000040060b8601414140e00751024010700101c0302d442c014081000980ea07000ba074401f20820350b000070308080e0b1864041300911610103080818800441c17200200081074081020194070b4900c05507040d551402c0400a03a00c100b5041c2c94182c0042c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 784275161 1250 784273911 784273921
    0xb19030c050313021507030201020a090806100e060f0a03151514041107050616111f0b0112020d0504061407080103030309020607140a05240a0c0903080307050c060f040b 74
    0x8039a0740003440307000070143c5d015020f20301c038404020361285404501503500494400d100030b4006502000400a86c00076104078544190f240046500c24040d59003405003005c04900c40780c9860444012146014000c62542c584034103100310212006031f55240310030f0407d0341a0249184011001085800ca0781440103000900c1d02040041c1c03030307144800d10412506001080c007164040165a00a1810440381031160b600418010088038905a0020055202c003010447c0805e50807000f020b0420420000180c8028034001210301455424502000754000315440502c03490a030320050044c0e110b14400c124100d2f001454070b4444504450b1000458664001000400c5c007030f07045016210303c020b1982c0c1c6010710aa07248461100000380090241c3c0c4400003420800804104440d0840c590001c0b8281c0074080d840d0510b08001c004081403111901c4908401070b02e8090581c1c030001d0b662094100ea283e00d0032000c01132041c0c01801c0c1703513011845003501003110700121030003460141c2c0d00074040064990b60 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 784276411 1250 784275161 784275181
    0x302150703020a0f240903080601141902011d070b0a050304020f150702030d050c07050f2b03090f0501050906070c031202010f0f2c01020d060b19030c0503 68
    0x2203400240c041d8001d150802000907884c641d40040144a01e02d07600340d2a04002c05402110020301107200c0700d0b0b2400039410b0100b034011005990140007460410f40d440c0c4200d080211600450540501e100d000d03280202d451901900806280c070404c103075014840b805066010742d940300074481c200c00394a042040603000e030f108000440c0e22a0000d0180021001e920000c50026a50030210220301c04c400716191045240c1807000442a6095203009401c00447e07600b01034458036103215191140e05c46205500c1d060311117500b045010b00380349461030702d81d81c3c02c1c02c0411043d4070b0100080340004c5c605180802d60040c0c0111407025140706079515400c1c04040c10034885103074011401074a610083c02d9000002039901400c0080380302d56980003103100300c0c40300c450741c09441902c40403250950609402d48110001c0e030042032691403d00a14003c00407850034424024400c51640055a42c01c001005c6201c00701840144485961135540d0703c880302588000701e04950140007002c00040007000801c4245207 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 784277661 1250 784276411 784276417
    0x318201201051e221704050d200406241110060e0702060c030708070c120e040b0913080f0c0106030c0f060206090a0206090a0b2212051018140f0105010906030215 71
    0x100500901b4606522100003681c8095042c00403a100070101c4150001c0c4001020841701117a42034500340100f07420f200c0711000e11908150415031030361544826100c411f201c0d02c0f1904080c0c0d803c038180c810310208ac1d00d520000d0700080c080c190305e840160303000c607460510010303000e032050303000300341482c11511542c0c001c840058000d4114000c1240030014440881c050254141e0b8118144d01c85120307110611040c401034800070810070388100103010801c01e01c02e0a800365061b4850703120848550b00c0d0b000d00381450b0030380911061400315600e40400442000403488640081d0303440007000c1c0b4811666210200d0f55603004907107812154110440040050901d1409885847d50080c15861701c00d0300c070910103119420292800c4a00f9240850008840d101055164042e01b6002d088401d10015515096590b45007015401034079030b40c03006200072011001d041000070302d50118040c924802600c1c202603440c0c50011003201c0952030300000085003c40f9108a0003225801b40c6020301c0702c1300110b010f001d070360 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 784278911 1250 784277661 784277693
    0x80301031e1208090d020a030c3e19080a1101091503150b07050d080408070c060c0606050916030e101b0318201201051e22 54
    0x140c1507410300000645845802100390b003080d80c0b03604051508654161400d80040001c0040d900420024008668003014030b480140d08100380940b51845566104a00001c000324210090095104083c14040003140c802d188071084500e94600c4e000003007107140c42041c2d03100307844041c1e001c1a07000c0000741054448036102d02050506948403030f81d59480318000c1003040d00b00000280c2c1d8080746021802c0f10854907016204141038141029801e0740c41c40d07a9401c01041060034840400c00050401644004948078181d10000000c5080d41d5202c00ad80182c0014600312102130030098041654102204111700c6084c500111030b003041e141520507001405112028051030003051110444404140a185071481041040f03482c8d01e0440c980050803150f601510382c28a01690354030710041007030300b21242d2111440d4001003122510030800175000c8034a403a40d002c255420034007001001078040c10036442c0715a0008407a40e103503440202c80300362000c018040d01080c42880c0c84850114170303c151080203603 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 784280161 1250 784278911 784278953
    0x10b13050d03030902030102031f0902030412080907090603030309141b040902030307051203040318060507021c1b0f080a02130203060d0c152a06020307120204030c090b01050708030103 81
    0x144d51907801090990344101d90143d800c002401d808041c0395074444094000f000513080031070846c00c082e51503000d0005100030040400a070341000c21114402484084010b03e0210010403449039a460050054000d0003002d07500c140c3c171001c906060942c08242d8400039029101a24641048a01004018507022500341c4c0c040c4024080c9000264007000003044085000400340c0e12845c00e440c0040200c0711844840030701c40c00003041088400e40250540b5a450f5049070144001d2050034021402c00c61000806440c1030742401070400451034076088141551540150031000545a80300c06a4654005070025040300080c84445820ba0044e4095030300184020080940c1c201680c030780280d001c020341c220008a100f8035000e078101d2904103403280001002c0c011410802595000d14018108032641d015295a800200290f0407620a40c0d0080c050710140c00d003152126124280944402958060840300314608241162030307600030000d907040c4990100d500344c5103a00390b0b522902c010150003609088 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 784281411 1250 784280161 784280171
    0x2100e010f2405100e03010501090207110307030b0f040f20040b0301140621070b1810170a0209030f07030209010e040b0103060e0a0b0f06151908190e0307030305010b13050d0303 78
    0x8a031b400b805014001c200b041009a150321050525030403105d10400041c2c403d034002402000080c003030586840c3c0c07107022010600c20550726401d205041c00d01c2c481e002810191541c1665607110507550050014220a4604000d025503050605003203c445103104101d014801d030005e8210300d0300312640c440901c031003000c00c411309a0041c992860042140c00c24044110089400110010100c240280d00030044a0f2010140181d90340507060260f042c400520301c42690300010300c141015011101c1044016049171410b5000c2143d594130740403035000c00c900c50403011000203143c1d00611a8180200c2c0c1005010703015074619aa14001425407901e1080d50340a0540e125003c06c00d01079a0394414002c0c0640c0110700d1522074100040d20f00c2045006090510074805d00200e450580218002c500d03203401c0001003a180d030000840300c0d81e0100c000c00d80507400d281c006110f0000100c0605503461081d1014040307a602c6981000242c01008020107840f10805010022480d080710504840e030b0184c100010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 784282661 1250 784281411 784281437
    0x90c05010201380604120b0a06030f02010c050f1f0608070e012102371a1e03040623010612111e0a0f020c0d06090302100e010f240510 59
    0x641c005910648080404036845000e000d91f06403499440300500c0d02c10441c25003507542c1c8100ba040c0036140079041060401d4490100a01004003100f80e100803c00c0362506041000700c007069620b0030034030001040c1071910004d0a0400050068142d43d242d800349615682810504071400c2100c50380070001e0a01c1c290b103e0007507100d014529150740120020741145900f14450344030324560707440030b4500c15600103400300702c090402801c039442d80340000c0d40140c1e98440030100c1c40d45011000418514180004280310030450703031794050440700c2c0360000380080c011880c1e4440c07440303074509100d0345010504601e0120798543e00b43e4003040107141741c0790b000c40c14651100c003c4480481d003402d9080d00c41030000f5407010300641000080410740c6640c802041003040400201d8100042028014809034a4614000405000340000a1516401e500c100681c207010ba207801c0c007820104030002d20a0780ba100c04500101030010300e41000c1280c0414103200300e40f901c0180b001c40c030625510781c02003120300c0b15911 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 784283911 1250 784282661 784282669
    0x3e0d051e1f06050411090f01080c07020307090b011128060e0f070806100f030b0402010e12010b010f0c0f031110020a020a0b010605270103110d090c0501020138 70
    0x710105152407030000d24141014148001c461010b210441c280b14140310045142d91444c001007440c410a03e0039101903100da03280c02c85176001d4150003d40c103010f81c0c0404a90034110750f0240c060000242c0e5542d1440b403030a00425148d50410301f510301e144031001c00000c405840e8101201d1054031541d00001c030f035400c24503264100865441c0005150f0403445040150200400c09180c1000f920160740d29454a030a07144510039043d44801450000c01c90009000d580c001c2007d00c0c458580038200854624109400c42c0c0200110a03100e03011031452511804410301c250101e001c01a4840300410741c0c51071646096a65480e0405c094040c4c0c03040c06003007050b0520900140c010188180c00419502074685816019402c058100904001050000d03040e0b6881c40080001c1c4c503040082d01124460340000124064007003040c1102c590980040d1500d8416169844021304502030842902c1070350710b0b14012400d03516043c0d80700d5411400c0851520341a0400c003810720154a40d08014602010204042 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 784285161 1250 784283911 784283953
    0xb0f19051e03061816031d15040c08010903050a0806041b050403030815060a11120f0921100c02070e09160914010603093e0d051e 57
    0x41d038060301000c070034000d113030900000c1030114600b05260402c00780703030000782800941c0c80548000100b6855402900c600e0565440741d0000d030340311005950301c5804004c45004d1000090310100c507110041d40c0001202e0b9011312901b55003603850b9a07400d01c1e0040d8030508444a01c0050b0000340e01c241d0722526021541c00c0501c40c1440c47c103482c0c807941c0d1142d2a50401600101c00104610f85d49418660f8141041c3c0e0341c541110480150360a1404203403552001c018502840594400881c840c001282d43c100214000501990341044811010201d000e0511004039100000d1a45a961081940c8010411950001c1d000700d06540704a8560541c0d480d4000c20f0041d0603907000e4650b0f040b60f0041422071590600c610007500010b9010700a601404007140b400c8101482740d0800c042d0342e0203000007002a5a101e03880612607150019642c0c84943c1c0e03520502600c071150700c3c001081c0081d880c0560b41000854010100d400c43e019004200d152100b0f02c031060314490340500d4138011490b10b051030000d40401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 784286411 1250 784285161 784285207
    0x1223121f03050d05090303120124181208040f0807140612010e090c030102030a0605040606050705030a050310170c0406120f02090a021c05060102070603023c04031109010b0f1905 78
    0x1040c11072b07645080c81d0501c04445c8451703100820498000d1030031020940c014203800c03520b001c0881c04240569081039085c0d80110b4005115080305100c0000703da40c000243c800a54200c0c03100e941940b03425500b006058031071000ca0041240c4180700400188001c9039503558411004815600c1c0d070030b140030009089a0007141d084245a036288818001c0b414a84650805401c180c10030701c0c50b1070075070f40780d0310f50b24010602040308114000000034180303816282508000c1160f042800350544145200c5516801020b07440c81c003442c6421000a1414209005680100e070000c40c0740f042e1001940078000e4107600201600c080b00c0e000c20201ca03040f40180c100316101c4c26101000aa9801d240000900344506a030010f0304060044c00700b00c0c40e00e02a4071414002c00c02448000c2c082040442202d2001d4405100e03c2c4c0c840403022030000f0600c03040c803083c200050806c40d00390181f41e8980d001016070b40500025820100d80a00151348010304000c05c9035440721407414103d080c03e46044010b1110020400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 784287661 1250 784286411 784286429
    0x22020409050c040c120c08040f0803070e0d030206090f06150103020706020918070314040b0f130204110c0c03010213050907090801151701091223121f03050d050903031201 75
    0x5c0e00c4d6212110300c00d0382c0c04540580341a1482e82410380700c50303803c100402005440c80781c00001054503140181001e003003c0c0d001a0120078404050708001c0d4450004580303280300d80c00380510b080d034400c4001c00d21900c0b480c00840c8004112005000440094114010803034038950308000900c15541d0b41034900c0350140c90702110b901c4070320700100c0c000c0694884c0b038203042d840480c0c00140320000b03014a6100e0f0380b2078941000440f26030344803000440d800f00403d401940140c5004032414030700d444000180390303044504048802d100580c1082c54202c1c416841c0c500b04040c0080c105100030f1070044545a0050014034194140c0b5403254461402c440344014102e00d81d0302440c5007004121060a0010402c0140400803c2050b8843d195010004100211700c01040311031781d04030088018404216004a4104243c4c5441d4070340d8841e6003000d60f03130a650a04112405d01c10380702001d03280c4a60f800550754803c01504201d1840c4c501039034560000184aa8140000d20028085c840041c20150003002224 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 784288911 1250 784287661 784287677
    0x6140d060b0c150f0a0207030c0f2d0209070509031e01050708060409050d030c1119170f0d0209010c050a06060f0503010b011d0d1b050922020409050c040c 68
    0xb45a49181c440b004200d0a80140e0000030000386034061480c0a0340500d00e20b1000d65999540d150440b9a40c44140c0700802011842d1003000c1071090f094944413a00d01c0c1c203a108035480e031800119801110440e64020340c81032080c0002103485100e5805081441c80c05400c40e10b100404440c0303204981564041080182c2d51a420003002d294440c141d0382d044101681c0c1001700b9119610750079102c80f800c00c0c41209041d201c02824122502c1400340d510016800030540f80683c04100400105162010b4240c54a41040700c0c295101009041251068400743c08840d1402c0e41000c00c000103074204c103109a05014101c5903210220301e090000c0c00c40d451180307000051480c102100c00343c007212035400045c06a0315100401c0c2c0c0320790b080003001c040c10b1410f01000000306006000603140c1c04031310f5001894061086c14540440b0b240c0c0103000d059440455902c043c56554604402d00005540b44c4007803030b030840b05002c002506096001004081c010800d603038030142c03003502050585028100c1c0b100010030b45 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 784290161 1250 784288911 784288927
    0x10b060a0324080309010809100f0509070515180a0b040e0f01210f08070501020406120c050901090b0d0f02031f0807031a19141504090c06140d060b 65
    0x818403603a0560541e506902d00c40781040c20a80e0b480c0180b0071154144800b0380b01103640b242c5c0030401d16441c040c4500d07082c402d03269000c840502030201610fa402d010300c40c044003c078040c90304540c162210340000074120309000640300d0242603100e4482c20707150004803402003c20003e982200400140030840020f0300c0314100400900c0c0340d880705901841100d40c03d0701440c040c190022401214142c1c200c0c100500204050920f81040d100b1010000c2180d0f2000500085241d00001c0350021005202c500700704800008006442038829103010720300281c1c840c0014060111080c02420115203014030018a44244080e000100c2c1d10a407404070004c00d0060040120681c010002405030074518042c000076891542e444c0310b05804030852064090928000900580300002151001402f902080c400380c01c2c442055040d1490035154110b80d00707001e0290041302d00340b1b03008007440b2540c014040a040c07460020125800f00071040d5010001c04108800e00000303605024001c05008003000c0981d4a40003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 784291411 1250 784290161 784290191
    0x4080705150906130206180f03010c030c17130303020a0516030201061526040f0c0b0d18030e0105090409021e1908120711040f050a360203010b060a03 66
    0x1000b403009103078a140d4601038006072200c5c01034850310380340947c143e07070040035070400102180c00d42d0a1694143d03103811021845140c4c543c103d0200c3c0091030f181d910400b20171000c10a50140100e4805150074003100e004c00000f40300e503000b403960360700b14501182442103001892282d11400c4c002580180c2d19002e05200c0315141c2c800507e1140c0c07090400d0714100c620522940c0141500c098040002c1103044000790610a0003d00194540e0344852921461a00d410400813950840b20300820b0803032403c81c60350307513607900b819180d00840e405803115070944a00200444465000c2c0b00d909410a4940c240140140c50305803100c40c5c0400f403690110355501c042014000c2d561001100006101c00d046010401c0d403c000c918103c008294404961340c54200b800c24500f080e04010800da0000e01c2d000c880201a01d00e070384100c3c0a00c030700781c000b071000b0043c0700381d04a24014060601442a108001a034140c03515036401500344610180010509403007800004880307030444003008021a86402115a030509 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 784292661 1250 784291411 784291423
    0xd0c09140a0f0e0622020306010b0a1b030e0f060c0a06200306150a021e0a12022806090533010f05040c0e030102030720071d040807051509 61
    0xb6420008001d07145240640c190348650151403880d0300003c580303005c41c1904800340ca14413101d4018049503501c0d65036164444140c9d00044d00c0100007902192401d0313001071081d82c00d0100030740503074807103030164902003c001401580050480c0d1205042000f2046403005114045071280208400200d1011441504900e030004c0d0910420100040040081c1c1f0b946002420440f001c20062440d140d003280c0f0401c3e40361051143d010010354110096040b0b4500c0000742980ca85071164580c2a4003e28408059a07144101200d20b0f98061800c041c0043c0d0303002c0d40c2c2500c10641d004030004101286c942d02c400d418080150050340840d06004a807809000c0704003410b8064120180b91012190b240541a964407641400358a00c921344038051120072501c5002c00c440c051038020021540d9040c4480d0141882c006c034201038003c0340000784c0c1a00007607404910f4800700d4058402000030707016400031454150100500c100c80c840c4052083d0703004142c0800c050310200f2000981c04410382801c11610385042 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 784293911 1250 784292661 784292681
    0x150321121b0a27151101060f05060a0203040f1e150806010c03030b09070819271502030406050a0e01020315010e031504080d0b0904030504050d0c09140a 67
    0x405988142500211540102c8100803681d242501c09a51406110603104188078403150421011100201d0304007011100320005084945502007030200d4440001d09075942e41c842c00e044880c4040e42084913051810090a05100e1441501d1901e0b40b20349660002d461250001034041d104070500e02103482e010500c00000c1d0414610380c8400003482ca8008110800080c43e50b070401c40c08281120800d03010360040402050010440c0c049454071501c000c01c80082102c000f1045807010442051062a502c05d100d0b10041c201119410b0001c2c001600340e03001803212044600200d41300f00e90700700740036500c042c5000364070884000c40d080c01e00740ca401c0207449481e04500d005074810028090501c0146039105a19102820554001144280000c0c20000d02d5608804544030142c100000c0102d40001892206c0803007408005102c02081400311840d02100d00130301040d0208010b21844c0741180e82049154814410714030b1442d203410f000400d60f1030405e20203080380c0c00b20040c80303403000e041e0080c1c403068 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 784295161 1250 784293911 784293931
    0x1104090614270c0f121503240f07090803040618060926031c29100309080d0903020d08090606060720030114011401080c0315032112 58
    0x3080c54240e108003002d001900080c200322002645150b040c10201c10380c0c0b40384a03441c2c0c0e510442d1800481031681d8000c0302e00040d00c213014442040550300a8910005107413190b55004100316541c7c000e1200100b4405840f440a1001d59500020b210300104010000f42070136503103c0c2c0e000280d13800e04070507820107504044280168130750240419071503403090584c00c00045444114040149811038290321500c07040d004120f901402c40c06980480b07030400c0c4e49002c04c02d154202a6240e03d41d118100d0103051034030640c801e00c88a4400e40750351090b0400340301a401a60654138025200f24084101c4100341030880241c0c0040b5500d0681b5900000107951241484010340f07410700c1c10304005079480c403800b81c0c003e0203c0802c154079180103100814010190b54060000c100407031010049154180d0244100302d1940c00b00304001d00994402c1c0310160041031550840d506603290820381d00d115000c1d0f010001d406224000102c0141b0196041609101201c00d6905a441c070101c5454042410010000301c06 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 784296411 1250 784295161 784295209
    0xf02190909060b0d1a09151e100f05090301140103030206250c060b03030301030f170a0816261b07020f04051b03150f120a02041104090614 61
    0x18402440044508010501130005180c00013142d0a128200320b03020762071b4000c0d0700030341000382c8140d04820195070220101c90000201240e50391820b42c06418481d040d40088100015001c6940502d001040c7c642a90178240e00b00701118000c6800c5526440180e46407245e458010010f154051003081d4200d0f219110742c0d941100341446020140b03640300c032440101700c0ca988022041c4165a0b0103c030344108000c041d00c0e500e503521705210980440440c02594103030005100c807400321079000112180e0031303000d4035840400d907201241d10810100c002c16020901004070041506690050484211840355158500060038583d6809190301540d10395041861802c01c6108090b030340f0394100040280302200c0202d001d90318400d008090800e514040e2500c0d00c000300030b110703045450f2084202d40c11001d40d54500040c02182c10013034000610814404035400084c054409030909400a4869659001c0304500d425a1190721000700c0340703203500c40015004640004175051518410074401c0c080d000301d100c20 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 784297661 1250 784296411 784296419
    0x31207030203071d0a0305011103060316060c15020910030c0e01090b0403260c010b01021006050d140c060f0309060705090105030a050a0b180603011113030f060f0219090906 76
    0x118a039039015a010040c45001075031130741c540e5075011140296074403038000d02010016282c0000d55810540705284280118500748038505244000001210900d0340d44148580040d120400ca1007200480d0704a9580c080052113025101e181400305085416030700000c40c4c4c801003100420340c010100c01141002220b9004010440072042940c017035940000001c1d9010381444000d8203018010105452466400b00ea0740c14500010b50100c000e050080c1c098a184540345503254003110b41c54021a80d1100440c10070001083c1200c17110812111220100d805903580440080d42e55044080c26046500c000030400038000014040750f50000c003a41070490400381d8400000c1c1550000070220442942e48000040c05e46035241c000c24103503c00034051401c5000010481c01d003800c0d007182d45078040e40c01c085001410b04280002c4880000071500920402405d6079075030055040380d60410707a00300f81c4504049000c103069100504858140703420ba203501d04041603010b8070000d0070f41e10481c0304915000c0100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 784298911 1250 784297661 784297667
    0x1090e070303110304030609140d1b15060b040f05031009050d050705070315020403060b010206070f030c03060504020325050a0c06180b04030201060801060f12060506060d0c0203120703020307 84
    0x381075035407504040090300c0d00841d00c10720707502541e400901550f0a00b00f8110500c101a6040030f8a09014000e443c1c1d40c01da200c0041c1e921444507000404014501556040486c20790784490a84107107000021556a6560803440b42a8103e80c0241d8008080003500b00542e01d4100071404030b8203560401804140d0381a240c00351540365644409080c03000006d002d0301000300602082c00070710b5101c4660703000400140302c090b000b500b250200311851031410100c8001d66000103440c43c410952035840d5900c0006884e01203000d0812188090245501d400c4086060740c3c850010b54421a008401c1120142004450844000e4a11256014400c00f00042003080780e2100c402c1c01200e0b080100452400311600d960103090075541c401034060164041440109641034000e54119040d610081c0320390b41d1100042c001c0b0362014400c501e0f00c40c006008000014405410241e48000c00504d0310341402861a008019116183d12400050700300203460300e202034482c090650003181500c8c0840c01c51411410107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 784300161 1250 784298911 784298923
    0x10b1b070f0b03130b040f1a060d0219120501020901030c05031909030c020d1b050a05030319052709182109180f0105010f1704081e09040501090e 64
    0x8100c1c5050b0010000c0c02144000420314449a40180c4807007042c640b50910007902e090f8000300f121482007280003c806405030b0205140245c00060a56004c2500c984c200108451541c41910102030008800942c0500d01441c100005003d20300145e0380300d0840303000404681038203945200b808018010b01406c4140000c04074a01600c507c00000c08020790b040c161042600060000e5110001401207400c10899807600b104042c201094501000c1c0c5a00030421440514052190503a10612503003c210081d03c444803c00c5074031b030900e1441c1010342243d5410307400c802003074a889042d0301c0c150002142070112009600c448005e0050000c4019082e0142d20f03200507c3c00b80d80c005048980c40050290100c0407201c424000501a001d4140b0743d600c10300b184001118145040d40301c07000000b03010350094600090249042d80c1e104607400d5841e2501410380005803003503442c1407061000498100080c1440581d0700b18041c80c90340c403000c0308000c2005690050308142101410078106810184001600c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 784301411 1250 784300161 784300169
    0x904060f1a1602061b01110a1b0c030b130308130c0603020c070e0a09141b0108070909021219060b1911191b0501080106110a0605010b1b070f 62
    0x40300b681e59145800c50b001058030a0000307544003000041c841420085881d40d041210891402070141701c0e4180c0a500da9400b80080950124030084608004001c0c0d40040c20b8000d4401c2e2604407075a0b490381c0302d403440c1000807182c00b054260606e070b200d0281030300428500d078403425181c00307000100c2090380c45854504140c0b044001f45900811a002480d20030711602019200451841115141c00007110000d055111000d4900780c007240100743e001d041c0401c4440303580d090100d80d500c01c11481001165520802040d1000708a0703030710130110702e0b41064001000c512940112000480c103240c60001d4001d0b407083e0940300224600701040215030031660503108908901090030411555141050340d541008890364915030041c10780300c40058290039071503d0350900504552125003014480c200789880300c1c0c020140400ca0540040003118402d56002c40500021416900c14000b181e4502c0140e45003030300000d01d204800b050503d00d181c50b0030305085440c035a0400030424180b618001d4401500300c0d000f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 784302661 1250 784301411 784301459
    0x80105040c0e0702030c16090e21090310050408040311031c0e0f0a030c0303090b0c0a12030b09150f0d030915110f07090b06030f1314120904060f 64
    0xf0000380c0244144c60241d0811016641c411824031059110209940175107200249072500c1c2d031082e244c000580b8504140607031100704550500c4200c2100c590003650f2800ea05104081c5002841c0e0ba5a0207a24059885039208585440c21880e090400800e6010300c0303400b07540904018151411119040611040b040c1000704964000b04041103100104071000c03504103d520500100308800840007000b10b0740070b0b0b42c5034440f81d40c441103006121f10071442c2c03003080c642c0002d045d44c02140030604402340d000502c3c10001680070308440440d040c0f403011190002c8007002100c0000030350a012050300b0700c64008854102805e07015680c082d000c4d1455018140c000900f06241020072030140c3d15892480c2000e00440300300b11410407006580d4550360096646260a2401d0f40c0359070304016007aa4003c217000c4070960719650714500d003081e805610150682e0303448544805850001014064180d442da20820080d507241214030520058036100d0f8001031801d840782100f000203100a542e0300c000710078620 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 784303911 1250 784302661 784302689
    0x9040504020a120318152010061511010b0a2d0305071811030a090318180e0c030c1009031509060c0c080a0516050601060315080105040c 60
    0x400031800c046201e80107264000d01100c0c481060642092030350b00080c00d0300004840444d11034017242c40d02d0394509241400715840316400c40b1f800383c0000071100810580001c0b207103901c6095103140103035803155001d0400c4030040c44014a082e5031004030075401030f00102c001c3c403c500c07004c408640c0c940400d02c980007454001422001d040c1c8411090344401040d25000074605c4d60310b0303043c1507860b201c59200e07007803000004403d511140c0c401030151001c0303481681541800c680c2c03100f1300c2c84041c0ca9072160890402c2240c6407100c40d05020341071010094040c03961441d000711031540c0040d086170780307100704a40c103a400f4500c500080d55000444004140064a41501c640d140d500c058481d038989400080c0128050703001c066108131940d005058075070080c2802c6c0a080e603902425900c4144812028107507420400c50b8a103000c0c0208014070702030a2519015081e0601600c50a081c005c0a030000e100190f142c101203286041c0d4040c1c400054203440c402080141017507500c0c180035039110310450314420101 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 784305161 1250 784303911 784303913
    0x1091a09061c1415102909030115030602042c22120206040201201e0304090923032107050d1a09090d050904020d0b0d03080f010e06030309040504 64
    0x2d840b09000c803080c0300403141d258000c605082214442103920217030340124040009142111212070810102c0102241c6055038096100780e80e80754040442c09815640324500d4501844604030800010b5018420040c7c035242440c1015004050214044084041d80500401c8100d13140703210503085007018500040792b486000f00150b02c581d5118000d0070302c2c01540610311403030b07402189151049100f6a03903420f58400c1e8500070f81c500c00420081d980305501c000c3d8941c0d03840710042041642e007240401181e00f0b00eaa10f4032000244c81c0c490500302c41500c404101c1800c3c009083c905140742c02042ca005d035040050324a0150700710042c039200721010800f030001241c0d006000e0000c40d5080b600c00c1c0da05000d000e41e803049204d000c100c40c15a8034054062500010b000500101ea001c00b60021645c469141c0341c0c0c0d01c0c4c2008080d40085109600e0580d48040c0511079036a6031075a008014440c3d02c89400c14a40070f030810302c2100050740243ca00510030010405a80da000c01100c99480c0f00321000261510340f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 784306411 1250 784305161 784305173
    0xa031b05071a03090105070f020307260d2c0d0f0306050907020307020306060402040f0e09031306020601090c03090b01170c1003021210051c060e010501091a09061c 72
    0xd5806405a050030302640c100c1c40a03644000c3d4424220728000b030010f44c42d0324504030b4aa88002160310016002840001c0026602100243c05003e5003000c040e90101481200b0030f80d54021803265449d00e585002c140490603405080598082949c00d42021070484420900e40f0b94410444140400c05840c0504404902950012028020141c102c405524289901035501c2d07000c0a0141d02c01e1044500007105860240201d80c1a1484035012501c00b600e000d0017813150300000781c480d9030540001c3c42201102485006010010045a8020809549032014035022204818403190416041500b5080030a060300100360441390b642c0300b1303880c050760000c1c20b0358100714003440265800f42c0c3c0c00c20310050559254000c1c112102c41d1050302c0056441c0e40e0104807010740c003031294980044d41d41000080c02000d11100070b4440303004900105680a08154003401c54030240c001d00c094540c1d5828814210004500e9000704440a0b21b841c1014104040002e030940c0d0840c05001549089000484c10088 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 784307661 1250 784306411 784306423
    0x702060f130f200a0f21050609340506071a0106080a141b2206080a0e03031017030904021204170a0c080a0905060c01060312020a031b05 60
    0x1410240071403900e68203103000c0010020070b292100101c4424400343c5654941482074104a5009090082c4402d1401c1c01c214440406c00700c00e40d1500a40085090210303a05101052281032080003030003070400383e00418440c40c050103000700745408911805800c80d00e00142c0002c03e8070301c11104203899507800e107807558030030380c00040411101412000000c1c2c81c50b046100b1a018400102050040301443e0003100070001048503030745003200d259103080101814400085c40d46040c0c00c460042d401d038075062032030042c01c40ca03406800000c10035801c00c42141d80d41d103e6940c42c4941e481c040c52031414521801c9420301c0c400d005440d14240300c410070401c10781040007190b0800901030800e41d00e60f280140440001c1b501203c09031503c03141040030220240d84d0100700c0f09600401c1d121020307100900e40310269207404c005075401c00c0c05002d4001103907035580c0c9400780042c01c89000010030a40d066203400d00503c2c02e4441fa850a6510040702500081d030002c00c0d80441c001c00c1802c3e000c0f081d9082c10000d10b491 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 784308911 1250 784307661 784307663
    0x307050a020d08190206061f021f0b031e060a0504020d020907030f150f050109030b010b0f090a0b0a030b030c0130020304080c0610050105120a0e0d260702060f13 71
    0x7803150701351203060b004507000d4480c4404454880310064407106d21210309510301d0042006030044c0261445402c944030b0300c00189440007800241c0440c0030b4002c03070f02d0411101c01c1d41550418a40c8440a0034200308507066100c000c03014180103500b019408141c005243d0b80009105900c420006001544294041d500c0d0142801d001d0000c40700d001c08004080a0f94081c008040c000d2070000700f129401040c042c0110703030f4440405045130386002c0d072103d40c68100341520240c1e00f40c10007900c1d4182d580c42c0e0740c1c07801904c00402560382c0d90412301c1014045a062102c083d019811101103034540d45e82045403510184050b0f041c0c24500400b0000b01000307249200040c50b01c151011050100381314480014140d040642800ca45403a2500c1108080980c020700c07407140012010003001380f0070004001c03040c3d000580c1c1c450128103403124004450a0140c5224503500060b00b0780000303240c0c2d440c00c0d5007411000403030303031458455820071810003500c0f0100100020b15a5070f408002c10400322651a09030019 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 784310161 1250 784308911 784308937
    0x6010e03061f051503070c150f02120f04080414131b020d08060901030609050c150c01060905060904030c050a080409090b0f070c030318020901150305090307050a020d08 74
    0x14a8244248802c40c040c1030a1100c51a60700d48020074182840d0102c000c1500b070040b811400d55840038002c482502c21414121204111064007424402090185030380d980076090b00980c03a04600d00180d81800070040850061040090a000c00324600300c0c00c031000c0d80c081d2105c50000d4002500802c980d02d280150340c620052800c43c00e071100364041000b4400d1548a40e00741d44a003820032404070303864403068624581c0310742010010800102d1903070000c0b004507c26070544401d13085807000503680c100700e0390180750210340024034811001000e110310005084041820405401d285010990680000700001c00348224681c8400034170404026181c11141c2c4900800c1d545c0303403100907071009402042c0c001c072180300100c004540100001212141714017115078806d142d2424a480c214050410302c40781c0f0301c841d00006040400758031003400301030203800444080a0f121444400080c100c400c0201200340d41d410900c2480c0010350b0200b00d920b0b01030340488400c1010040b0f0304000210b40f04005802c085 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 784311411 1250 784310161 784310173
    0x4080604060b09060a0f060f11031c1d0a110a030b09010e010f09050a0b071b05030c06010b07080f180603090a03021e15090313080304150e06030c0306010e03 69
    0x30408075401c002d018140940360140d0340d4640005014000d078007405007070030110002405100c11071160100c007200c0740e100d160152003800848062411588070301412510419051200d40c0720840a0080c01031503004860703108030580ba0f14842940b00c2000b400010408201c1c4013441c0415500d900102c0d000d56009601005c0707600301140014001c103a02c405082e03881d4201288242580e90314414461020340013070280c00444415035a15203002d500421041c04d020980302d03621803011592084014a6200c2c00055541300b088580e8186841c005134402651100100803400015001c8400e4602069040002c25110f11000312403241c0340018400c4690059404030030031008002c0014040c44070382c02131302500d020081c2c0c150b007038004505050170aa819030140c2c8442070840459041180c2c81140030302a01d0500c0f08411406000401a81c0710f5441340d40b0108003480349a400c0880d00d03020402c10b08149846844100c041459404000c229607008100440003c180381d003d08104e6442080040c1a688 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 784312661 1250 784311411 784311413
    0x1021207080c09010909020a171303140a1b061413110a060e010c0203010e03070311100e0a030804050a06050c0a030b0108040c1217030103030819021606050a0204080604 74
    0x1516100840e62000080d07680740104403881c207070500302c45072408103030344c3c1c1d404240c04c06240401940c043d00c941003c01c082010168110300700801494000c841c402c41c03010107503040b8200203054810200040685503810046910001d4000142e085c3c4000445000300e04203100f400d103071005100b00c1000702c0c0544201010000d20030030f21580c6841d514440e0311854603d44903041800b5288415000e0200814804141402198060803000d03000300d200400105441e0a801c02e00c07030035a04201030840c041140c1031185190b80e1011321825410b0404020704000c40d0040031001c03035584003e40d20180c03e00c40e201000c81d0900105101c0c031105141c100300240600d0422004200065010788410300000e4076204001c0502c3d8820308000c0e01464000c442c0030203241c01e0001d14944d409507000204c45406040100c064101d6085000c2c0d07008500075160292540f610480c0700790348850051584241d103204000b51201c202c2e040c4014608507400501c009100e69074016214000c0c4202c0e000038000344642c40c1000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 784313911 1250 784312661 784312687
    0x152001051f060e030604061508030c030a09170309060a091e090c02070f170a0b04060203010614030103210e0604080a020310060f15021e01050601023d09050102 70
    0x1c00540d90903035010103103555810071202030040700100caa00d600034102140c0482c4045d041051031001005803102c4240e5121015031465001c10b010400303d4001054040150341c0203440e44005140d1903403602d015074880e00c0300a4507445000191889240c01080c1080094451040103000d000e45241c40703500361510001a00d00c0d41014442e22946038203051780c0410903032002c2071800c11244414800044542810600010134048041221540c4124031155000c54074261803240154080c2c3d60050f901d505080300182079500094008030940020001000061508801412100360740c160410503404d101d04110f40c2c0e28001042c2c0c541c800c1012501060207372000c0b85642201d07200324121155980c1c00303228a02a03403000d1040d11205c0741010020081c141d0b442400c40c806113100d2060301e8520400040042c00d80d1301010304500507a550301e003082030a50b010842c0c00c1003900c0013a41100310850000c194510618142e00b9080c103101c8420364100203166503006a245164860000e54441d03040c40d01030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 784315161 1250 784313911 784313941
    0x11e050105031f0b1c060c020c0d020f1f090f0608040809010c0507050a171908040302011211031602100506030d110a050d030212070504050108040605151003060602010b0a15200105 79
    0x6560451800f00001d0010b0b00001d012054403000ad021054001429020400310b4210806895000950b0095001c3c1d0110a0360054092100fa911401c3d2950300b004513801c00088940c111000344071112041c030000c1102501031f5080c44200b440c3ca51500103407440c0c0641070082503403080b9004002c109020034813000c1d00c040d4400c0c0090140c100c0300c50281c1d4814424001d11241405406440200018400765100760b8082107000c1309560042140c0c550380005001740d83c003c650302e1500e6090aa0f283d4009641030000380c1c00b0a10088050046041c0030000940701c40c0100d14010601c00c1c10301003005605003d2096022030764002e000d071004664103081c0038002e58045464030712807801e0394000500f242e00510030b403002c1d58010ba5821072981e0740d039038540340141000307424010f103100554210a199580c080505821024079600862498584807000e800d403072a40042602c0b45c41c4a04040c03082c1340b8100742c0031200d115546480c40748000c07280e0701002c10000c1c1c0d031968015542440204000c01803c1002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 784316411 1250 784315161 784315163
    0x203060604030b060d050f1c020a1505040503120403031406010c150f2009010f05120a05061c05010605041116020f040e0d08060a091109151308011e050105031f0b1c 72
    0xb01c2410f851062310880e1180410000202001000c02c080d50f0309210f035a0020354031600c40d00442c0c2c178041205111242d006402c560840c0000d4540c14101c000c200c5020b4019000007007800c00f1103c1061030342e255241400340d01503c440b080c2d5a40d00002c02d10403160002500050b503003424000d482803d1344039404a6108510711800315200c1085000388605c02c208a031000c03080050390b844141c46010703101000d003101602d0a0303408000c0406041460032902107401a4920032400021910701c0c100c00d100948450980c400140c11041c014a0100c82510250b080f8181d81191507900f402c03400030005005240036107201c0100d126a50f501d1907580e0308800301501541084075405d0305590360702104019103940c0300c05040c00050502a03407956050500041c0c05030800d04000d6402e02d005e0071010400c84000760302665881e9154015000d85000e600705404003120424014000340d8101008a50369201c0f9986ca0300a05102e818041c2d4103040315841001d8401d07004048803511003440d01e2180b9507401401c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 784317661 1250 784316411 784316443
    0x60f1303020f030c0303160606030c061805010206091005040f06140103030e030105070915022e0608010c0c121407080301060314040b340309150203060604030b060d050f 74
    0x1640c0b101460002514290110001c00443c81d00f10400180c10704a00564400ca581c2529070201200040e00741c0c8990000c0c1c46039544c0c02c9030820084841860b011401d130302c168190b41000b000e100b9502c0c0e0201d1440701500035004d0108582c1c90703078030f000380e05500c0440001d0400c41c64510b102109408541003641203901a55135110215001ca04040c02c03104280c031201d020074045c42c001c0084039910031003894543c4039030050f902042d1007481c224606a1980f10f04040080104040d005040b00c103100310405011484001c00042c1810000940300040a05000e082c0020a0a0a013000344c407034103040c448039003802ea02c00d403204d40758900491503400038041e42020a0600b140f03d000d82e6080a08a407140b0303040f074002855601c42a1a950865512001c0300f0b000114035001c1c0d01d80c000b08991400045e4031150340010310907806050800d42d50707014048a8040500400034030034141d40d138409941c2540d401140e5a079194403a07500117a1549000c0700014039a01544140b007500900214505448081d030071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 784318911 1250 784317661 784317679
    0x41503090b0a1a09220b01092f0c0307050a290613050c07050708070806060907020726060403020c01120b0102070e0709080a08090a0905190902060f130302 68
    0x150184040ea4050f40c84200140c20003201c4100c10328128800f150840b540c003d040b05202034841e0036810a16803200142e03040c044c0c2c1d40c0100514040342c8542c070b80c1d000011200a00582055843c081c400e00d8182d0103220340800421240c5c06003605000322081140e100341250380b00401f6141140d489107840200c8240c0380d40d03882144212032410b0040511410300100000500c030b0740741e52284014400038020462202c4107120f8200040c2c010004a000351051070000c2540d646004c0d28649852001400e003401171040c00b003800b05241d000102d207403d40b40d4190300d1341030001c40390520386007081c00d41c956114103100da04244410b054010600040465081c0e9886034110384401404050f5000c1440041c01648400b4040064aa503d07001c00c0d08914549040c201c000c0d85d4060ac0c900c0c00881070030607200c1900005000615250014bc104010413035041e0600961030105071080042658400d60140243c40302d01c450110f5581d6012070718486000040591140e5501c0c469203000c0003d80022130080d4912 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 784320161 1250 784318911 784318921
    0x9080a060e2b08100513200c0a032307030f02010e01060810230f0106080f070903030f0c1e02040605150417010902030d03020c010c090303020303071103041503090b 72
    0x10b9100c2c00055001c4442580d004036020122000c03d00100380601d014444840403826685400d480094958031050100c2c8214852008074070400c45100003090b120000c0003050140c0c44003150070324034035401d030400c1c81c0c6000c80620b0b590203458a0303c8510703420340703800100801050740208150300c811515034020041c4144804440c0c1c220303076003801440c42c260b003c1d2007400c81901c8983c0161750850381508010021500c9207186212070b900c00c0d01c0c00e6480902200041c050680e01111650780821040702c4d104840c10980e00c0680350782140d01000d0304001400c0d2100f41c20038003501e80100b403d58022500d05509240f280c4800007610703040422031007182452000629440e00e4850701400e00d1900f0300040c54a40350054040f05081400b5002d0901d5499500e00700144e6800d10030707a406020740e0b450140c1e6500149810508550352800c0c42014000100014804243d0000c10780364040c0d0742c0c0c108102c210108082d06880d6000b161700c8400c1404451140b004030036419008121114400c07040b085081d222 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 784321411 1250 784320161 784320193
    0x1d03060103020a0b0a0912290c0f03220308060f1e04020703120609050105040605031501150509040e151b0d09022d0306010f0b03060607020109080a060e 67
    0x420711010b035001c074807a0014840a04030703000a01c0c1800f141e00301020280d640300d07026901c2400102c02624101206054030701c1d41c1c00c0e20481040c0c0800c1c40c0304c6410aa14048583c24202d004903600c0c0202040040001180107a0003a10701c0c264803914040b62089002524000709514400c440e1035021f85103e20051a16003801d410000d006030018001e0560345c0408400d100c001d400240054040200c00e00055503280700358480c52001c0c0030200004101e641c10301027800b0960b0165885107001c0c0c2d02621500c0303804090b003404141514030b00d505600003186440421102406403000d00da138050303d0005000400e00000501074448c41041022100507034400c4c000d03ca0500c0728400c4803014000400c1040820030240d445000424030080c6401020b0719541e1410301a41e8105404801929640418100d540b0703013000500e004003c0c024000714403a0900036058294000035140901554000c140703d01160f0080c034011010f0140c65007119241142d074109600070300f00001c240c0e11103000b40784851110184c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 784322661 1250 784321411 784321423
    0x402040b1b2515020a0b093003060f06090a0605030f1503060411030109060c1805030d0c0212071703030a180b0105010503070908010e03120c090d02060c010b101d03 72
    0x5004840264649408000460700c3d80b61460142140240c0241d040044c0307141c101c10317010741180002011281b24043c6810b541c070181001450400861120315072100303115200700e0341d000d4410b9032954500c40740c85001c0b030802e018806c1500d0740503482c10400b1030340a83c08006188600b64000201105454844110145400c03040d030058064001c1d00006000c80c4010410010560020700001448c41c45915528211580840131100003030001e091290500e41c2d1014440c0540720850142c0340080c040c41d00600b4021903290001d00501600d100c25040080601054005207058a811014085000310050b12a801145c12982061030159200001c10381c5d10004501a50304c070312200010303402d1000540d440c0c3c00050043c800c10458000121b1240020700901c5450080e6078011600c440c003041404080401c010404088448180401d4045907152505e10360703000c2d010b030b0f02607070744841c4000c881e4050300d0300005954100ea400c1c241042c4566000038161b4000701d0300b501c030012202401041545030340d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 784323911 1250 784322661 784322713
    0x9020f0d0f0b18060a09020f04060b031b070c06180e070e06070503210109060806090c0103093306052e0c1406250c0803060402040b1b 59
    0x120054007040c001119055501d0b08490320098002030302551040d003d24007001214000341586e215252481103080000c140c0b150f51104032014032146d4100320360040540001051907450000d04110742038007000010032903500a030005070902000ba00c0d0840540350b2444040d038650642c1e94807000082036200c12203a64080c0c24075954002e91000e80200300704503900840380a4401d40001c2004200b441e1850010420302c00508085040f15032400340c0703180072140e15601a50320750300828100000584082401041650242400130301c61400c0d051124a42e02d46100042ca40f0500940180c000802c49140d001c410241f41c806006036a210018408503140003030b40f82103c03001003811143d44d5403ea425454068846240c204c035a207840752220b45400c0502c000c0703510349410000c14003000c4d2001d030502d410030f1940740c030809070303159074203240280000c8040802411811010002c01c01541e123a40444004140e0401250381320400c0003401500d803180700120540074400c070555002d02c0e1403a260310b10015 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 784325161 1250 784323911 784323923
    0xc060103111f090623071202010e0c09040210050418060311040b0609040917070b04021002070e0408070c0f0801020909390408010e030705011109100f200109020f0d 72
    0xa520b412015108075080956000310003034448a02c074005007411700600601c82c010700105414401c0e40c10040d0071190022031043d002c1d0084446603422b616600d5074903401a81c16519552181140b4804035194040d81d0800340901c03451080ea0041446107406c80400c0e0b030701031072008041b041c5480801046039200d002071500048140300507026450594005c64600d402072440980007215504508580c0c0d000301000c1743c10307808420500042d403d04a41850180035580020030004d130a040890410180050008100341b80000d040c60400c200ba42504c001800c4458500e03052544561801307004c0d400030b01441e802070280d0000200401c1031440c140c048001c261444514200d1440510412403103c4200765070f440c0b00030030001510410904c11010140341240203161a065a440c260382581d950715034454072020244101c0b132041d035072136440e0225581035080c412000002404d013601c50070448140030492041440c1d4001c6040c4064000c4103a42d4070849003400c4610458082207982c064076107000c0c000b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 784326411 1250 784325161 784325177
    0x4120b0a0f291e040c09090204090f0e030c0303010e1317030712110d18080a05040302130207030806040e1e070f05010201150b0a140408030d0c260c0c060103111f 71
    0x4181444e90144000c5c2c405854103c0f03c50fa207406e41a8103907880303075000d400490360303c291700e400024880c4a03241c10101020302031450301d00d810301c81a580e404107005d1000d81c10b02c03020100b10302c2d000000340e11440640c01405090b9488804811243d0354004441e4031010039001d400740c003515141489a90303403641a0603035031403c0c0712801c442000148608001c40412201070b861040203c4c08800242107410742c5941c030103545504510621038a11841590401c946006100700e0300080e400c03000050b0711890907100050114400c80602e45800d01c10918401c09141821440b10444000704490042d05c02240c0b06e028801d0761400128222902c1c04250601c415103804203200034105903001708140b84a0b0710381006451011002c88c007169110790700c9000984c0c00003802d00920b9106010f44206054181051100349041922091010800c082c00300201c0da400400510404002002d98440c031004004032203141d0303107074581525011103a407002c1388644411503102010180c12081d500d44550300b940c80c001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 784327661 1250 784326411 784326469
    0x103111c150b060424030b0108090d110a06020d0207230c010c2111070501020724050903030a02070302130c0c173609040c030312023c04120b0a0f29 65
    0x1940084e108070710b0b0340c41c0110040704012500500103489040080100103a454b0740341d00d0051083c0070b20090050020310410012007030403002150301b4030850340a00700b0101810b03003441c00e5035103050b80201e075000102d484030b040c10200f54400d800700c01704402d11040740c083c241c0b039200580c2c2d0382c1031500c21104d00c400391003081c1580044101401c40d0f560702a0130410b0070306044030002401c1d03802c0741c5801001170f0700c00c03d010415854890904c250304856010304000c0300d642c011000309035010b0504003402020700d0381c20900c1da54004008039a00f14440b41003003142d14032050210524003090045503503440041340304000ea1403070131310b5020703000d00c1e40030040810305461340ea015101c1840b08000c201c2c100d0303400c0c4180744070588046caa8cc40d03c00801d4440002d2140a400700950341d641895105c3c85c01c0d8010310040c420452000040942c560f00116841c1243d6a081e2241014242e4454880c1400b410b1004066038418132041410007489007100105c280c654140170f00104075500852102c1701218814402 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 784328911 1250 784327661 784327667
    0x30702130b03030f09040b0d030f0f0e0d110f0301060b0d05090c01081f050303040b0a0201201b100e0d020d0203030c03040222050103111c150b060424030b0108090d 72
    0x922001d001c0c6c40464519540d200240240003000c0c2c00f50003141910352031b4118280e004140c2c00200c8442d00b042600400303240081440031420786801001003054455161041c0c1c0c90204c1d001e40307118001c1c02800301a071525040036007500079140300800c15007807601181d00240b001c01c4615031140183e5650f241503541d4100741a41040030381e07040c051000d02c00c20110799510148001d20241420300c4065580301a40d010090848801054058445c030382940780300b9560741c25001b204c14020307501d4246403154541c90542400d1841da1114004102d1405d02924403454000c28202d01044c0b9607000ea50210541c1031042c0c1c2c50344400c959404486800300f0001e001498405042c0d84000c6258060340c5407050300c10a44011510207030010b0752541e1000c04041206c0c0b501348080101403840b4000901041030701e40e03410480703070152030380a229283c45095070001c0e5101e00e41a00d0040c424680c2c60458031b2804d5000c2217045810000d1070001904181c103480455008140f207174000d0100354002c00141c803c0380011 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 784330161 1250 784328911 784328917
    0x51b0f1b060d020712090e0708010312030608160603050705120f0c0c01050f011703041a030619090c141801030c051c0e060a050405060a02030408040302090405030702130b03030f 78
    0x100794807840c1802540030a0009201425003148501d000000416007450301501c51503003079010308440e02d00802080481540421054110b80c1d0000f19488000f00300082640688055044158184180711801c0e2065100e08090011035040d40c60410860b29608400c07070f03281c0300300d000b11702c113614150000ca0701540001004a61105142105a0a00c40030141003401d580d01a60300c40d00206030380c0014020b0710300500450003180b008800446c98545082e09046640c1031202484682c80e00100c0050040e0b1244141080c034071000c288844007541c1c49150302d900814141c018800004d035952040545e141d006402c03208620311112403002d0803071824004501420ba1248040e0410005111000840242600d00c4100081190300400c042a050341454604a001400613002505000905c8003241d408600d1f55003240460401503501d6a503420000c245202c0c66200a400002d442c04120510001002400b10a80f00f240d040382074040c080b038041c0039100390710035055143e0000c0051082d040021303401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 784331411 1250 784330161 784330213
    0x6032a1e0301031b0b031906030b01181d1506040e06070c03020c010c020d02040c1404080a140102120115050405032d0a200a030507090b12030a020c06070303020d0c051b0f 75
    0x100b40952242d480031011002a4004cd4020541002c070b40b280e25500c0c060b131480f603c0300c002241d600d403010864090707890580c006900a00281c140100c1c000e40c4444e0080b02d0171000200c121401428455001410345404243c1500140688203003407010703603c40d640815901c1d03001040c81c144c0118503003c000041240380441420300500e92500282c12810901038002404250064400c04041d810021108001032031212101d900c104000103214444250f0303a41554858000c50041d201b100030305035000d2007a5001213603d441080200e171101d0340c030b081c1c0c81d0b800e2852070580304401c92818000196038000e902e000818800b0520240d0381d21a000c40710454190000600991400d40c1d251240750401c00709801c80003105031207480002240c10806250016a0200401140b81480141009448403100d807100c605c070703403000502002803500c00d8060307450380d0103507246c20400301d4240c0713002a0065206a45042d03d0700f81181a41d14448000b01c1c2c1b05400c4a0f855001d000045d030320b50318a03c0c01c80b9801c20 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 784332661 1250 784331411 784331461
    0xb06030105130212010621020702060409091406091e0d0212090d021809010b010504030c1202040f0f0510090603031709010e0d170606032a1e0301031b0b03 68
    0x4c0980402020440035038000c1202d500d46c107000c0140c01d4003803031080c407090251a442d503004000c5400180c8503001103070100c0304042e000142c03500d4031b8640032031740c068a4103025031948210401e10028030004a1001d0304881001000040030000c100420744514400c590100560050411400600340c0070b0000c4c54541c00080201042e04019800680d03c041070038041800002342504000c0b40d103100b44a01c007050082400d0050605140d555030464000440c001e6034521881c0310084c1c411503c42c1d8001540c0d00d80702d001c080c4a03904c8403108138030042100311a2203c0340e90320724000040c5011580300710000c1d20b40550710b107140c2e500485551404400082d042d90015966004005802142841781c1c2081c2c0c80c00783d40303042410344122031031402098090101c0b03214074030800c00e001c107940024400c0c00742c0c1e5102a0420206d074000e201e403114140100800703520a203d00c9084105030000010046d8181d07403041c01c0380d4a084142d80c070071020554141c060115045000c0011034503512400700c01c043e81c82c070905 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 784333911 1250 784332661 784332667
    0x50f010e0102070b0d0603060b01090302030d0f02160b090901051027090e060a0b031c1b230f1c1407080d020a02010f0c081503030c06010b09010207090b060301051302 73
    0x13206050562180e584050a5591840d050003004107a01034025800424a0100c10325420354001980300c5941084600078000080341c03400d8094001e100c481c0070030301980755640041e55030715601040790b8490000301e84905950000031581d894a4124000101200d50343c2141d40b1540c0400301c00d4410062000b0309050482e00701c0001d00030628003135403010801034000380201ccd0400c02c60035010303a0103c0101c18030a40008502006192014030000728100045c03a0a40c10b00c540d910990078000201e07035014041070800421780c188150080c104504090b546800c039584070301d1090205483e400e039031682e400b154a0207400300c01694840d41000000b08081c007a1145844542d40e40c64241c2d601510028a2076600440c0d10103c50750207106241442c0c2c00000705021084041500034036502d001000c2c03041c05030b540341c240030060302c080040c1d0743e0b007442c0305089503081e58441c25848607940168000314018442c5c80c801041d414024040c0c100c50000c080c2c042d5003180d013086c00300280b540008241d048116401c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 784335161 1250 784333911 784333919
    0x70605100e1b0c030f13060e0607120309060606081518060f011b1a012c0901060503161e1809060e0d0f020d1403041b0308030f1f050f010e010207 64
    0x10f000500c44c1240141c80951b0325081d03444400403440550740200140b0100002c0700301301d40c4880048681e000c0d40540d500241051541064004000139071002c0c00d035614000340402c0098121481c1d0b4003d4800c280449800142c100802c551030b21038011000a11203440007203440340c10520b100302c6d501d02050401c40a6076074024040c00601c01703003100035a50040c82e504a44542d6011000c0c3c5400340c05102c41071400c9207100b0f400360400700b0000a40041410701c070400500c41281c00e501620103850020180c50130550701c6010b542e010704050140c003502012941075402000360102000040700c20348000c41006d4007662490000030306021009407441501c518001c803036450180420800250b540d103030b070130206294140c002e1801d103054400320240503ca040e40e0054102000a480e40700e54032100ca10452100680512007811a075440246420310220520121054105000e0301c60b107004d40500c0e18010711170031f50140090051050982000008090301030360752040078603061261043c01207d0461341d031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 784336411 1250 784335161 784335163
    0x4030206091507050303060f01260718093603030c03060510030c110d172a1e0403020105040509040614011404140f0112031e05070605100e1b0c 63
    0x5003c01c454036000001000410302d0300c0b581010408030b0a180c207040180028590302c0060800381c40801840e51311500154045100b00314000340400d06002004450750340d8410400a409082c6801e9122148940c610342c10041000060032060080d40040c804581c4c00d48042e002804058880c40405071210780c041629111801100c258003801d58000032106560f075001001c0049100408060382c01c10040c022401e40c0c04001020404062132514040f07407940c0c0c81e44c01e031008200b44418071429000320000140014400130b050311070311000c654440040c3d004a01c041520503400000d0100324140310070b20460812a01555206100c2c0b400016000c0c120b12078111f45150980c454100d034180b110707082c92103007000e00401006071400d011030790310790410008840509074140244c50f1100a02d010417418980325003611040804079004040c1c90b00c40c511802000e40d804100243e441c3d0341000c0101d1220401c501084040310500071321152542c0710891000c00f81d600103048004220420300100350603001c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 784337661 1250 784336411 784336417
    0xa0c08040b09010806241b0a110a0602060118050613050f180102090a061119030507020405010b030712111213052404062003040b01030501050901020c03040302060915 73
    0xc0e00c4200d01d0b48880890300010200c960042400b801540340000928044000c481042460684c800006031112507005e4031320f00c0120554482c4040d480746120003003e100001e1644880e0000544503244a42c0d1503100a0b40d0340c80c4284a50299901c0720f0300b1203103058010b0f5010980041c001042c83c00b40701c0b44c3c0c56105040d5201501d500c89030389206014170400014107168041c0480201c0002c1d41084d800100142c0440103c1c4140c10501030070f141c80d160006024088000340c54440200c4102101481c10010301b940c0040600301e00991034040003242c0b0071015010b89108003045e603510b845182d250020480540b1451000041481d428404010340e02440e000451217082c0d404641180340c1042d040c040d140000c00c07031015201c111451003101000c00d807071035241d5100b0b401c03d030040b408444464010070200000e2a4500e01e00740040300b0b10040080040049040700c0c080c1d0000d1005841c1d200b060b5080344184025040d80d60b10401040005040ca64064038076048010010003c00d00c840c0a1409968 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 784338911 1250 784337661 784337669
    0x2a1c081302040510050102070501020a0807080a091e15050c1f020408070e0a0f0c081f0e0405010c091703090904050c090c0a14030105090103150b1002010603110d0201050f0a0c0804 79
    0x21400071300a2110b541d040010b000104400d10080150701000c0c0c48012441c42100760103400c403600002c42401c8103001c0c103038140051412080405003074000342010036240b02207002e1020140e180c0024980d0252146055500e084540006411009003000302c0312202d520107141760b100f2540038080050f1000003031001c14000d01d0400c1141c2780d1441d20407400c0003101c120200e4850a42c0c0380410200c0300719841740000d0391040f404412030172500d10000d406106020503038856916030315008200001c11070190000520014070f03880d015100d40d01d8100940452a801c225040344c1e6005101503070051500c0107200b50014000d0302036848511007040072400307003241103800c60341614000076601e40710ba0307101c07418940c0c400300e0200981c00d42d41000000b458450042c070024050503004d00840100c0000c9503c0014518001800980c2040701010301a010344010711081e540d03107412a00c100e0250600084180c0003a6050792114684015040e0180458000d9030660b03040061139941c2d400020010001840a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 784340161 1250 784338911 784338931
    0x9060417151302010813030503010b0a051201032a0e070e0409050a210e0d03030f290a0b0f09060a090e010e0a05090316080d0906022a1c0813020405 65
    0x52054000034100c0c04000c1d00c511070411b00c00d09144042031b40710059a0540d071f0103001c00d996910a0b0300d4215843c0c0500101d140403000000000010440701220b10007030185100f03c0d0955440152000b50190000b52240a01c2001d0000000b6841407113000380e011500c1c0014000120300542e0b88829240150301d903001c0320a8005070903030303428151155a20402504040c589002103001070350208010302c0b05d10313400038203060321250045120401500000d0750894241d641c04402d81a5588103d4026107c0c48998050f0003550b4010501692400894010000a06e81145011074020034014640d109010700810441c100002183d00100074809038001d01950700036056500744600480308072070300a010300c0b030035600800103034a04080c40300c0900f40346504007011548a03131170303502880040e00040d00300400340b5100050804050230000e2400f0527400f55802c9818810408000a9135141880002d920300b03c0024801d84814910441c005035009242c05c074102c1c240826580481c043d600c054400b1910 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 784341411 1250 784340161 784340191
    0x1218030b09011118010503100815010f0527060f0619180521030c010903110105090105220602041805040308091204030b0c09031204080d050906041715 66
    0x15549090003080c0d195000c101c800751801c405130b00c207007958042200095050100210004032469003444090008101c100142d400c8104920a40000c11a09004d40700314240d040a01117858104540c003405140c1200070040352118554442d0080b44100034016944140c104200404507113581c0081d00c0c00c41d1001da03070030b80302c3c40702c1c2540500881c540d420b0300702c0c00c032070328000411040d550000850010720920074000050040c48901c0707420361003040340c03141702903080c0a000820107078401e42910022110304001c02450302c0f40d14110f800c3e1502a1000c030304010181c0d009a00780b180e501070400300306104e0a070040c60f0590364140c10102c178007024003202032141d031001007000741601701d05816031012050300030303140c20300282010711601d000720b00018109000c0c180014803442025001c50703079004002800c940445220480103030050340300f40506801800b07050074200c8164002c04c1a110064401000a420f00c0e08222200828101c1034903071060b14030031128040e044071b03c1e602d40c4078081c8030381001c80c800c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 784342661 1250 784341411 784341421
    0xb0405060304140f161a090405070c06060f1a0301080a020120100f0c02070303080a0c17010b03100b1611030c0d05060108070b0c0705120336010e0109031218030b 71
    0x2204417050b80c400d42162040c000340100c8220228101c6100302c0003103c00151a844d40041150743c5507a01c10028807280c81e10303802049032522820018100e901004c1507a840e58101c00c0404002d0000f881800348560095000000540c0030710300f804000d07103544009081c00032594100502e8005d24100c0c040c0c115544068616070a00d0303601510400031024002403038140d256075001131100d040240702810310f55403403000003903541c0710300412a1a4841d0420fa160703556126101461294016200110071b0140440e00050340d4900c4070130b030707500c000c0c942c804401e51905e5030700e82070907900c6000b00e0070b5410300600004002a90711400300c602d80a0242005040a6051801940c50710b1300d9500134040b00c2c00107015034030045d94005094400e071107050300e032130841c5412400307081d14500450035007201c0032401440558a80c220700100c0810880e1412035400030b192000015903a80c80310864a600145c81c05100b0b001142300c845501c840541c0328076102982c4518010002d8440e17045070400c84400c0c07e82c0302401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 784343911 1250 784342661 784342693
    0x6180521040e131b060c150e12030a06030f11040e0a0b07080c0c03070309031b14040903030b06030403030f0c110a060e0f01020a050309010609060b031302370f0b0405060304140f 78
    0x92148001f240c400c000300c40b8141141c5075100daa06840c01d810100c000000b07003c0708501e0308002e00a5600100118440d80c052503c1d0f40740449a50311903000f20300e841003007502d0710000030b030060403c0c2e04190100c429172150541111078800044c0b100a49010810001d0708950703041000704a940d000c1c2d034600850741d0031450080b501050706c903a910a11010035009006900c47e0034a41e24940c8402c0b6800078001c03070701e80740179000380484202d9903500c410080b0802040c1501600140c0c02100051f00400c06100e0184003903503c06080b111100040d07108501c0000003034002d500c81d0114406980c11118140183c0c00c44500b640e108040500c0010004000d00080c08000d005d40c801411813110700303000c030f141854809106400f005111150312032514401c03400703545030100c000c4040c01c440010f07101035082207080114001036001c0c484030710303981c80000055042c81000024094070f881200300d44c549440d180800000f80c01c0540203450f00c041038a08520200b030204403103900d0924450281c03006030f07450500c0e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 784345161 1250 784343911 784343933
    0x4180c0902090d0b0c0c1e070b2101170705091512010e070609060212090d0308070311040308030105120a0309090e0c04230c070c050d06180521040e131b060c 69
    0x21030010810144c5e090441f4041400810b44e01d92000ca45d03160f2191a000c5015144108031400000c92008000b2070503500301120b0122480d100b80488144c41c1d40c0d4000e02c003642c0400c450154a803070324040302c1516450701400c110920745900f00080f82d01c00c3c504409904002c0c1c9684448040303a0211010480b0700e40502c902030b8402030200d0f010b81003242c2c01010504160060740300030308110130f074000288601e02a902100c40000500e941c1c50311551245002441e0f03034402c2c051944103807954441c0426140780022034814080d4190f445c083e01c83c2ca05041c06000d01505508235070380b80603007800803510341c80758440e00308071071001c0384102c0000c030107440b4146207071502a159136074006081026030007065042c010030080340c00a42d4510b8801080b030401100a11090f40c0d104070030003003101014107000c40054405214107601da90151281c030a0041c825017880346200c1d05850350301500014559200c0201c40c00120380c001c13188030356141c054080c0d0b4908070000b9000b007008100c00c004130005100f100c2d481 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 784346411 1250 784345161 784345183
    0x1206060d02091807140f0f06070b2701061703180405070e06030f0103020a0608010b03070f0903060f0c0305130c1701091209080d08040b0f0403030b1e04180c0902090d0b0c0c 76
    0xc451610400480823407454800e0702e40c007520002480c1c001c0791510b44541501c41882641c5d0100b1500070054450b054041c02c0c0a200c0c01d0461400e003c600b05507140040101e8141502c51801111032031203210501002d00401001ca10601011100c9a10f840d00c641008511560b01740740075510546c1140304111006007150032080c1001900c4005100700c0c220f0741c04407034100c0780b50305001da4000c040c8030086807050720340d0304000c041c0c07401d005000321400d85039044041424101c0c5c50910840d0303209400c4014159250728041e0044405007810418041c0e9090000301810104002281d82d42039901e0312044a21003281e2000050100c260030820301c401480505401819881c1100140c10a900c44900d00c01000d07007510981070040b4041f408240c0a603100919150019003000b42d80710300d100090a00c049109041c1d4012410401004008007000d41180311a84d8001c1810390b100e402c1c070705100c000350042440150407001d41c4c00c0000201c1c02c00c1080500c111518a0141c0da158007010312103082080c0e14403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 784347661 1250 784346411 784346419
    0x8190e0a082a0a200d03031b0203090d14030723010f1b080601121d060a0c050a05130f090e1606021b0102101103061206060d02091807140f 61
    0x8a0702d64400008900450b00d00d070000200e40024180076000100e0300d120040d003980c010500825201010b4040d0040c0400b0f0210300c00c0007401c11084401a070b00c03849411642c2d44c1c0080d0a200100c00104039000188007920140c2c112800d01003140c0e66220910000058002d888a2030071050302c0741d0340c00340140340303200740246810301185a01c8580b20348644540c0249809000e0b85400180076640308038170342c80c0c91540719082031091b140c1c0141c16080765420340c880403a89000f0f500014210009074091b141030305000c0d0703071802d00d05880030800f00e920b9000b05034951030b10140381d4800100220b4960709100074101070080000c55001e4142071902d070251380b00307200c00c01c02c3c11240c040020640201e1403235541a50540c4194090304500f00403800d0103850034000100e0342c40d1200c82421101064080c600c501e03010b41d140c03000043e4110407a9600d48040302e805070300c190040b01003001070400500d80380e001083c10b4401d0b00f40e0952040c00314105600c82c0c1010030f41c0013507001c03850b0803890107404000c09400251 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 784348911 1250 784347661 784347727
    0x109030c2006070204230a0b04060605030c07030305070c050a0c21020a03060b0402071b03140a0507151e030c03060b070b0a0b030f060f010815060108190e0a08 70
    0x10085002c5014100300a84030301d41d1b85000a80c0400d8118034110418017041c1180c1841c50400c0c0c0081c0203000505406001d640781420101e80c0d207002b00c007203c1c0520803898101e0704140b641d5a0407405418000d00e40410032921415500c00a4020003490710002d1140221030945410043c4280041510703008041c48002d00340a904096100c1502003000d40350001c41c085800003488002c90041c0c4180703c001803010ba0b505800f400e01d00f03a01003940381981d202d501e002c2e4103e81c04e01040c544c0c030381800802802c940c00964040000422000307100c2010585400c1101c546100c4000349171001071b50324221004603441d444001000f41c1d15106034809050140951400d0010584071111b58040041800c40902c1c0c1ea22442c02041c1d5082101c5450810303140c2c1213410340c1c80e0440404410070028825580f90744228151103210300c81c04d0200c584101c406079100c0390150788405002c40702e1038035810005001907507042e06540000003840541d81c154011021646d40707403203110040306100b0b202c0009400399070b02c0c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 784350161 1250 784348911 784348973
    0x414070906020d0509100e0f0a0905060f040c05160f06110a090501140d050a140424090f020609010306090f0b010e1207050618031f140601051605030c0109030c 70
    0x1012101107841c02c0381f0304044a00c1d20040800c24290b9503040701c070350003240300c0360009090b0901d400042c8220819541c3d13001c04904c050902080d211003a1a8101142e42072100ca9205443d8905c50004030340100c2c1d00e03c030901e40d95107608048a90f1700341d080f248010300041459405030040394038001000d0078605040f5071790007020901e0042c024107803000c0049484001007404016545c2120321070103010781010019044c9032508546140c030a07403c051403261500706d40a181300e6140701d102c140a0300240c5201400740c2990800206a00c61203169051507602d840200e9220a184500c150581100d44000741806160001514201400d016103204401203507001004040101700401295800d8940d0350326200c000d80e032055031035464400650184154001464580c0d881e40040700e41c0d20804004100d220b01c0c40341c6286494004070b40c0240071610401a0360035032815007041c014081d00420a40303082010b03e00c0c141e400d5401400e4203074001000f101028050041030304950610588042d1022400b401e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 784351411 1250 784350161 784350169
    0x15031c0315051201051e040c050d080d0f0b03100911091918060605030a05060c13090603080c16080d0e01170a0f0c090e040803060414070906020d0509 66
    0x104008410806458100c0c0d01e00400c009580d0308080e00b0010700000c0c804103c01d490380d00910040300c44013108014140400b41043d0070055142c0178a0b0040d10580420781800144803038004168030848032040208014008440948140804000240d20200d12094210700301440e108007002c1d150101803504080c940000c0300900784002404054030003080540d9901180c090005001c105492910b007440d003400707013440f00d040c50161171502c504c4c401c010307407600c400915030f40f0304c4441f10003400d40c1d203e40007040d01000040c000d00b807918030300004010060303100c8604806541c1c0340c0e841282c8680e0082084030384100244404038800e034082c600075500d140340c11085503603454000303818000d10550040d41c0a050b440342c81a00018071030b01000c10a0b03070802c1141000101804a000c010080c9000c0b40405494418440c2d0012200301741c4110496840d03544991b00540c1c0040d00c0e540d403040d5122211005401c00391225072095801c0e85070130348070500d4135402a00700600c001e00c440c100310741045205005d41da = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 784352517 1106 784351411 784351453
    0x9070908060c1c060b07030c0c0503030708123d15020607020c010f0518121e0d09053105150a050d0b060904050c0d0305031503 56
    0x32039000700f0850316640600089600100b002802192098140300103490090a000003c3c50f601d1000901c1c5501070902180c01c0d0401156130640010a012030356070003410071591103d1380270f01407405a0b072110785205071414500e0030181e100000c150041c0300c4029020000c00706440c1822500c0280d502d030412100000140728a03030920905511442c11400401c4181d03e4050412881081e5140c1008507202181d4000c2d502c106846d98002040010030b0042d030300f06201c8910751000604040c14107056200000078080d1040c020441600d400c1d21440c2d54062540d6403c5035a1784400d108603a00604e03541c00018203007040280000500c1c403203111134003294202c0f442d004055894040c440e0780303c410200903000c4e985810000d8218203250303905543c05882401a00c100100c168002603800c0c40b2500c059000460100070091210040034200d2041c00003200100040406010311108800c = true := by decide +kernel

theorem cover : BRFrame.Cov 784172661 784352517 := by
  have h0 := BRFrame.cov_init 784172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 784172661 ≤ n) (h2 : n < 784352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
