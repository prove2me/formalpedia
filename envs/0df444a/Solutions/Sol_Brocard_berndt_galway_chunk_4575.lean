-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4575
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:03:46.927016+00:00
-- url     : https://prove2.me/submissions/c731a771-7704-4997-b95f-97ec4b1306f0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 822661870 ≤ n < 822841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 822663120 1250 822661870 822661897
    0x90406022b02040306060f030201020312040318121103011b140c240a1a0f0105120702060a14091e07030b130c0611070341150912 57
    0x2401040c07080c004600c2000410442a400704050003003064610800002e080014102a219840c55000030340c0c0348104404a00c3c00070302c0d040032078101401240301c4452141c221000400141d1a0900518580741252007920011100c0400e00b10908040c0324419104203000301103906040ac864080d43c10709000a01d82101a10412071040101ea0901840080c2c83c01007081407070350202035041d5483d90300090325619080745400d010a038640300700303002102100c8090b40c40062207001400141c0352402000b8940c840d40802808014a1aa0100e00307607100da5003c172020000c0b264510503080049004450401d41e651200c00f03200c084060380744070381000351000001c850460fa12a40c998200d003205a9180002840070100a4204480b19883c18050b06039403501008080c54066255a01c3c9034510000c0c0c0004114002c2c17140140003840e070000301c841641400400c503a440d4220071034008005145005500510480461510200c07148034010b01e1150000c000e11b00003900b00300c5407a8000d80000880303 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 822664370 1250 822663120 822663157
    0x6180512070e040c05040b030706170c0405040c0305060a06090b030f0603011d0105150108090318040e1902040b0d0f11010c0b161202030c04061211030c0c0d0c0209040602 75
    0x10b90110388025210f50f21a1000c001014940340500050f1020309240c0c43c0710390840d500038000260b0062894071407a1a0a44104c41d948414825940f0380c41550440d6070060b0404040700c149503095008640500b40c29241000400d994604c101c81108c124010b54411600400c040f998114180c0340180d0000380050000594400c4410384950200c3c3d910071000f0a0307512001004020b10785542d2008401c0e03800c0c01d120000d0700c2c0c800c60107070326807003031705001c0c0d004090043c48100c05032510f511090b8402c1140e400c0381c4143d1300050f5001135400d130303100d022031050782403801700072207409c2500030040c0f03084e803042e902034030304405580d01203241c440c00c0c107030034100034010020402045c0d04002c42d034019402140d044183d40c5d81421700403c1c034007005402040c080c0c010014011040d000c0c004176811585186401619200c403070760302c0c2026006000c49178a2604010007400710034030221000300403c1104d1400c648000003264400c1e18102204d501c040d6200c0040c4d00007802183c4160010440311800c280e0f0340d0b44 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 822665620 1250 822664370 822664379
    0x305040c0902041503060b030f0103060c020a080a1106011d0402130b0a0e04110108070f0c05150a0c020f07030f0f080c0d081806060a290d150618051207 67
    0x101d803c103a11401100790742201510039240c01d48102000381a0482c600c919500d040d0081c021301c1001072000902a6565070840f2560603c00d002da08440742d44050003540d1920480e2000744802c0858a0003001e600400000280c001640c0311800b03c1c40100e280303509041c3e5500d4007004043c9801300c00441c0b000e80c82d4003120740e280d503d065004000c3d0840107401070072030030941000c1801204280780303181400500e00502c42001e40044102c1c1c5c6986e17151600110315001841c00328109280580b500f04403071480f030188038003d052900300c0300390f0050940c02c4a01080429020a40e220704c18800a814001c0181d0024040340980c178020891a010795005488c1000402d1710a182100158002c1c000480910502c03a40071540c81c0c0050f8000c0301c3ca801401c10b802c002000a001450520903504032440350f444110800000c5443c10107502529516980c86c0d02c40124110040c00440c0360000e018600940301003561401905210340000440003070080182c100342c28403190300300d424824001c52042100000707 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 822666870 1250 822665620 822665639
    0x50607030501300b10180f24030b270601050f010815010810171e07050f06031545131103010c030207110f01020303070309020109050904080a08010b04150305040c 71
    0x100781c541290002440ba200500020f044400e501c4482488600c0440058242c82302e0001070b1060b079400c0805202c6944030320003030f4103500d03403202c1c03124001c04000b0b40c1ca41c10701030001c039555040351000d456940d1004030140c01154040382c102c4003040507145000121109500c20b80e043d60380550003041c4489560346030a40c007001040700020b518801d030700104958100b8103101c000314100442d600010001c0e103040c400055200e03001001e42500070480031001811841c20041303440b08408000e08014482a03000008030341c020300c3c005c1c4d1004a0f102c01c6141c403801c0340d13030581c40c01d403041d444070201c04107511840e40c405101243e402c02925007208101c0c0205071a5001e104100d507211031500d00680e54081c03460600c6080e1a0124070310f115802d8218400307103a903008000caa074050b01c18a400643e02100e840141d448010300c1e00510f4100385120308110420082c00020103005000c2e0704e0b05e54040c0e07600c0b050b0101e58070807400b80e4141c40c4c1c60f0081740e600540c001d41140d500305110b0094045644d85034802034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 822668120 1250 822666870 822666899
    0x40201050d1a040c020718050c04030b0103030206070e010c020d020d05100204090b041514210d08190b06220833060901050f0d050607030501300b10 65
    0x202e0b000701107080d440c01d40d86030500c55100a40803e001030300034503161003241e44c0c02149503002c1e00c001d9a1604002038140c51168210b502640d0311107440740c102d503140d04009603a04000c642c00d80206034175080100041d805414040c800940c010084800e80074103600340907011007442d40841c5d00f40300d84444410428042d0001d00003400302e076100050103143c48bc1c1004180e83c108209040c0440c05d0383c500f8042014440c00002403a81d041e10180d00e982c5401d0032640303000c02a06422940ca014400d5400401c80d8011103807070003070482d100c9980703c0c84d900107000c03000c45145103080307640100d081001c03440e03200d000346084545800103041d030000141e440c5400e5003050b4084030740102000f405154025142c1c0c007000d001d58103c035507070714440c00d91901c0000300e884040103000d0644074035200f13062060f40d0303a1410840c0480c15031100564407241025080030380941028042c0000c410070481c003914045210300d032030507141180950f5900c2c4107845a140c08044030005803018050281e02c880100d100c004101342e9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 822669370 1250 822668120 822668141
    0x1030c060305040f0f152d02070b01090b0d0f060f0506040536070e01030c08060c030103030528090e060d02030c04020306040605061b0d08060f0111030d06031401180305030f040201050d 81
    0x104c1900015608041060310302010b0f201d511f41c810302244000c64200c0701411b05494080d40002400142c840010340e20940a01c2d0007080c029101f110202041142d030082d020007429034105010315211340c2c0400040d1082140e8602e101121010400d003100440d00d2000c104285e03031012030665018503c100760402919400c40c1014040f0100100200041480403000908011000e8140b0f414040985002e520061001604018021480b43c5a0b2040da40104560301202e0115001642000b10061300d0b03418144910004102c492002a40b1410588118942603a004001c2e105168a145c01c01c00290000303000d95402c20703a111400305840d150728004107030760000c2e9900340a001c2c04e4180c1031840c2001803d10344003004040010b000d400d0b128100c0400a0f0300c42401c00000d13000e280e2880780e1940c0110100c4c441502d06040300003040c0121341400e880341d00c5141000b17200202c000c040c1c07411181d024450050000d07004100045000c80003a90064116105240580c507202e20981d5400039254580301 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 822670620 1250 822669370 822669401
    0x5161b090b1f0f0807120203010e04060b0604140409060905010204120615060503070309050c040c180f2607080339030d021b010c050301030c060305040f0f15 69
    0x504a000e00e07100d100142a2a502d0a00300016000640c00402c118020344110f01030045071008079820134000c4142d00c90b1800c80850842d12980d580500c0d131003058003a50282c44840c52300c213408002d82007103000c68054400c0100c56004004081c1c080c040240680341c0f06560240d559980301c1c002507005e0001340300400511440c04801c0d40303103081c04400c81c0c150361104501c804460b1010000d01e9000000d5a03400350440c2000a404041e07800c14504184001541580c0a440d018403030204070342000140c500312a1942d01e40030700c031b5200c81d08241e025609028107104c03102d00301560b0038031100340a0450000350000c4203640102d0b41e203419492841c3c005000200100d45e02094032034581c80450015441d07060407a4555040955030404da5841384620410038a1054001500601006d5210381c1d4207854225080200020f819402d80102641c000380411a85000c1885001500340e21a0250302c0c019a04440c00f41141c0e411a0382c0c40002c420f15180071a40000d101029030054a901c0c81641070b00f40c0d4046 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 822671870 1250 822670620 822670631
    0x70b0c0a080108070509042d08041805130f0312060b03180d120509012d06290306041d0705030705030d1706060f0d0204140109030305161b09 62
    0x8102070550700050300988400d0f403000c18204440d69919503c41e8115801401c803070303584014003502d240da4261144000743d0304880c0d40b102d5402c0103800401801100c3c8034011500352080341c02000700070780f4004c9d40c200c680b40d104098503c020039070b07a800645c41c2ca80b0030b081c0f00864009e8079118200b900c03100e81c403500711142d02104201030030a4140610b0f45102070b41c80601186041e404010b047c0c0c1304000c244155655139030300050b0889009602c892482e8610b42044175640d407040180300d03020450300000c41c59483c1040b1001420101c420882c0c8204d405100c201c030890320700c0000d00111501f004202607402920350703810b01d0038000c541d410f4561110011014001603400c000501d4a010300b02da00950082d40091449181c080d48180020103030b054040c90085517442d00400100107009051404290200004802000c1450399004000b2184002c00f0300517045604001950508160310019000c524108403040c1d103940342c42a2014000d101d02d841903c40ba40b2446000d0708545a504910695507550 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 822673120 1250 822671870 822671887
    0x50301090c0905030a2003010f02090f04090c090c03110c03090306090c011b06240603110a09060e030a1b0305010f0917280c031130070b0c 61
    0x140181841210301c0d09004442c10701e414003096a5001950000e40014a04005951403510b0541071640021006009003c50580040420000c1d407004000713a1003000c075900703484d1050915006000c10380c0d030884c034013404462600740100017a29040000b00b0406584408078000d04d00d00002421241c10407000658035a45608281498502c02420b10041a804100c4800f9107a030f102c6113040101c0001070048902803054500316003d0034a046480883c8559001c00d0707101401445c0c904011610389560a0040141c0100c2105061040d030300c4060000321308040c14850700d03008005000406101804403009036086480e03040b40140c14000d03005442540000c100709202090140d030003018614070b020012043e0999400400c4420118003400b85103001c43c010450120040104414540400f916151049000f0f4000e140314080c2e08201c2c041400c3c1d02094403807400000b100c411044c0040485a502041240880520b01d13550000c0e43d0f010500f08030032800100343c1e4040310b0041800703d00d49034882094 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 822674370 1250 822673120 822673139
    0x20f06040c030b1f05010e041b0302120c03090312130507060f09080106050a030b100e090a060c0e0306070318050106170706020a05060a02132301080c07230a050607050301 75
    0x340000742d89224284204920b00c1c03c4d19481d0b0308940e000d00701610700510080104001d004e01e101c580701070034070183c4c03142440d68042c0c0080050b4107034800d0000b495070350420381c5000c07400f050702c005203c0c1d8028406540110720070f00c801ca400c00c0b109030250110303498969030a446c000b072039000b04000800300003c0b050580d40020011029048400091020314108004030318040c5036444050310155003100420b8032354003a299a40094a5614402c541c2c2b8986205801e070390f1000490308070b5042d403401102c54003980c4281c44026202800801425043e114090101c0c054051141c0c9402d03030080240706000054000d01c250401400070713229910b220b84590101d030381031051582c441c20641d08000c584000150002c00d10903840741c600c0500513241c0f0208401d59000001c1034108041c410705e4403d010314070f40c031055460426150300340d071444540e0b51050042075860251810040c030b001c210350f07070841206000300c0c80104c0507201141140c80348006512000e02d400300a4601402041c000001801403200703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 822675620 1250 822674370 822674393
    0x408030d09050618060f041406040f02090c04030b130819091505210709050406080307021905061204050a08120f06030d09051c0b0903180306010f0510020f06040c03 72
    0x840c801d04c2c252000001d551a80303c150040c00c16a00c6a00700b40001d0421549018200341c407003442c01210180d2400c6d140c00031800c105200c061f882420101c000424500c02602105c01f0782e42e01021540c115120740403c03a003906480402211481c0b800d1090182d4442d0f21b00510350204001e5841080c00c034909500034007805da460ba51402084010443d80c00b0341caa00300035040101c180d0140c4192a95945d400c100c4003552030707400103580281400400a0b10310310000280110b40e0007100c81261000300c251074010440d19600c1400d03002001481441ca0783ca2862807a298024012815200c4101c1c0c15a80c546160340002030424644051109101c0c0948021042c0d07a800b00b42034000f0540c80d008243e000d02000030782d2140522071402e0501046d041c800c1c2084110207581e00640450407402c06808594480d003080039040506008081c14082071310340050700ca41240c81c408110050242450244002d445000b682c9a0942c0729040480c19030303005c00c005d11449079028880030b0261500b107150a005012 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 822676870 1250 822675620 822675631
    0x3150918020a1d0c1308060c041d100909030e0409230309030c09040f1b1712040b0a0c1505181b0f0a0b13030515040c0b09060408030d090506 62
    0xe5450807000a074050841006070894410020b6540b1285d81a001e82c01c004001d40003440c003801460240282101903902070030980c0d441c804a8008a218440d0004110500705e8840c0030594480b001007059491340d9001e1b4155501911300250340d000e26001003400e03501c1c40c03039007102ca04034614042c01e0703011000066160503d10b0b010245203803281c81e100295480c030000c5070003440b50000f00b010034100050080b6a0050300d074080c01142402810704c001c0780741000c0c0d501c600214030711465040904060081030300f42c40941c0341611942818181a510519030308640c100c4014808002048004503051514a418100c8445404101c82c500046d2003e480047d2000f142c43d2603010154281d8403040c010600f8070708010503500320340303010316900008610400c150f02c40c40107810002804a45101d91000c1308042d01d01410444000c0390300c01c030346031202c0c903411100985450110b038070600603002d40300300900403d80f00400090506482e0551603003558001c0c400200340760303038a8000d1020080d05004095015 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 822678120 1250 822676870 822676889
    0xf0518150c0d020a0306051c11180a020a030b15091003062103033206010c0b0c0f07060c0f090509011415041203080a15120303150918020a 61
    0x80c102a00030400a008582e40300d02070741c0d00401c02c040301520940c0440010400240341089100400c81e0601402d480c2200a640c5c2002c000000c3d0f103a801c107000c000303c0100b07812002d0354480d41c407920b20b5002500070804a03c205600c0c0d095601700703550f03003c03a04101225078100321990390014400300074131444040c0381c18003410f082ca8020048041c164070461020518552410214005498120000e2000d00d804410900c101e1405000241c4070b800103501e001c10880906020f51103040040d82c04d500e0301c540c01008150b1580c0000d580b03460241c042c0c00315214a0351854100764150780d41c1410b81e0060b800704400140824003000c02698444200b4000300000d442150041d4140801480700f1345854200383e00815070114100f81c4007500707004032070007080e0366149540e000000381344c010249002680c0c405c14442c2000c030380c982e545840c1944d6a003140c406841c00031400210b9a402d9000d04418409030701958200c040016801c4a140a200c40c5000e10788a1050b0b1030400e4810040d19503510380042221 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 822679370 1250 822678120 822678163
    0x2007080a08101406032e060905120606100c080409022805090409110409050604020108090105010806070e190f090c080112110303040f12021f0917010f0518 68
    0x10681410030f040c1c00d0242075594035601c2d5640414030312440c2e03000c1c21000440041c0e04201c009041d01c0003078007041d41d955565000b9100d64030300810840344002410424550001d03001314140f4030389401c0c0b0016203034990400380201142900d03600d01d580c00c242e0168950070740000309000c40225480080206d91b40e131101403060884440001031140c0510804940a955240490302c18001e10702c1d00c44002410040c03007404484890f00e071081c2c9890080d45c040303010801d500082201c2c107206005040c140c45655000303244640d101001216035000d01500f49800482045d8803001c1c4545c0380082d24050040040c412428900d0b00d42c400c000c8807007180400c010044684014080d04e07803180030b03020b206038001d100c105040e1070b0040080c0c11403203582c1c032034618200d00000019101c000021102441b42c0219990684801b5003800c03e032105080700d004800150030030f06c0a01c817010740f4200c10003809001c2c500015002080102c51800c5417000d0340e0902141c0c1c4020700d441603800301040485440364180209402 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 822680620 1250 822679370 822679379
    0x12060f0616031803060e0d14070803060f0609043e0301050d11030d02010b090604021602010c21170709080d05090607020604090b03010e0c01050901032007080a0810 72
    0x81212103250000d08000f0b420012504041c3d803107584201540d0400e13030800400080c1a9065a2228200e10b100046001e5400303107095100704606031122288c00506492840e0340740020000c00c80d0b190302805a00c10401d03c03404a032601c1e036124a62076080300d220614a0302d1031144040c80708040c1b4981149004400842c00c0c2440000d000c01d0720b0450b00140c422644003c0c0ca03150440c280161440d81c0d5415101d91300400d40c4031135054100c0c201742c81098801718440c2d02d4050600043c1d10582c050201e151854034810801940710703a901d0b09826008601c03040d19940340b82c2500300d00480c091100b600140c0342141e00946d100050320255008509410301828061525400301e45406024080c0003c2c00302c0891303c842c0039141c00080340c2070030b5070082600c1c0e501da4507400d4440080c80e0003040d25000750700e0b1113031180384d01d20300188c1c5c2403454005849a605012050004402810701302c199a278081c0803800310184000845805400401d224042441d15846024002049494004d004010000c3c40400400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 822681870 1250 822680620 822680647
    0xc041503020108060a0b0c300906160602030910050a05010503070302131e06181406240f09011206030804092406020705040b040504020a09021c0212060f06 68
    0x2141e50a003840c0e45195208000260741e0781556005120500001408100c410f10102d8806170703528140d55000031070a1942002c034680c5c6018590415984010000d090b06440e00c100580340056101c4541d07914802a959404140c0e0000d4800082e140c0c00700919941600d2940640b03a40581c2e8a5403c0007039624080000740d0740e611501c400f03400f901810040364007140c22a0881c218048103002d10000390010301d9a140020310030303403140307046d01ca00e00c0c80c148081d1119401003952801600c2284001a140c00c410060f0b0384a4681070340100d02a04100031002a4004000c0c0c545101140c25154031064030750000352000c84407c00950440340b1f800414000541004244c8003038070f2040c00006004240c0c25140b1048407c010859008078003c0e03000026520750000301039050b940103a50a0021806110921040e194181c90081d80002039803400e00036520a907000e807050014294082c801180c40303440c10781c00ca9126904d010741c0d181d06001003024074101401070100550040d12050300e4025038a0158 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 822683120 1250 822681870 822681911
    0x1110f04091e020301120317070e0603150d0602041e060906050a05090301090b1816230a030b0901050c0a020a020f2809050705030912071b0e06030c04 66
    0xc030441c503501d2402402c8020101d040c40c80c034603050030045589503116401403114888551040300001c550041203d00c2381c0e1140300040c0a511540c4410215192a104021039904020304010020043d0b45400c003070359854002c400981d03030150b8001680c550520701c1c4a02c01e1306500e96004400d080d545800c020050380040c0c02012107401b403030056210fa5101c1003c481c28820f4500c0158598240090401407060f0180c15500078131000504040d030b80e0f4070312940c64070381807041d403500b40d000150402048280181032a18075054004c85840381903100b043d0001c2d0022003550401d40709101881c04000c40340400340300f00703504040002000343c02c1c03c1004400039520400414000e0103120110300c031382031036221240070318803031104020568000b00079140c01050085192054000715414140030414607402842202d020b0807442d4094840712444035110b12103940552001c40340440f0806200340303194010211000941054203191074503050000406142440001c016441180b4001c2c80c0002ca50940c24032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 822684370 1250 822683120 822683129
    0x290a150305150a06360b15090a0e160e030303060d0f02120118030e09070206040318050607061a01030506130e190c06090803090904060e0109020d030201050901110f04 73
    0x41c02c1d01d542c940740d14030b01500740c0340d000d040e0640d45112100c801d10013a100d0b131349064105a800503510b9404050f1300b010b0b6144481ca181c1c01c522244600700710342048400a00340c451001e06580e0519130b8492001514500848404401d030f003020038449660b5a2040d42c00074448801c40007142141022400115041c3c5041002050303140b403c92648110340f14a4101c03002c00705404003c0000c00007180d25001003140e80da000700d002640f00d2a002060b460121285400341d4844e5004000c0780d0307510b81e030075120b102e040248114964182d400018031643e4050007841c110b441114082110044080f07818205581c1c100c4d03041c1898102000c20005403654040185400c3d81090040758040c6040c400350705201d9040c60100ba10340000f52442c00380170701c40c0c0781813048603101e5541a01090751403850540708c0c06150305c10384d4440e00e10800300780440d51035000310000d031802c4800041d01c814241d0008604014030b00e8201d025035115420040e83c04003e12442c84030100022080b444d0090550400d019481207018 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 822685620 1250 822684370 822684403
    0x1213060302031312050301140a030819020a0c060207050a090b030606010f1101050112050c0d12050a09050603072c0102030910021906050a0507050a0516290a150305 72
    0xc02e000c3e404203600601c02c1e04850003508070750a2640041166100340075084582d031240009441030b0400c040600100c079041404141050813070a0b4003038100c0d24602d004011807007443c030304002040c4c0d9190064010011900200422490602400111007a950140785401e2078000c01c3d115985010404503449102403070801a0b0030390703804040c0c1c1c4441ca944006001586408004a96410102c400060540c0528111981c0001407010406c45083c40c0300d000348000640a0101d0b8120302039805407000d000981001100c681d1110302284203500100c801c90b0005403000e507220b200358820074540407010500c040f4505071065580010f542c030b11035491010700a1032000320200e02c0e1031081c02003076019441c03208281e186407102d0501c40c026180030784241c06120301c0c2c140803640fa140100200d44154100e901c0c1e460400c200100890038464011100b92140c1d0030407840b0780010b0440807005481c000240b540078480d400d0113890701c02100e107644961910b1030410320050011540018800c41c0c030300100031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 822686870 1250 822685620 822685627
    0x813030201020f0d0603210903110307030f0b0a0b0102010605030a08031b130911070b040b04112205060306040b0103080a0e031c030c14090f030c0909010501081213060302 75
    0x5800c80c020320503078a0b401168000400e80310f21003401600000c080f41d01030f401c50f1092052140300d100030b820701c242c8142c01140c030003031007000001c2000084080c0240000e040c1c440442d9a500c8005240300b103158100c0da02201242013094a402621420040081c00c1c8003c00446040001081d035510010101810140700480000d510503a01e00c200c0700c2e60000b40c214a511542c0000f403260b20611240600034526040401c0c1100701a034500a40d015076400c40460038140d1aa91114036914001a1050302c40700015100303898261141e203020100340d02100c1c0314004039503c04000808846010745890702c00c0e002103061102058103050002d040d680c00100c02d6544004150094410381e180900d80c41d010300896018003030900f154090f0150081c926141400800c1603030404440002c14010500c00c2c141c13051281440c10b042102c084025000040c1c2128684104a800100410304c00c03903100c0000d82d1518010b000c00c2c41c060000850302c65a441d0118240101c26445e001d480001d8000c0d0820540c0c040f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 822688120 1250 822686870 822686873
    0x313151a04051b0328060803030402121501060507050a0c06051b01060b0703030216141006060e100f0e04061212021f2a0e04060b0408030711061e09130c0813 69
    0x4900b803030202190804018855445890313039244c1c2c00496093303202d4682e80344092030003003000c46c1c1028500802c0d81f0300002a13082010a461030b4201702c40c01c1c3d8072840703800202c1d030014003003025680c080d0140303480300da1b1200040300031450400e0048140c00c40e03d034103000f0704000ba0941a0103444141e50b06040142e1a0794000055200c00c2c002e8190241160000b095066100d100200c0c3c041c00070710b4004800d00c00c03251102c02c1074891484954105d41c200101d00440780c015403003150340c03c100c1082841c00300981d20300b010000301510f00640260200b249080d06a42c20800040c0b4404103030201d50004e440c100c60700001811342a280340c0c80300c01d000c68440040221082d80003408404455500700c10840c00380d10540300409100d00c009040703004a10717040e0081003503201c0a040d1011210450015032a050281e658104004041c40106400c99401e0183d590f1060018900645502491300d6407500c074542441004840600340c8071703554610380391814044425601003a0303682c1c000400ca4040721202c589 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 822689370 1250 822688120 822688171
    0x221090c03150601020105161b08220e06030111040e0712110a17010b0a11010b0301021b0d05130303050711130c02160b0313151a04051b03 61
    0x244489501d8010407100700c150403a46010a4007a00080c1e0080010303949040000c103582810b52128408225440440d010340c0d400c03d064414228454600141480c5040b03412554044171425449800f09030301106120750405400784503801711040700240324541d01d1000120041c481c03409030b10510881000010440d40c01045035003141c5840100412004e0303205100600e498211488007400550101108464100c443c0d00c120705075000c141985d40303881d0030841d0a0b105030005900110680d521032407075003844e0b0340a00c080c2080e90940c105000011918500541c100710750121b0317000a000d030038000032540d030412000c2c1000352545420100c0c1e403010701c3e04104503005841c103c2170343d0000c80003000c0350b00c5503a650001114048031b1380880b0030705180764003038507103003849800340700c007805030610002c3c1c4031100c5400405145809603070032070712040c00085000b05a4800c020070003240202055044d0f180c0c00d041c8109603000d1444c440b0280000c1d0075900280c0988009460003000440b0340b25000715602d036 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 822690620 1250 822689370 822689383
    0x1526010e070c1e060b09063a0b010608010e070c110f0d0204050109020a030b09090c0108061f0504150e130506150304060f1103070f080a09120918022109 67
    0x181d41d20300700c3c80502c843c41c000c4050240805610b002c0e42010011071441e0414003821040013008404014801c0f05086648801140c0840c440300905150404038010a40003641c05010708101d80c0d4500c038941c189160807100c054090064010040b2f0340308842e01094840b1004990140201d030400d102ca44003800188400c050117401941c0140341100004d4094070175030090011034032580341032041d52419820418020021141c2020f15080710281c400650f21400071254070070402403c00002d045520b194850801c0205809008140005400d1000411005004901e0080c41ca011094000c020b80880c03d003a0403054400c003036a0b00c0c1c001082d0290395001c0000c9100442250042e241d10300f50506a010705103603030021000500d0f18801e20340c1402e5034400ca80c1300d817480342c07502041964580d4049074604002010365900320741e10305030341002800f11898200c60100c140d860303c090b5420024581801140c03071803c0d0032030601c104040140300c22600118a02c116a0035a40c490780d98403040e149007802c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 822691870 1250 822690620 822690653
    0x90b07150e0f0601060207050105030c030606040b030705180f1807110102070804050a0501091508041b080d080a0e0d110106090203090a0606090c12151526010e070c 72
    0x2401c01e841c1100d4000001008281e449400d021a4190b03645d400381641c485542d406118002142080080c0380041a00c00454100da80a4550751400d1794440350452150400d82d0743c440020030016494109161440070350929030070458011103208940400130301488820302c000c40c0070f440703128001106103001c1da011050020104009558450040c645081c3e164040d0155511601d10081e0204403540f1a4003e0001d660072003a20703614402c442c1c4c030b05591020303009008440030604203c00c5446c5c920584281c000406944009004032441d80300040c01095008140e24516890080354206005000402e8805a8010b04000008055105801e40501411341100072402c0c000010300100100000c6c0299400380192030070800540c0b1400108181c5403100c00f90310005081030103648034406540c0c8614180c3c5030400381c1000c5107590ba4000c94292070794030790b41c502188108a40d040c1801e0810990751800958140c014a958181070030796103003010151042003040380ca82d0304d0b00b0400c03044000700e48081 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 822693120 1250 822691870 822691913
    0x60a081b0336100c020f010c0203221d01090f050f130c0e07021c1b030f0c060f0e1603021f020703050303010b04050406090209030606011103120405010f06080d090b07 73
    0x511008440f040500340c1d19060b40d0040c4249000302d55021018400d900000016a01961402c444800c7e070200c0c1052683d40320410f01d00300c0000240c10b4010310464845514000342c0141550b14045030f0f24111a10740c20070301907180c1450200031003140100072080e07003c8501c074540c1a400787c0e241800c808038041354019001c01409042440078a640004030042d801c100c600b01c20500c4070403c0130840c2c5254040801d003071023064800515001900442c0140c0ca00002480c208403039040703e8880c04252108805441c00c99591410f11803007944092004d684c404a41e00a1829024990b03404a096414a02d4514a94030005182140c0d824804d04c0041c00450308402129100d507100e0b0002450340e800303440b895106034504003000032401014001d40b100c189000b0003804e5140d84400041d6040c076003101c894407050008100c0c1821020710302212074001c40c0500f000040098030300c200f2401b2102c06801400d11680b0076001e250741c1d02da010910400b6100c2e1070700c200c0d48803401c62402000301102520605d03c0c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 822694370 1250 822693120 822693133
    0xc0302130e1905010506270612011d01150b040306110702090709050a1a0d09020f06070f02090619090b180103030c06050106052d0702060a081b0336 65
    0x2e010031a00321110b41c00781c8020003603a200c070000c01960b1240d40b40c00320b038050801c0c0c101034240c2d0800e0f0b441c01c0c0d2012001d0260f82c1140aa800020b0864514102511842d03032051544000010700340306024030034400040c1d0000302410600c90741d04a0040340b100415242e1035a22003218065018180e980080c0c4c050074010b4a424005c3d40540414694043c40303001d100d0074000013070141d031280c1c1c0070113885024495035071404100101a4019240c4401d090341c02811050301582070307032291001016400d006011600030b03410b040c4100b05140c04054400e500c42c0740740f2500e03010440d0403405954103d40e618403000400111503008079000001c014070032089802403a000005040e0060740820304244038040c1005240e80300c0000f0756403800f40c24080c03c828417440160b255502e0810f0406004007082542c828240509680002e0503030344090140c0c0c0000c0e01020501040e420780d81c0161106038400c0955500314680302081c0c4031080300b4504507041e8180244010900d00310188408544070054000341c0f0103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 822695620 1250 822694370 822694393
    0x52d0d0c0608091212070e06040801150803042709021914090f0610030603050106080d0f11030304060902040b09010b092409210d022103040c0302130e 66
    0x10384554030300c1240045044400010305248011810104080406038114100b140740004121030034001040e0360103001c44561504403030740e100300262000700b81e041e0010800464030100181100307240c4c3e01203525070340288414441c2e40342600341219000009908001002004203000d00030b414091030117500b00f05044c500c0700381541421410015900148202c031143d031705110030b20100c00401c8803d110501340310004180c0e185014140f031b2603c1d01080c9400728040c0e840351600b40c2103540e141e018a40e943d1200b290859842c0d00030620480d44000f0f07091002203091003010203a141d1200034002050075a03aa1a40011541ca5074001101d803c400303444800341e5038581d45564371a83c0301c00c058a214503170880d2070420b05000c010509038810403401403203090162600500c40e1341c1e821091100360202c118143c03000026010010707000303050400da0091403003aa001d50b0742c112203192199030007a40e8600300204804a9600d9800e80110b9506881d0030840c01d981c0a000f20062001c013a5109550140c4084480c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 822696870 1250 822695620 822695633
    0xa0b091c060221040b01090e01020d062907050d08071b061409030a0903060f06030b10030308180616030609090f05060609011203110106050d060203100b0301052d0d 72
    0x4004900d141e00401240d00e10303500c3c2c3c0c0d4003002107400400d01c8a0308001072240f02140c0d00810f510840764030026080c030072120240020740e90641c000c814240a02644948403035107100740010241d588002d5145880070b0750311040d0311004007221010500c0100c602080034140f08044c90003000561104000350301405192040282c403400148940389490200482d144d41004021149407500c50303200c81590501e9507071881c001e4414400e12030800e680d51000000411a600d05141c810040c04400c0410241945406030031030b4000351148120b250740c40d0126801c036100003000ba0b00700c502450480341d240480e4004a000d08a547c00010300513081060b00000c0080d92050004602d21560660f100c86c2e80302c209010041c10240301e440c1d5000d000106000100b0b0150180200044040002040990302c44e4081140d04910034400c0b40d8050b8004104040e8a00741c12180b000341a004a80300e20b594513000c00114800d01011510f51042441290a07642503443c0c0d0025101c150090702c00c0307200740200c0c204130 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 822698120 1250 822696870 822696877
    0x40b0105190215070f11030f0a120e011d0d020601150c0c0306110403021509010903080c03040b041706060301112a0d0509100309150203040204020c1e0712020a0b091c0602 75
    0x8008900346c2205034200302404003d0b1400000301009642c201954103c0403035104204400396070400f81d8444203206944400e0154815550a411042c041d0300c0c800c0c0c420520340800d0410a400310b40024005018550303406125115080d41880c11001e41c0d0074504200d0329100d441d0380010441440d0843c2031601002c0003029100303d070b000f200c1040070017140420702c0105100d000d42e060b000900854085c400178031484050481e50614604480c02c0540360018034019a0203504643c0f80000350740d414080302d500408c0515402030013038000344070311101e20b03450307101e20300841512201100580e0070f40b1880079400e481e210135960080d001c85041c00301c5a10050a2603005a0006000d12030310301c8040e50241c042d019a80741b90f41c0c4004c82090402a15044200a4001a0080382d00a408116180c40010304004441d02d07034100c084100d407541d02080240b864207100743c0c018610128400c40340c80150f03540300040d408690009130a1690340c455080011410904005041e840949400c141010701c0100d0b8041c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 822699370 1250 822698120 822698147
    0x126010c082703040b130f030318081603020603090f011b020d110c040b0616150605033405090c040305011a030c13180b060f040b010519021507 63
    0x40450b00030341c2d89002d000344071500d404405140d004000400c0038402e039900030503d6206560302c0000958031604c40c500310400550040c0c00141c0b52040154410b08880f2507440105004d000038400110b140741031010818191002900c291070120018140385030a11070505900c2d0750340020010380030340318005503584044020050040c0302c0c0b5465024058040c1d000e10807501c8001c40148070305c0c0c3c1907004100c06400c003140e031a03170812418440d00d01000480342020410717501c42e0540d0307070040d501081078400303c60342680000c0c420382c0b00000c0e9039640c4403aa000c00c5180070700414000e00311600c480c2103902c2c1c1c1259030301032500078141404101d005900301d4003420a40f48904001d0040d0580140d042c00b0758080c20303ca240d0716821030300060840d4500030800d02c10111203001c000c41c8114290300510503401844005540701d141000820007145800d044550011204035010480404c0140008050740109800c25070300104c00d14407010014004c200c104040300503290501103914141c0c000a0241107010b84 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 822700620 1250 822699370 822699391
    0x3070804080d0e0306010e04061b050d2405010c02190e0a050106031a060309101a040510061407050102090d0305091c0203060c0d0207050a0501140f010e0126010c08 72
    0x244014140f203000881d450000080c010300580c2d0030200040002000035204440e0b095507656844440b2060100d6000c5140c0243c03289516403000c14651002e81e1181d00f4030501501c031500c1419552210780801c2d00c1501c40030328052100b0403040c40440d01c1070400b4002802d4884a078240092100880f9902c1880b40164401c00d000691340c0d0181501581c010050140c0e4411003807401440307504103900910351140d50700302103034400d0040d0f62040e411140c900200300303a080100b2803c0c406904050013100d4000010041700810b15103050001460a4904110b030b410100000441509210003501500c0c2a04001007000c4012900341c500034143c0c0d8007400d2140c0c0244802e8120b2104004551016500320741c010700900100e50b14114041c0056000d03010341005c143e42407003408003240341000900c1015104000018003034007229071280d1030800003801c0002c0b0f508540014001c01600206490440d204c980218500180b402910784540589030f00d00034142d81b134603840c076051503405125203018621900 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 822701870 1250 822700620 822700633
    0x6170307170c07090e0a0b090607020111030609060f01050f16060f0504020d021c05070b0c0705030625030618050f0c07021f020f100b150405030d0c0c080307080408 72
    0x1040703003075070164180007a100e0304000070422146045030001c10405840805441001d42160b83d00300900c2c0d4291038a1120754003050402c1086a0244031740f0114240384040326040d80303055000501030240041240e0301030b00d1203207070018607a40160103407104c2c0710907801240c1d22400c1030401d0024444001001360740780d606050280c400e454003442490300940d005081500003a0362502806481c0c080e1818807001040e1001400c0003180307043c4580c9000d00180c1079110303500c2c0ca070078800d21300c0c02c034450300060320a030440010b0020464040c480510410164080001c00000160050b401450168009080c4a80000b01c0003520440340e0b010501c180c0c40c441150f40b540c0c0303508031400303103500030803c0003500654002030500c111038079800714000b0524184110b03003010442d40c05107402d10014000203c5d155031600e4880c00790385060300003e42034081100303180e81403a10300000265180c450010780d2081c8550140350314140300c100c0d03031090003a0040100301c0390f50b107001c0c0c80d202209a0180c801c4100fa0302550 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 822703120 1250 822701870 822701903
    0x1e031311090105030a0303050408130902120a0c05070312110309030a03050c03150f040605120615101e1119060f020910120e01090c030302060f0708070302090406170307 74
    0x401c1950603210041e0080c0082c082e01d5600b40e009081c05041914a400c0c00d01000250030707210071401c000742c4088180940c13142c0c240d0070030b030703d02c0e010103031a941070305007041ea043c0041603001060703888490f01460082014465803e9103001420020b000b4150510000200403102d84c2c0000201903001082d60100420381c0c840030180c50f58081076900344000c80c44800c28007480e26141a6640420b94001c0c0001040c0b99504000755821002401e01880c60300421708200c0c0b0540f07417100c0c070807000905543c500c49102122030020301c01071403402e600140300e46840c0003c0c6901d00c2005000c4442590404507a4031204485e2001d2441c0c0e40b01c14201e031480e081a03a03560110509000782d9882003c003a142144000c0080c01c291858088010070361255940e40c00c460b2400102409441403031800758041403040e03404c604002382407042c0200720041100c0c00d4804d0041d91a400046141d101c0d006c1d1a0060f107070300c0454001809040c6c1d5601900e2038418060b181d04499201000402595109085255140c0f552 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 822704370 1250 822703120 822703129
    0x90b090d080601020304090905070909060506100903020102060708150d1b050316090e0a1a0114030102070f06181401020409150b03060f06070b0f04060c0c020d081e031311 75
    0x102c40040c0160004d001c00c024015460308007040c403d01c101d003580c40c007503113a000c0b610880c0c414020a4810312b45400c140501030824407603e030b1141009140403240141550000b0307503240c001400c145c0c200510340000902441c540c10000c402d0010003401c0081c140700504200c10b01d151500e8140d1140c146280700020f8a180000b43d80303014504100802d404107107010a00001410b840b032040049001e4400c408000030f1111400343e0302d1094a220b540318950500d0050103d0074818079166009070710402049000c141051072020560364081c6001c512070104001075080e00640060090603485011003600c24103406401420a5547c4d81d441040144415040010b6240461103840901d0904002048160074880284458100040c2500d450060300d80d8858005484c11a14110241c2060043c401001030034003c0b000b48005618241450b1221600082c504014840000300b082c6400110240031000c0c02c01c0704217a010203c422591280342001000c620f00f4907041c82105c1c0100e00d251500d015252 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 822705620 1250 822704370 822704387
    0x1d06220f0206030a0e06130b010e13060b010e060d050a0e0c0901090c0c0f11031e100203091c0c0309050a0614070c0f0f030c0b18060a0e04090b090d 65
    0x1005003620310006155001e10529510103400c1c040c0050311440e48000001042000038001c902c0105c900035541014103005540c0d1906130488400415200e00b808280c1412035824a16507811100001300c078141540182e035800901c4812980024002c2045500050f50340d000e203103d1000910b06205440500c003d05844131038011599600640040c01804500c0e165484040c1136451401d1140b505a526220f005034402031480860300d6824140c041d441c80c0c10f05201d000e201c1c28907161110a45008a040191900c40d454200f0a01c150702000085010504001d03900502d041c1103803041c846030b086078000300f1a05440c0c00640100c0c0240c08e000a50381002c50b03a803403c60307049944a000503200c60180d030721641c1c068807054a180c900c140c0c002c211240c0003001200104400c807501d0740c1551544c50300e1a00f131810b56108000e000002e0110f542004100024000344000848096590b9640c803002070385c84c3c0d6200809540c00c035181081e41001c01c084094524021083c02040310034130411900111000721 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 822706870 1250 822705620 822705623
    0xc0f010b0607081e040312020c04050c090105090d0204060b0301030b01120203030d0b06120106080105040e010e0a1b030503370c120c06021611010f02120d1d0622 71
    0x2004102e5440401d01000c081c20619411511410402d03550300f00c0c525a035000760f0420b0360340c1c3c902e64504580340c5070104044100304006490a010518111045000b00d001d242c182e1414000c0015031078171241d50b4071040160542d4024020042603440781d00034080c07a00b00740421540802900000304a207101030f000d10904a900800844c90020500307006000341c0301400506400c4541401550001c01c2004140c80c082c090550710000650300d8201044142c2d0035650034040680d00d05104c10003c80b4001c10204545900001301c01040585010601d4180c0f0041d40043c1560101040d40f41d40c6080c414504c0e0354040030004110041407220140408200340203106134085000050790b440081d49180005032110120b0400070014119901d9200903a80815900c80c110139041034800200001010005040b0000b86815070101c128514040d680344414420020140350114042c0d9640003903030001400050f03a041d141c42c040c607100c0d84284d62843e013620441b0340451485d02411066440b0b5071070241c42e9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 822708120 1250 822706870 822706879
    0xd120201060b25080405030d030e010c09180c05040824071d150d1d0f0102030412110307080c03090a0806101a071b09050901051005130f050c0c0f010b 66
    0x43c0010a001030f940711100d1401c5510301002d210014590741d05000e0062105140e890100d00701f002040e81d50308551a02c034140d0240198000140943c00700c96a500b000d14690311800181d05a201c002640d40d40140c1d44100b0042c444c01412a03068040a20041810f0a0740480c1c42c20075203c465095891100c4c03051080284841143d04108902d407807079000341c06000c03941c60145820200d2072038009a0315501002c1e03c0941c0d90310310014400c10100700001a80303a15200860640c1002c0c3d48141c201c400f502800380c108203118a00c00c950150501c201ca07429070380045510b9885008030340f56602d0b508940c5c9464403402000754001003114010503060b10600f01110030740304130360900a400b450f0700c0d401c240e80c0c590650140701e04000114585440081400c080202e003441313510b04511171041e108010030564099040000340500a00403424030310a0f03072007c5070007030601c20720118008001d11117801d06100e2030341007805104203025031500030130301c541a880075501d01100d00710300b607405e942000e114036410 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 822709370 1250 822708120 822708157
    0x50d0203040b090402031302061902060a090201170702070b0d1d16061d030601060302250309170f0610060909050405061308040801021c0f2310050d120201060b 70
    0xf81c0c5070a90046031b00141d8040040c3e0030890f940c011500c00e8001c4c1003501d621659448100948a80400205512071204e11003030000d40041c1d40001e02c400c000040113400d2201031008559000d0003400f80e28080e040c80c41d9640c0d2240b00c1d000c1c480e400340c2140300c1c4c655810500c1400c0f5910100e0007181041a00c01032248607483d203450b140003100c1e038401820070040c00b02900c0002c00c407160703003c2c819180203100700c1e42d0148e11512504080405800c2c804401d9410f09138502441d0000307a00401044219060004c0040701c0f030030a0041ca604082d001c1c0306200450041200300103004480241d658240c502c03d640e103440450321005a03008580b816039026200e5131002d40041c45081d0100804e2134440d200d48030b1182031550b9407004a00ba0f0700f00d854403c1c021220ba840c501030384107251150b0492846c20907010b200000c074130f44c00d060106800d0701030340440c0714490000401407104c4000e148014180600410070200583c10242e1001c220b480b1000e0040d420040e0000f54100d1600a9034400b8050740c040a0a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 822710620 1250 822709370 822709387
    0x90b03030c070e09010f1406040506224a0703030519050417032d0d0504081e09100207050603011707030b0a1a0907021020070f050d0203040b 62
    0x6080c010030541c1c4d0b43d07403680d000034061413560045170f50054410004045070b080281c02c001c243c8000900940c0241c0c01e040c840c0001d400b07010132005440d003038500001010304140301015190481c42140507045c0d080810030102680d103030600030b90702c2d481c054003001144840700c40c901d0701c459082c40090b0000d00c040c00094019000e03401c40514440282c12302601d450350f901050040c00102580c00c940c19040404c80100061088102c03c01440c1402d00a4400e4540c85654581c24091244103000c5c144d07503580040c1c1044041d81c112031400c510032007464140706402e00d4400b8146d020307804490055100006511140b8000184001921070042040d401c517820050300307821212001920361054892000d001001c00d0001028034000c00c083d80c00810542e0441c0c6a41d0071010441004074002c20440c0e0401661075030100e120399135841c84030000319481080424550554038002c1da1402c1180740010500300300042c076001c50f140a0710400503104101c1c020300303060780c5a0266124241c800d60301003000d0f00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 822711870 1250 822710620 822710639
    0x30a05040915080d2307021c020a030b13200a030311010f0c0e010e0306160507060b310501030c0312021006090609141b03040c030f030801090b03030c07 67
    0x401c030a0030b442110440c80d91800401c1c504003040d9042e10105030410355249100c0c9901030714803010710344440030030700d0451a41c1c085242040c040102d081030070032441c002c40031580c030000071000468120f461b259050070880090030709040041c0c42201e25038000e5008503082012004071074420440101110052480c0d0744040d96142042504280c2c1550b95480c01c851640551060880440030b0b030f6644840c48aa00c4005441d40348000403083c03180c0c0c0940c00b0000661944002d0701ca6090b040e14195032154000e141c040003915804d280c1c1540000103c074085010701e03244c0c1c503848680d15200e40b8a0001e901c0e0340465012035100307000c05032442840d00000d10108030704215410440d8254070488001780076005401c4121a1203412400b040d544800040104400303600504510403400402c403001ca00300105881e0220f00d6a800da40a00e100200002e070600200801110055400120410342101e0600d0018040cbc0004d0281c4441c851a00c6400300c00c5040010940d00700445c003500034a4024103200800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 822713120 1250 822711870 822711881
    0xa090506120303010e1b13170a1a0f06120c0402090f09090a0201110c03062a040b030a051b0306190b1b060106110d03020d0f09081b030a050409 63
    0x940c00040c410314207018100204003c600903c00c80300c1d181400c3c281104c8990081284c1c1d101040c4044080c0b02000341442021403910494090804402102e0100c00e003090501000744000b50014601d103440d80100c0004501036403040fa503640060030941d5900302040380089001c86509850341c0728001c8240e481c1025401041000e40060004001d11031050010b01044000c4900b10f0f156040324859a0844d604030014138405203080c4050007a41122502007aa1420010f120781c00348401c45000d950400c141c0c034950040c501c46080043d030b450b900e60800b046180c0c415284c0c91501d500d010700180d0b404151040c030304103400001400317600c0c60300e94008014103d0b0300c034501d50b509a600e00a0005948480350010b1081c1000455031012409150320501d09082c0c05920207030074041c0c036020030aa50342c070104a00049807120300b401a262107000c000c501c002e00d440c0101003050341c41e001c50501400030010280540d1070805e0080342c00403440040442c0c9900840240c00c02040060005200009894025 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 822714370 1250 822713120 822713131
    0xf0305100203251715150906070b0c03100f05060702240301330e01181e08010f1413050120040f060206070c120309020301060e10140a0905 61
    0x109074081200c4003c01400300740100d401c00c0404c1100d45054420031402c2c101d44c2e4091000f410b14030750380e990746010508000c0c001000c2d446c541000201c07039141e50380d01801da035031083c0c0000c00d01e201c0345080c5041c4202ca0317009071000d40700103941140010b01c0e01c10f40b80c1700400343c8102500540c00c00006a007402901e4403585001180c40c1f2055060703410320180e8601850003040c0840c0b80362001d81071042c0010b0b200651f000c01e00d180b0010705040c00a09230b00b00c5c070004003500c0b007841d01060b920075256104495420320380000741c403001e80602415000c10b035014282c040d00c24560080182109070101401150340200070b2119020141c1b0000341c80b01400c8407036194085c02400085011079200059641600f5a030b64445481100030a090107403551201008019140600040c191800c050f8009040300e840e0550003400e52006806006270350b4480d410808416038068028814103884212484001c50112448100311806100010302100c03500c0d440b8400d420050902e410312410b014425001c0c0000404 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 822715620 1250 822714370 822714391
    0xf0501080c1c0c0e060c15040218040317010e0906161719050105010c051207210c030206060d0317091f02070b010506030c0306011110060303020f070f0305100203 71
    0x71aa142d01d0b46030141898020068000450106140d006050500000340032401001c0a00103011014400904c018410b0342c807181c0807001da0340724400142042031100008120740c0d90242480205074100e1200980c5050f9a61030f042a603889130705130201d0000488a0342da0b541c0c0004041001205900d0390310380d5040c1d04d0300d0200055449141601c00780002600c800d01e83d00e0504507a02a070041c1032207034a015107024a86004442003940320595640ba411000c051182000281c01003040102042180c0120407803504900c2c1c000b00c610060001d1684403c1500540a0480010014a4558079101c011075040d143d292005040d2408503040d8900200380c0b030601d1044040c40b001780c10b6080d81481202d42e1214001d80e6440302c52402d09100101039104034014002070040c04017601010054a40c404000e20301042035074040304400e490028184400400709103844400700a1542c04540c900309030121904490f078144c0d4a12403000e0314145484050102c3d00203030b00342c00c0e00139030a40040da00310f41e2100c0c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 822716870 1250 822715620 822715627
    0x1804120e0a150c020f03030403020303041e1a0901020f28080408010216030921020f0f040203090a0606050a06050f13150309122f120c010e160f0501080c 67
    0x30030090b4800c90055031107002c90040042d050441c6000c10325081000000d802560030300b880c40d40403944d40c0c0660302a190361640030056010920080004060003891000104000729054404e0342e549540036081c064014010070090180100d000200f200b41c49841042c06092001c1c02c2c4c3e6403806e02d0107110720455455404000002e581002400503064040083d8419580e500341c42c500580726400c1a400f11480b4070000c290002da00540810200505030181c41e040d0041003a900001c0c024800d0052150b406480401800303000503001a807659210701c0b40c3e504102c155261410065101103130300c50388000480c2000803c40b01d02c00c0078082d001d400003035030446803600e403140d09603444520494583c000282d9249642c1007031011034064074080820300d00700b4000d48454011502d180d0401004041c10180b218000000281010400e440074081800c09098840c0c42140125010307158030b4100c440a40304120510000070651600c5400310341c560810311144924010054415203401003203004034170703000d2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 822718120 1250 822716870 822716879
    0x5190b06091f090f08030403020f01050d060902031602030405131812020115270b2413150c021c050a050c130915050a02271804120e0a 59
    0x20071100e290003600026071400006080b006100d03903800d80c000d904810740b4100c100000c28000c822107090726015204e403180360321004c0041e80c05208a000d25001c051400900288204841c0d01550148200c8824403042c81c840b440204d0fa240030394000c942d444005a075010403201100c0d8851186081810001390060300540c481300144509200d42101507516003601e4144000b0444200c0b015005c81031403492035180c20201c4818400a185030350150780d603104440a800d6031075010300d8a00c1c03109804288403115407141000070700c0c3c1250000700701802411a0119108901e685840003005480e0b803140c4045405070200200302400121681103504079208c840c01042c02802101e000c6805100100802d0f490101800700c8401d00c0078649109a1070052590001350881c0f40c44507461820b101d010403603454090240000744698100346110021210400e070200c2c80003001041c180e00129184005a60041201c05106204036401000c02079418108420765005640ca614200c202605c2e951045440c4e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 822719370 1250 822718120 822718129
    0x604090b04090f08030402091003080d150b071a0c030618041112010905060f09030a121104030b010608010b19230d0608070f0312081810090b0a05190b0609 68
    0x100c043c19905084004100025802c1484d101900450390a5040d10030310314540340c161303441c0100c000c41c14945849000049401e0560f851440207020032211032a0740d001c1034944802401c90100c3c0b410035016102c000100901501e40c1500c1c8519005040b0310400781c2e031101d040e006080001c1c0300310b903900c1c0c820303488840586620046000071050f08000043e0795215090aa150210040c0958081000350b01001b4180b800803003a2400800c40e820030000b2302d000a03401c4c10250038040c001d070010b11000318000040c014600640da040751010380340c07141c640c4d880c0c01c0c1d000100d1082d4949040c07448081540da02c0104c1c4070785095042c0d0724840120b240d07101402400c03d440e0f54000710007207002075201c0206002861081c405500140b044843c030060301e40c81d698509012419078100e0005009914000a089070051401c506002040c0016669048008040c00000700341d8a203050300c2c0c4194080020702c000580c1e11075280100c4400e0449600c480461b403203c406030007003200081e00200d040c4484609605d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 822720620 1250 822719370 822719393
    0x702010507050319030605030f060402010f120e0625140f09040b04090c080706110c0108130c1e081b040515040608030a0f0503010f1a040b0307110d05090604090b0409 73
    0x381c656000c200c942c0340408140c0340270f000c113860b00d040b50042003d010040c3e0700240c144003a4162800c00480c003c60362964540203008030041075050b07020707810400101c07140909454042c241840c0030001c4108194108a8120102ca52002c03803003442041010501d040240150101e80c40040001c00c85092800c04101900d0030300d5802c1318a141d00741014442c155040c040d00c8050401440c0c90491083da6001041e581c001124090f0f05025404020a80150f501040b80104542210f82e40c000c103a95000400e07a01000c101d420100c05001e01d101141000c4d0101d01003ea80e90042031000f004c07501c0900300001084050101144254031490050781030b10746000f03072070041c00054041c40e1507902d0702201400101240310700004005082005011240e01d100b20741d01aa0680081d003000c503070b400d000450b02c0d0312664000c000d40940110411414562019400c0c0c500c0d40b0007030903034014000351217055030b0501031011482e0f4402402c1c403042c072660b00d0603440342440a00c0100080b460700c013141c445541062 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 822721870 1250 822720620 822720667
    0x81f050a290f041107121103070507050315010803070605060307080a050a05010f06030803040609020319050c0a051020070b030403090f1e060302031e07020705090f090307020105070503 81
    0x100000a418807914150000302001d4005031400d00030018003482641c414490100c000307141100a520055810b40710340300c1a0300d140e001c007044a80d5400301d418519500d1349203100c0c90340309201e0100700c444a006440006412550004002d40c00c3c1266580d449020740700040446400d44581c443c0040c5042c801c01c01040fa0600400151001e0605400c0550a480d0724a5031491424203201e01000000c240d0022030364444e400c034100094411007480043c1c240340c07000d00c5001089600c45a46c0003444004191140018411070300c0e03007417250391181440030803580c1d031140402003142c450090390050030f080040c003031086200050718852030301c078400c10790a5002a68254009061900e047c00104120030100380613180c403803241e0703400d0010222081c901b00c1c0c0b54014001056004404030b4580f03500d40000b001d402400040020243c507060800035a070300c0c02031185500c2a040e810104444580350000e05010381c441101961822515800558659000740c104807001d20080012512044a0010056010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 822723120 1250 822721870 822721931
    0x1b05060a060e10030c060f090b0f0a0f41040b1e0c2d07080f010b0f0a060852020a02040506130203040b10081f050a 51
    0x69052003580307180002c0080400700c4003140d001d800d02c04114401c905508445407441d2006100740b08507401c031100703044c13a44010354095022840c0792101e40c1c00c8000d05010f00195441805419154408903001c038221051010042c8a8102051080d10f020b04090b540d12405400141d81d002c3c2e02d06805425403140d40043c448078004a002e2001880401d646008103011750013150400d07482c100440d4840c045000d81e003010446203000325200c0d940c040d244003103150750b50003a1060303103540302030313060311409011006115946000f9210040d490050002d084d05540030303110142980c10301744195005400500f0322164074030582082000030844100c00c0194040c0c0d4162301c0fa03001c00c00006032045200340f01c0c1d40e920182c00b501c1500b030011380c0001c00003465501190f0114036900c400002c10100761444a004401d51700010401003840324448115028020b03e8007140c000a44d907100040d01c0e070101000842d00c0b00c0440d50301d0b000400711b82c1c01103504000d4050b40041c03491020b2034898502070031040d045401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 822724370 1250 822723120 822723131
    0x5070212030c4602060c070602010f060305070b03090a02030a031d0904081207030b12010218151b07090614120304150c080706110310080703080a1b05060a 68
    0x500085010003100b5840c1c150305003440e2910383c0d0000c180c84805a80100080e1154010120a800718007220b4014005c690b651064003111030300c0300d10900550000d582800340540556040b8802c107412aa080800303080500c1c2080114615944040c00119042c8102018440541c1d800d0115a41c03091280d2034a100b0b50006041c2c01c1d4940e0b1540810b0f51044c00d42004100209241c1400c130303030414070074512501e4695500ca4041d4000d01400070442c1d000300c0c45d19003283d2a0319056004002004000111084055840003080140c0600c00d404940c1000f042c4041c046459461540ca2442a4103109484a007034560000c1d0044404550003040015441c10900c0003508107658a54040754003070002d9480c1c2801d108445003080e00c00c00c9031200700f001d84000c0505000482c400d8420040d8130510601c10300307800e03c154000c150001d855071105005190800580c45000160010840707601c100d1107420506d01240a4034900c411a4014194403110b000120014405000040c42001d045100040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 822725620 1250 822724370 822724387
    0x1b0f270e0607021c0c020907140c0304050108091209060a0509030a12110a0c1e081603150b0109060e0d0b0103050d030b0f0a05151308010603020906030a210507021203 73
    0x3614001499202c04c502c002922448080c0e4004c2d40c80d08003680503540d09100ba200c410b0100c0381e4050342d40407481e107000c000ca4140f9410901000602c02c660090380c0300e038941d0b200d440c56941c490708000c14000511104100e041c1203424110043c1c101c1e00e07038908141d07040000d000003003800c0c035010007000c49403041c441d016228081d4001840c0d040d640d046400a0500004d5035859120b04e00c500c1c041c1240c0b040d0035040240100c942c1c00d68030390180142e40161400442002000701841000c1e020032030340403507400c031b50044601c050321031107410304070595488028514001069600c815055900b036000340d8070f00403900210341c00000e036034000e40c42032004115500f680000101159030040540740310704480c50000c80304d0743e41d44914005940e01214240d001c030319803070301c240480d106035480c4030190081f450000035194810340c000c0e400c42c2d000f03650400d002d41da54402c041c2c403102070160081c103100c6d06980307204900b507010013800a81140c80c00c0c403d18040c0d030b54000036400030341102904407075800041e2445 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 822726870 1250 822725620 822725623
    0x110405041d06040201121112070809030a1e0c020402120f1018050901140414010c03020f07330617030f160f0b0c071b0f270e060702 58
    0x4031030014000740c5507105421544541e0700d6042c00340c0064108100010100712081055101d0366420400c04440e940e5000045082403459000312800b10100d110400080c41c100404400c540508045564298800740f8039005e200358076503d101d1110412100311404001030721248001c0c01021003902c10043d1074074000d074521409000050403592040d143c1d5a0421225894200101841010040104040e03450348005401828140221070303020f000d51050006103c1820084900004044024040c0c01031000f0181c0c140c1c800c258011590150402640000c075040b048941c4006251040c201105d00120036440c0044c042091080c3c4516982c0c03a0400040821840d000e04201e10308000d0342c1400c9595154003514041c2030740521a29a24107008400c00815508880c00c0961004040d0f150382460002e13030f45290440b0308101e8143d0580b80c84030b0070b1050701000020444200140300a0303190b0810b08106030b03400112106c03038416403004c108484818024014860301c03401c0140280410703d040c1e90000d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 822728120 1250 822726870 822726881
    0x909020d0e07140a0513150e0405120a08060d1704062a081b070e0106121505030606041d0615130c14030903090d080d14010518060105070611040504 65
    0x70305002070140c2c03c0102546134015200100d801c1190001915064090513801914281800c000d500c0110340c4c02052151241005900450084c004c0703900002d4100070040481c410075034141c0120b002d02c00012103d00d040005120054400d01100151100150a0b00c200f5042508050003280c0443d440c10b0f820b0380b451035140c400303032810700716041c0105442c1c50b001082d00c200c0c5060034a08061055020b80403004004a400408020203043e40d2503944140051502007004141c0c4190303810001c0342049a961000c500c3c080d10710060250400e0f1b16084c0422005020041d040d50401d03007000c100003128203090122a00c035444e2120480c0e4120900401c0200070311340842d0b401d051030b2a0034140c11155600468031440801812100d95603070701e035034404510307500a06608680c054200d4180d41c0410440700d015040c8900495414070981407100c407a1440140240550f5070040c050064481c080300e1003524064200c10181407452520a40341c8904041e5000710010f800d4882d0000743c2000b076828130340700b80c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 822729370 1250 822728120 822728129
    0xc0b10140405010b0f0721200c01080c09032d070807150c1e0303060305010e0d020a020d0201090e1608070f172e03050d032a0909020d0e07 61
    0x10481e56041c6134140304180502d07400108005808290002003000b0140840844200c402c83e6003950088030000500710b401a0f9880401c92501800399a94811b0004611040620585172000e0540d00e14204c410a6000205220b03850301c89e2440c40c4003140d2400ba151401c603010310600c9900148010142850192a50303c84003180d030002a04214039401454442c507904000c0c82d001c8000304242c1000040700c0c00702e40d080b030090034110a855040540540c080b0040700d1103100240700c551703110302c10582c440304140e0001c800b580010704800014a004645102040e10506040f100584c07203d94a45014900320380048000c030400f00880d007844c1d0018000365000c2d13494035007000340d0310660000400c000d0707062080a0318240c10002140c50700200c000c044900080c6500819141e0103040b0580c51201e0051005694502501340d0340130350103100e40500c07501c041322a000009440031a17406000148007a100d03e00400c4126100840e8005860004060300500c9103004510b0040e21000c2c03d01b0042240e20 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 822730620 1250 822729370 822729379
    0xe0601110607120204030c18060602031e0c030c2a030105041a0403020106080609030d14010308032716030201021c020d0e0d02060d060e0109140402060a0c0b1014 71
    0xa400c5000800501140d002040307241100811108803c903001a001e00c1d00010070a0180410103d1004615061240c00c1402e001d41030103903564414080e41c903807140031040c10101c0710070300540070170140740f0004000c3d249001c1c04072450a5000d0503020300700248041c02421002450044216000b140c081500100904038020000790400355102d80302c00c691241e800764940b400c44001400d06000303500240080260b1400d40c5c502d490100d003100d4a0346d00891418007400e1800b007402045400b00ca214505a0b42e001d65450311b10713119003a000301d41401d00f80c61906000040c80301c4c460081c4003441b142948200302c0c408200054218800a800d04a43c00c044a1f05034620000f2076980c60380c00100c503c60002242041054080d400b00031079402d500c0d184c1c029403c68800a56130b040400c15501840c02c40781000089042d603603d500c0c51303a043d140a2905200804140c1d8086805403900d40700600081c1590b051800071043c140c1d891240034101125085840d034081c050030000740581030040480c4010031503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 822731870 1250 822730620 822730637
    0x20909031303110102010219020303011d010f050105070807051020120412110f03031023060a031d0c04060b0f0d05070e090f0907170c010f18030b010e0601 68
    0xc0303981d4181c080a01c4041c05076030402c503011401d64002c1d41252480850100101c52068403a6006580c0e0390003031081c20100041c2d001102c880119010b0002d058070071a0f02e00024a40c581001168182c0000e0300554014004002d600300060003005201c5008a401e00d011490541020000040350545580103081400070400b644100381000e03401c80d0300c682d000041521100c281101103c29090b601050070440c400c2c944c4d4251160b000001461250325070340780268000743c5a41002110402110104410580018056030a45823040240900109034540099030405410010030403060496000c201904592500075540c1401d0141c031010b01090f124a510708000580301941030b04c11008078042c019682c0010030003a0b8840c500d40032060b50010400441410319401400c03840c0301c20b031603902091055110009945944040081d401d12030600a8a4498442c0740151000c186a210000802070030008840c403002032401e07054051800f900c603006040d81014181c0f0520040900b0f12410b0091a1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 822733120 1250 822731870 822731887
    0x809270a2d110405030d0804150c0203040603091a0115090f0f0302150c0f03030a0513020607112809272405011202011b030f0c020a0510080402090903 66
    0x4241d10510a005000006004180d1081007601e501690f00815854001c184050340380c6644030340c203103000d54003644c0c2c07111800100402e101c0440307a200c4403000150f04244010800b10f8041d50141c500d05d806510284a140708112040400c55000d82001e04c013071803820140441d2940c07007007410703018019500400b80903030b0402032035148281c09480000d10404035440254030106641064900048100048528244811441c0303900c1c0c0d00100d0303072540310b18a1300d40010031400c07034001c0c801d840e41d8001d415180361892070348410780c03003004070f03102684c01c4026108169180561349030340040c40501c0305070620f00c0604014410040d540081d55000016030f81008000702c2007011810032860a60105540007094110001044484003600d410301c1d60500d44000050800007070544075100341e100740e07a090030541c0c2c0d9050a400d440d4165030090f0003d2002c00d000000c1d140140d0000320307981c0c002008440707443d81d501c000502072a03000460400042d140c00600c41181409000180c0002c810009141003440d013 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 822734370 1250 822733120 822733181
    0x91407020304210c030b04021f08040206070203010e07030b010f06020304050303161713090e191202150a0608190b0609040303090803090c1017040809270a 68
    0x1036008441c2030070b202c0d503d04020400e1000d1040c1c402948500021038559032410480261031048500ba030048010054000d00202c00005c1c0d011982415200c00201e070322250240001c81c0c01080c001c0340c15640c5e40c0b005080342002000200021403140004801560500784c4a01d0083c1050b400300307007503610a0000b032042d6540802511407541c0110398110400c9c0140c242650300b130351400d4150b01b1414000542c0c100307820f1003415141c1945c0d10008188525044415132550340c0c558100e14207009007207107807000f00091208050021180062040f03840086100341c001130b07060b400740d600103840c40d1f40780c0c0c08000001c81401010810241040c404020403000e84441030721005c01010240f10300e80c0c08000038109406903021a07580e54111140f551a480d01d0005113645241c844c0090b1f21440e0203541c1c4042143c803684110041c64440461005070342c40d9603607125030039007048100b10350041020844840c0e501e500491081c80c5a140301041c41301c2d042c0524044100c0c1c84101070800480100d802d1003880c0f409 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 822735620 1250 822734370 822734377
    0x201060506121005120f120405010e04050a0f0c0e120607020a08450603091203040f0b0720070e07051812011d210a12150914070203 58
    0x1040c49030703007150350701c443c20a0b405540740d8100c203a1043c900c00211130f80050006d41c054000c280c0004070745146405407641c0909000320300c102800203804a088010500b040d4000c0c030b0304006088004100d9001c0c2e854035005844001c9480c0e00055002034030040240392041d0b4031190840c0c02d4000d0800c80c20b25181c001c1d2500f641603c05440d80c140054807e8048803000414090f2002403004800d8030200380d4034a208125141c0c0c3d002c0d801400e00c5128003101c0c64200100d0b0700a0348001c00500c0305c48903070400810182c10060043e1004052500c0c0c0c00701080f43c44524604c42c40040d614170400c400c08044488941300795060f2081c05900440080c02190400c00c84103421515038101151908200b90040b5054011440f103d40c2000800c01842c8452005402100f150001000c09038940403800c0340103030f9200405400f41c9080c02c02c0d440c01803551030001c402000786200d0b0b1320b040e5421724000280002074820700250411140200d4008000d55040b40c420140180c5081000c0185410301d000c00070b54900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 822736870 1250 822735620 822735637
    0xc060507051b0108180a02090403030504150e0c0f030111030c030403140702010e040911030d0f0207140d081b0f0d030e0a030f050f04031a0a240918050a11100201060506 74
    0x3e00c038140ca040c0c2203500700301a0081b55070007801101c50f45440d1800a01074241680c0c1140c1e450074414018001e101107016540c11450541300034940849103108000140400b1010b03160595608e512480c0d030130740301700c0003580320750b2100d60f0040d682d0800b0301c1e000308040c4003801e1022140000313100384c50040c1e1b4486030040344d034882114040746c5408a428038501c020441d2400c6036041c803554440040081d00910240040045902602c0302e00e551005088001030408245c55070040301298072038005003014010380180707154210320928002c3d41c01805442c003804004030f0384003940300d6154110807030382c580207a440280e0080c1c05003070007008941c0c015000120441980060081c007181401180d0040700c01da80c0203540150514107081040c6a074103005d0f0b0002d8070a000300c0d5040030f56a2460084030503c0320110900151925a400d01c3c00c9030000082a880045295400e103c8810130702080c010405000781c1742c050384215001d0350241302040345100c0010074040079641070001c100a42d995440c1694904d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 822738120 1250 822736870 822736891
    0x3110906060a05070f080909040c0801060b040b12070e12061f0e0f07121a0901060f051b030f030c0307030f0b1806030705120d03050109140a090f0c060507051b0108 72
    0x12170251400201b1030041e02c04154001180a0030001400080a01340c821101400001c00c80300e0b8640c199414248514000c0d18203291742003000500e016040e054041d48084549003055a02c420b1800292850324045044c4c05c05c0d51069062007180d10100ca00b040341d018100e034061300c1a40c0b518050080d1001c00404400d803101000000603a1603015002e0442c0e00782c058081004602010035800341c043c0f04401c0300c0c038000c4641800200705c03140201c16004207061580c45035410004000c0b40b60003840d8443c0c0300898103020510102241e0320380c0002840c02842054851516854441b00c010110744501c0b03103400c4c006081118416264980d0442d1409000454921748030781e64a90b404a40703420f400e94465601b09107500c800c03000c1d0b10b201042c00d5414003055902880140d80e124191015619408104502e5408003004a80c0341241a803152540500c100c05012154000c0c0d200e2001041071540080003141000900d1801c000c024480003017900201404905444896030000701004002025960803 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 822739370 1250 822738120 822738143
    0xa113a02010501140d021813060b0402090102070e09070b07210e2202040b0406020c10030501150c02300d0503010806010b0903100207210206091c09050a03110906060a0507 75
    0x547d00c031203062032103007081000f0008160404100702c10701c1c00080c02007503440c1403500000030803a15180c001c952103803005900030800e135400c0401d142d450078005000005184a102e0001501028500150030002d00850211000d0692202005090f08402c201c11040014100003008240e840460354a540c1114010114280b1340074a4604000e00c520f4001c00f1004e8004580041d42550014902d1080d1400755001c441207816071006405983c1d00b8000d491000d032240c80c02c0307001c007849058002e03140b0340010240110740e40300c0e9030810001003008848104c0e4001014200c018000100320f1400340c035041c1e00c3c040c0d03d15032422a8554407820180100c00c10f1243c00100035520340c3d03042141c11800185e0407803c5541e038540e850210745402055103101c42c0246030041480215002190389445540100d028090701c0418088540c03840d07072804404001e126212a0105150700c1d409106005103118004c040340b800a200200649400c0090050784118001c00c420b01d0250343c45001e89441c00d070701c0141c9102 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 822740620 1250 822739370 822739373
    0x70801140a061103161214120403081b1602150c190206040f230f1e030316050a050f060105010c06090809100512010e0105060a113a02010501140d 64
    0x40d071142c1c0c0c5017680e5519400e5149410f0188180e079610b030f0a0400d4035810790500500d10079400754055041c00300c0c49045008002000b0038000d0031a80d03849440084038251040d4104080d0040c0c0c4c000030f00602d18030322190a00d0045042159401082c01c04101d00c240c02e10310068500c581d02c40c2600016513141d04200c1d03c101c11034540d102610060070780c640b99640700300c1d1034a1415010001550704400c45200d000d00b5081142005941244402005441f80d02e41840d507440c0c3e40f50780c60b1031000b056018807080110340d1044081c205064006031055016001c130305900c1c240645050301d0030860f0395194201e10010061681c205c03000c1c040c510b0b401140414060064180051a070048080d244d4100c6040100e828130b0561181c01000c1c03100c10101c5d0115141d803941c042c9542c3d184240241034000340c0403c14040101c2c003511282d20300200107411216011290800402c09200301400190250300a20503c91a113161340c01d40e00401c200740c03008206a40c501410085a004066070f501e002e07191084c841030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 822741870 1250 822740620 822740623
    0x12020307030501020316030605150f0304020a090c09180b01020c13060b1207020d08062d0d0b0f0f0609070c05010e1c0306060314180a0b0906070801140a0611 69
    0x3801140c02030700854483ca0001e40c124071071014600e1700c070002444d124003c21a454400011f2402960f00c11625003850034000401d8031581c00075000340e0707015401e16000242c3c212540525601d00700160b4070051020f103404a0300226503e040080491181462829000c1c2d903400206c042c0801001c50301c0e501091603660661000340300346c3d0055a20060009100c0d440742904040b02d0340507000e03a50841c2d601c003461030411505010f050f02d0859208030ba40042d1910449500301d80700c10105448900c041803003203030000502c01c2c91100d80440e540d0020004010845907250712080e4001300d01203600d6001d251a4000a1441c00014140c4040c050550322130800c0c483e0940c4031084040401040b10610741001440741c50114002000000007403c10030041100c1d8441d014542c0f524003038400180044c0ca406450540410a80e0007990203841106009170104502c100158090010000502024184000c0042919505030003600c400c450901c8010320584a0443d501c01716009441c0242c0d0103140343c40190b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 822743120 1250 822741870 822741883
    0xe0708040314040303020d140c100b01020c0a0e0411030601030506040813052116140f15130f140303071506080706020715090302011d0612010306050708010b0c0304120203 75
    0x54650441c0403070f01008040e00000c0000b00800203456605034510301e4602920b9520850000a0b629008891160740c4200c0c1070f0020600460140107072a40c02994030007045461b002540001c4000c07114205000600010a05603492005d0a5003c0d01c500d60542d2a00e0759180b8014000070071105000441d0541481e20710099409020028800750910000150040c0e18501070324945185005408618890301041a25070080340c0c1c030603d8400d80d0503100703000c112201c2c1a01c0202600140c2d03000864003e41409401042c0388048040804221418110f0b503c440503a250444510082120307004d01041d94000300b5100003c1e0f00140d80c041c0e07e80c0c2d040f580c0b400b801a583c04150144905500828110b401182200c251141c1800110603140550021101040305110181c040741142d4042900b841014510000e03400700070f00f105160044014003581100026132060700d44030723611000c1c0020300b40d21900507401000c0101c111828540c01042d03041d26031248c1e00c5107115a400700801c0c40115102031020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 822744370 1250 822743120 822743147
    0x213030308071418030111041208090a170706021212010905061807030e0c090601050301150306051306061d1c02030114040804050109082b02210a030b0a0e07080403 72
    0xc03070329208400d00c58181300c40c0d4000c255100c1d500300219102c50240c90b0040d02d08842800e84038151404558903070781c2682e4401d05543c1c0c1c100c20505008980081c401200e4140241150000d140c5c0500d070003002400c0c1459205000030f5904100001909a962085000d054541c168000609070702d41c900000d00d400070700c450f2035201500d00c108100404c0d40692040000300ba2080913030f208103c8800801c840001c1c00c450050114205200600490341d104101c03003a0800c040c2800502d06d600d0703000050501240d1000e00107020345030035003404469801491003256041a03400c001c0c001d10048002821150400715540d00011070185540555409411001480521418000e41800c040c20401c15540c032500416020a050010000e29400001000e18a4604d6942c4684110114801440d41c01c140d4121950031882405070750381402d0b82c80c01040312000002d0700c0080c3e4804450b24058103070350100c19071520643c04c48108000d00002001d020780c0c030061610f0a280940d44518050ba81c00048044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 822745620 1250 822744370 822744407
    0x81e130530070c12052e0e0f0628020d05090d1e0c030e06120f0606041820040f0f05040e030a14091203041503021303030807 55
    0x15044078050001c403003180d41481000c0400410000180503105110b0400c0007840c10009203810000041c0c0d8800e03030711600b40300d01e003615602131301c0c0e504040312400032408040e50b0070490610180c40003c1842240070006100d0081c05907140c8000e1200d4903010f0080450003007000302468107440e10003014a094511001407000c43d217420801e00b00300000c05013207407601d0562048001d2040e01074051110140b8414102d5885403a80e200f00d03c0c21103804141000440038408412442d85103940d4203409031100b400180004001c910b4889141221401c0140c42c0d0781c068070003048280045d1107003100009511481031008540380c1403070b001c4543c007107203940090601160003150201d00183c00380900c000b2105c4006a0403a2a80c8480800049071030701450140e1a82c010005c02c020240500d2007480081d444a69290808040d1030108404a04800d140217558100240c02e0045009591401041d0810b919045003070004c04888208035071039500004e4180030403403001070a031510a81415114171a25007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 822746870 1250 822745620 822745633
    0xf051e0a153f110a021e150a091b0611010c09120b1008060106051810051213120c050609070f0614160c0e13080d0e0309090421081e1305 60
    0x4000e40b910511048100c5640742d028400c007503520b000410131808401d416a5447c55102d1540e810003e100360b0f40304645003c0d0790300f50242c4014180788a44c000742216141c1200f000000c080382070840d14400440001d200040c14140030300620101010300e186d07400b501507011030319044031a816000d1942c0c0710070b901e48251800440d45903480805007003401030401202c00d90300d02000420a8a40750304c01d4900014800707000346040404c080c00fa440d0010b000031200303044104240c4810659511001806010603040b000041c10883c040040640c0404440d014200d09c030f040502c050b0907955030744601400c0000711040724155180450407594030241c100311001e003449480c03510507081101486001c8000da60200010401842115452aa0382d4010141032810711181c2184005000101f80f4582c60700c4103000c2c040040e1a040003040c00b0f140101201c00505000e04401021201d240300d04a00308407015082c48109003041041d0326000b280454503461581d0743c8078100001031802c1c180034206201c1c84 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 822748120 1250 822746870 822746887
    0xa0b1b0915071527030c150218010302030c0a2a0f030f030c17100b0309011d030c0307020f0d02091509060a0f051e0a153f11 55
    0x1c0070100e106180080c9080c80f03101e10340040354181c500c00d00b040a500081c0e00107101d19a104110964424240084500c0c016124510b0b94840300c00c034105450703800544168160054070f03040d11220401d1030b00354a07525140c4080c0001c0e029403400401404070f0100410209456004075110305003113051503014201523400c0c00333440c29400c840c0540110340718804280045100c2e0003000319540007525501c0022000e054013406102004200c40c40e445070f81d400124449954200960082411000100300010300c0c514020303403044000c03d2010560b104011004660401000340d99030903404590b50800b58655401003540c01c010000300960040d1100104510030041d00c904001e00c1006840c25003140c0e40b40c0051142c0d05d01540124003045002400400a42c80c220001070f0407103003154a0040c5c40320a650104443d000b072900f107008041200f07221003441e2603020084e080d482d5085600b40c05c025590f290f80200012909080701e11140700202c0240300500182c00440c41451581415903462082 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 822749370 1250 822748120 822748159
    0x280b0f042702030f030f0702180705030f0907050a090f060b0304020109030f051002070303050a060e0106050f030c07020a060206090c18160e060a09030b090312070c150f0504140a0b1b09 81
    0x4413400c0340b003106010345c4940c0343c4891002d038900c0352b1065101d81d0321315242e200c01040c100b400208020040d08c82c5090200d83c0362184218080200381e5000003280b0714981d402d0706804e0307403020b03003003029540303030910400c80907130b9220240c141103a0700507140741000c1842c0c0c01c00380c0c02c080c0300c506410107503400003480c0020154103a1106120300c680e5002000303020b0709d840007c50042000e21465001403000d0140319001419480215004910904114540012607001c140c1c0854642c0c03000740941c008100b000074a00c01444201b010400440d03011040e00c4891004084e1840c014202e0b100c03065501844041d640d00441c48402e2620005200136110307206c9910080100301c280c00200e5043c072404000c107140b400008107403a544d08006054501d266a004c078111418482c040080d0341e81d040e41c05030b21000c010340340b00d2000021450800400c052500341041c40240c0032090300c041080e80004101c4c0081015032891a80205c8540c401030502c050409524030715005202082d84c1c0401e155042c004610b49 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 822750620 1250 822749370 822749377
    0x2280e091c02070b0f04080607021516180603090b1b0a030e010f09150e0a0c12020d0b0a0c0809031e13030b0f3c280b0f042702030f030f 60
    0x84205c80041c0da41900482c0ca43c440700fa4800850240c00020ce0351450031414205415200c41c58a00340c0c0071080510b0391181400d541c40240400c0e514010300c400e00a440c0c000a61140f50031480c481c400c0d060b9030801500e841422584400c01d5034907510034580f00000c0d000107841c1c0341c8007141800380d2002d50a010344000c4002d5441400b1514141900360307220744c0868107818458204050000692410151401803100d90000f203a110001c1c5184500141d10a585103005038400400000d00900c400c801034400c0310013400d8440c15510500030041403240c5000040c50000003170940907214410b1030710a040b01c0c80b4540005045100d11410005420076001d90140b08004c03030012800750900915141e804401104041c01c800740c0c07181b20b000290401e00500c150040c0307100c1704542d202101588400d6200c92079466030904517440303244c420018a8481c5c040d0031006402c9034100700d40d00c0b41d412002034504482e4400d4420301500c90301c04013590390078041c00c0394100c602d8003a6a552084891101710703a52 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 822751870 1250 822750620 822750629
    0x2a030f15060d02010909020c01091a010e01050a0305030a0e030708030706141510210e011d060907260a0f0b090109021005031302280e091c02070b0f04 66
    0x202840c000805030b01d4864499a25941c06845a402c0b0a00707000001d0007a43c8401d0808440c0d6480d0a4110005000c2000e40a004024610f02104c103505127218000c00400680c07200344541b004800610101e100031003242e8051103242000550440305002007800d16540340d01c1103c0d076001c00703d540d01c00c0c000580c10203e42e140403401000015034501144800c942000702c035980e000500c1403002a0f8580c012940c0501008008032001c40110a034101001a9105c0508400150751100e000003103080c05480e258180701e000001400745860002d80582d501d410030b10820b050f106140a11010341c02c4800c2e1190386202c083c406443d070f10251802d01c100d00082d0340f181280c1c030800100014034412418440d401c149a4018100780d001d16403000104c0d0380303800150000f40c03071131607a60180c4016a07420200d06200c0c00c10b0b070020f000103003c000102040c1d007402d601c1600d42101c0081004082c01d00858005280700c420b0b405603000d07020010003245444280e800c00b00c0c040c2e0002900c003c2c42c0302404003800896 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 822753120 1250 822751870 822751903
    0x315060e01080607020706080a02070803150301050a09120f09050a030305030702100902010804020d030e041a0102011a0d230d0302030103061b08012304110c011d2a030f 74
    0x41c0d030303207144859848004450803001170f0486907082c05030500c1892030a41003030014501505141950700d6516007a8010b903100510501c1c44100e5003100d007003c1c0140ea034071210038507040000400c603407207080a081514030550200082d448688010303030700411560015040c081c04511009490340780203001a40b0580b1041c000d4422101f220020104600032042c505a041c0d640511649640d428450101c02941c003c40074442420b09044030303500d0701c2c800c00e000603074540c142c1d00300e0081040029003100d14107120106118200c0c0340b40d0311039890f4903c4c40021140d02c00401c011002d480c2a00d2404245103000c601000e001340040410780940c5038001c1c6040c2c1c2c1c000c078001c110b200350302c00001103520461070762140880c03510300041003010340c010005150300780c40400d8144036090b031000040031501420007442440b40c000c201201081d20074415401c681d011000014400d905181d020f42e942d181c04c0400b07100c50001c90076800f81c40b41c25400c244240001c064103d40d114412602650740ba40c0c404506c40380b00e03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 822754370 1250 822753120 822753149
    0xc0a1223011a0a1409120a172a0c0904060c02060c190c020a051009030c05090c22090903020a02040c050405061c022a0d03091505090106031506 63
    0x90840040d000080d140b8640920b001811007040c1c0c0c0703542907481c2c42c03c1c070500140089207045e140c1e80d2841e200c3c0d00d400c10141c2074010b801e00c6c00245188845c0a0700380c02500038402e110340c0710441c08000180401401210a00105440c490740c0b43c04810034407039402980707040600003006540d420454a00712650280c50059940a20390141801000e00e590142c1820314800c81a07507020b0410240014000303082120000d4507000801c076000041419540040d1040400b0400e10405c004104050a42143e5440e0a418045940189800750824000300f0441800700e00c0d00d04900900400000d14000078240030920150401135100d0282c502c05074013603800c00001d043c0c07552160381102d050b20b40041142d403c002004000c0a091011810502d0300268200f01e0780e0b80310481c030054950344406442444c120055084c00460801503020303079510070301d81400407502c0000c0c4c0c655112894042c2100c80000e00c0e40e82c0703040c06030150140341d001034048010040c02116020407600024142c5130020004148d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 822755620 1250 822754370 822754379
    0x30d02040815070c0b1f08030c030901031d0d0f0e1f03152607211208010810110702150a091409070302071b06020a021005120c0a122301 60
    0x1084a04c00400800311482c4500042051603807803050110b418032449100090354407212202d103954840081080258400b094549456906004643c01c85d14030300c001e10703114010300942c5551400032484640c1070101c0303110703001c1c545031143c07c01d02e1002c40010400b038118540102074555603245200c034100040c1c140442c000c60701c40041d81041c21070b004020054100500c8101e440c55101e1205100c03010f5015840303001a007656449045001050407021800c0c910301103241410300c0760040e0303492009100148004020440000c180b0145411190700f02144061040320a480144215140254807850041030840c0721403114000d024645500d8440c95091520b965003c0400c68074840c0f083d50001314800000c00b590303c6500944560303482070042400f05480907909071040e040a801460050f0b100824200c1945001981301e1003045807810040d103003140303804020350000780007410b0140b41c080018200d0b80d454480c030b036106408510904104034480c8140c03208038401040c0c0e088074100400f180d00104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 822756870 1250 822755620 822755627
    0x80f131217030c220815010305060a0b041107032a0b04060f091a06010207090203060f0f01111902030c220507030b12010c1e090e09030d0204081507 65
    0x904076007021021480d111104102107040d030000b0444140c0c01d2083c03107414508016010307204c0b00040c42e86216001c8500b48031417140780240300f0b8449020020741a00401c0032a50100303001e03400000030b60012480045507000304010f80402d401070f861500000400d0810b150b8000854200d000c0801c005907002c400303450b02140c4000c100074001e0185805900410300107107850780107203a54981400c01180d45852900c9901404201d01000010714002104004c02903905000d5827001d0400c0358411030441c01d02740081038024003409103081c02804002c00815a5a0040010203050410402143c0d8044c08404082e40d00440e911001c234028812605004010303c0e09613840118604c11980050700c000500390f143c006800050504028159901040b50351500d409080000034400d000000c103a19040081c020188088403034111304c104100300d8106030141e0300c292640202c41240360f040c03486885101c50a070651103161065420315100142c0050480c602054907800b4000c4508074150f9a0b4549030300350f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 822758120 1250 822756870 822756899
    0x90316230c0a0909020a0308070b180a030c0308071710060e09010e040308040609061a0f091603110c0d09030b07051c09110d031e0e0907110307080f13 66
    0x2140e00c05890b1809100c201c829501a0201600080c43c0c3c0100a540751180307040c44c0d0100c5415110042c0b07090070807082c01013500c01072a08041e850002c10a50308103440041c1400200d107001020440fa80300403d00261041e0000d59401d46d10460720941030411240122080c0c00380c1c4a40c03000704000d002d649135240740c00e140c1d60741250103040c0300d03180395038a03954204c4080800508c2191820b03558401000465550f11030305014840040544c050760f01c0900400051100c582c10140c80750350300700c0c10801207004d10408498a10510304011801043c2d6103142c1406000e0400c2c40b0655116034803005003541ea00c10020b10840f030107a1400b0201d600d40c02c80444040c0309d500b440014101c0c4441d400030b1080c00d103074060361819024903000e000840c00400003c3d06524400000c0e00013a442141d83c07415040c0e01c80000e1019101401c01c941d00010f0400031820030100148100248081d800c4001d48009003882190340c1554030140142d81c0d005400e10907409508034401d2840000c003c1000400c0d028114001c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 822759370 1250 822758120 822758143
    0x60f0f080309010c0f060e0309040f02180411070f0b1f0f060c0609020613030b09010b1f090b0d020307080c070503090f040f06080102070b09160303030509031623 71
    0x181d807810044500540d09018610f0040760440300e5030b0800b00208001d4440d0417001e00d020005140d44452003000c110580c1d0460b144104802c0c410040c600340d0b84000d907040301030700000340c40105400c0001c5401400d18083d000d00506072582d680104000c011300c0c41019403180041c8100c80580b02040c80c0aa41030000354004d84c0c5603140c0e4404140800d034041c094155505201e11004240384005078042a840e07000314440c401c019101d00c0c000e0080240244030a6806150302001f00030324001070001030b0750084040d80300342420400a190810452042d0161806441215016070f900e613203041004c0002e500c1140d602c0000b5403810b010419013440d8100326030720950880000c50403c0d00200411000c505180700340b65110765299480c44610f01036020752002000c12100050726400b4038201a41a51f8000f00740e001e103a000401040c10044603251003800747c03030b0107103000100c0e503459940440c40c611900d507a003c20f0010412110701000030040088490300711a0700b4100e04450584800f598404031000c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 822760620 1250 822759370 822759373
    0x809130501120807020a18050a0c050c0c060d11040e0f0112020604170f0f01021309060e010b0703020705090a0e1924060b0d0903080f040c0509130c09060f0f08 70
    0x9070340b000f2500c510040d000700c81c0024070721421195505444a03244c0b04094014103040d0311070040101d60701ea14816201c20300100e0504518000d0001d4540e600c801118445500c688000b00d40c0c043c3e000c5c4103078024201601007498080c0d88585a038000c0e420b10101f2a4130400d0606c4d004001308051551f0f600c80d14080b60b01415a40c1080c0c01c0807042510304842013420140d03403141d0804aa8017040410000c0c03d81ca182d90300050392544400301e548404686c41c1c00401c0c502d401c100042000e013100d10440b50440b0203807202151160b07081d26040f070030300d9115480300c0d03800442d44080c041030001950000013540d107100101c4908012081c403448040b4420003010300f400c1c1320b803100072199080700700001c041c40c4468500003c0b503e841d54414111604500302221005036140c0542d0200f43c5c010001d01d401c10806204c0009500e0103070394440e405040c50040c140038a03116004035000d1101c580d65582450343c8241c159038059160012103004100510488001c1040001c000507200640307580d4000765100c080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 822761870 1250 822760620 822760649
    0xf0b030703050a021303030f031d1009020a1d0f0a05070e01050a17130b060306090c04091514091c080112030e03070b0a0306050a18090305160809130501 67
    0xd009400802000382030381070580d0200300c51a00c5441d50072070080a1031080e190711010420390200182202ea0003031103011144c1da4002e2001403000001aa400202ca0500002c02c100d00241b002c102c00f03562940c0310800c0c884021003119a40b081e00303034034144142c1d8200000e151954036415150309540301501c6400120740401d403004240c0d44588010032035095642055000f01c070281020300c982c1041210041c0310b861a80c6c0c005000c1280c1790981c40c1c0c111004800134419070500702c0c03069403640112600707548201e40e554032503030030080410200c54068090080400400c85900c056807040c1908881c548001c6c007038102441e4808683d24481c100144050752020141c0e0709200c09005070301200c03034096007440022142801c4650302000010080c02d4240300317030342d12000c0c9003501405984ca40e8101c1840703035588400a00055414107000c0c501e110030954045480c51086c202600d0a202e224005600c0c00742c01008441401001e500404003044165480000c0e00300b0328030080110b40083c0a40001d040004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 822763120 1250 822761870 822761881
    0x1b030118050c13060e030d080906010605030928060c03050c090910091b110604080a0f110106170705060403021012180c0314060c0d1802190e010f0b03 66
    0x154001c5500c0414080c0d582d141940703a0303200d041c02c4085540080000b8440c2080e090150805100403500c203000d0b07003400d6002d810400d03005030300c940c8140500c0080150101c000f9241303410400941c010540d03003180108a00b404400b414002452581301074071014141350551044900c02e02c00c1500c038840f564842414414204104004990301030040111718040c0c201c00b0440894034403820841114510252100082c2c8602c0601900c1d44051068801c1c0c201c0030802c004122034004840a02c0503610b014444000810003d072102d001d4149210115072a084010548030740e200e0410241c05460030031500042e650703c0070032078640300c0c600009403c58200600030305003901039030b55450303902409040443c0b400300400c03421080040004080e0303400c2020b20820018405880c246044014580020b00024074100c1079082e100d1040b1015040925070310065800d2255041b030303442040740ea00800c8082c02103500ca000e8000726002c0d02806038800304150001907068164854a0112280a441c2c1d03400d56413403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 822764370 1250 822763120 822763169
    0x3010507140a0f120507170a110a12091506060e0307030c14220203070801080d172e0f050a0f090f090210020d0206090c0a181e02031b0301 61
    0x304020f92080c05013080e40058941c0b103e0040d40d11900c42170342c82c0420011800786505100102514904c13003141703403140303580a40c0030f038404441c00c494417030506850700007001500c0b500070904207501038104016044803081c00d9003103801003000c0304c540d40d6440c0480e500134800c068030b40d042480000d114651107201005005058100d6441d90320f070040180c01e44040388952181d1004104090381ca403580d0000802020342c0e0840401805800801c00030803111215101c00b50500b03090817039105030407107405d0006156400c10390800c00101e0104500c291712111000c0b41d0559204540201510007080035804141814a04c1082c02120741a07104840071a00d440c5118004017100b5a406082580390050000541c0b04c4200203540c00138264000c00b4041e1314204000d04000001c2e01503c2c07650001d04251034540e485e01d10702829a03200840900301009040451401081061752049200e000d01048610381c0c200c55000d07500c1410000a03100390701b0701d400d40c16800d502c070034010394281912910000e90001c86 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 822765620 1250 822764370 822764387
    0xb040501060506030a06080106060e061b011b1d010f0504030b09190b06031006050a03083709050303071703090f030313030306050301150302062d0903010507140a 71
    0x80000055039502e0b0700c042078695000f1203800d080caa45400c400c1003c110240314030802800d42c2e10745210040c010000260080c401c6c428481c040e00c2c4403504500e8045020741c420300e8a12600c20030301050000c0c00c2c1014200110f03150386034090800c00048008a5401228219030f81c9a090782e4161520b42075a9455032180006400c4a85a1183c1c044e40e504800401c0f440c544c440303020f0709100320240381050406184c5038449410368055400d000041120707031100c01035142900e03808481c0c1511a60b420351103001c041d4058000d0800b61040951080303d1006002080c8100c11641c0d41da03a07617894030b401c00c1c5592446070300720040035649101c00541040301036901840d0048a283c0030b541d0b000300c0c038000c6185190416901c0c000a801501c2c2c8400425800d407145c80c006101c20381c002e001d4aa803007422106100c10074840a40241000035090b201c4007001e42c0180a1903a050398500e4041801c09a00b04441d04003115240c040d6203080c0108105500400b81c680c40700c04003400052a086030060129501c0ba07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 822766870 1250 822765620 822765623
    0x31e050103051e160902071e081c090b040c030309150e0121060f14030a020303121906150e01020f071401121805010c0f080403030519020c0f070f0f030b04 68
    0x10031395800403941c080c1a06200034204001c0250b19041c0345c0c1882241c2c0600024224641c04d4101d138000002017000c010780740400d00d82040c0300703981c6104e00c0003140903003103011004100342c0010341040b0070030101a0091081e02e000b50750300f0158607150655204403a6004205c003000c140c10b2500904907610601d4070754000007181301501c038502200484030041e20501d070004c1035189840c100c2407081d20800a424042d80604070000c000090503500400d889100f5038200c1d1003a58240d90001c0c8665100c405402e20442850204101d00b659411880020001110005002410958110700fa943c800205102120203003005000d440345480b6090140054a0858034140072010181e200f00c0400f61190031b1540142101d48820482103140080c210781413508442c080c801c05003004244294409241d91703109030b0604000410303450311041405410410f0800c1c0407035900008013903981c0440801d80b0803040b142071044a00d2292500165404c0242500604041c514902020000320b0b00344090660041e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 822768120 1250 822766870 822766873
    0x190809040504030e04020c0c030609031215030f150f0a0203010e060108190c1d040608061906090c020a021816032a0801180203100b07060b030d031e050103051e 70
    0x1c1c4c1280c03000c2002da800c1100103400c240c00100a45486040c148040d0b80e01c01459005035103803449141915a40c00c0028207580c171300d55000c8252010300d8a00f040f10247c0c000c1000100c9070320b54503601036125066011101d564103440603c2c0402c1d03000d035842c001c0d241600d08040d480c1c20a640da1a0044a91610051038141440b4000c08a648100316500c65a004140942d0360300e40780d44880c0080c201152001c440c95030099103031030000c00040c0e6000c47c02c1508004078250030808813084595104c0a0300d52500144523951800c00101640c80d000100a202c01d4803d481c0070000035400c90340d1003c0254102d980d22401c4070f4442001c0ea54900c00d9202e10811074101541c12140400d016010814410b14a0110301140b07a0b20018042c200d110400540e408100c9a0154a1894402c80300d04100c4041c1c03080c00c030f800b500402c0c40c0d41000126008071006980c0074049402a01c021032000300541200905201240085800591900290701903181a130b900b150050509403009400007150328030000001ea42c1d0b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 822769370 1250 822768120 822768137
    0x7030b191116350a02011d061303021006060f02010c0e0907030c0504030507120b0a150b0f0d050a02030601090b03160e130f0c0318051f020f03090304060219080904050403 75
    0x140c0c60200c01490903003d41051592208219031002e07003110940340704007441c0340c0c15100801800708001040355101e03568100d464005001850f050b4079281c0800354003844c2d14100100814a141d0120a010302e04c0e0041d8000d00100710481c0381980c4005e044088a1f800070b00c6540040d08050007508280a003001c40c1c5020744c0b07010360301c6d240c1900300042d680042508022001c048000d21030401c0c1e00c60703000703001c1c41410403400d5888000c0010050442c4100e0780301c024041404d010244a030b40035100c010900141c240300b280303800c01e0014000c0d4030440b0b00700d0200e4100c81d00030810400342c009491240341c4030080003006180c00e01055071700d440b100b10056481101c2c080b6512060f511030040076020360300844049508010640cac040c06660107681190b0b0203c1c0644002c0011030000500c03c941c540030404244003038030300601c0e030300007030300c28040c0b0801850000420701c0f1540400000420403690241e00f030324240d140030041c041d105002d0101c0603001040500442445141c03540c889a00244a070510112 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 822770620 1250 822769370 822769433
    0x603151906030b0f01062a03211d010204180b041104030609020429010c14070e1b0a08150f1323161107030b191116 51
    0x181d480a40080307400660764028841c0d0280c1409035039001d4840d41c140300ca80c0440511015030902c80d400341d81c00e5080b14080403d41414012440118a200611480c0a0080f6603681d400003414440f10400001c0d40000c040303e5031f1401c10300c00e44043c0e0350141365100c400c9115854401c054414002026403047da0762000c03500f1010004000c0006520030000400c40d407950340100800c40b00c03a5016440410f600918030030036007040700f8803195024000d0801051100c1d280c00d0001c0b54540400c50841c991160240114045218401f83d40c480c448800403000a00e200100c6004180101a07504000c0340d03c040114021403e020010740326540c4c050100700b551114400001d00307650350340f6480c0c04c060350303645040c4086240032108002ca544e085840c01d13049082c140088815244140d1045007000400490450016424068080155042080401d00c4d0a01c1030440500b5541d0400d004480c80c070304580c41d03c41d012844292100400b110014000301c010039180e00156030b0f4480d00c9000c0e1500d0b148420714 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 822771870 1250 822770620 822770671
    0x11011d040b061603020d02010501050402130308131520031806160c06050703030b01020d0905010c02030a0b01060e0108070e0901151b0503180a0506031503030d020d0b0405010509060315 81
    0x20000d01a1740104219094040040d0031030300c06800c83d600807401004030401601c2810030070001c80f9403042d0b0043d0b031007140300c440c28040c2c0f203540c00c81d084c007242c6694000440760703001100340c1c0e00c000425451243e102d807562800e6a03c0c03013814103541c05104009040305080c5841c5015248031064480d071910795840300da80354441c0003096044080810710204070b800a0603498481c00e2410b1000780004c00c0166001c80700a400307230072188074042c10429031220403821505c050021010865100141d04215611504050541c107001c04540d8002614840000c80e994855a0b82c038040340b0340034024101a90800302e44030f9000444044107002e03c000f0301e03002071114041005c20a031641c003e0000e951035280520841600002240405105201c01034042c89160350300011030b9001000c0c08000900c407884034001c01e04601030744c40510355440c8085103040340c0070225008450080003c40d02000a0380c1c03a00c04014000d04103030f40e0690140c2c440184c2260068100c14141d4002342e000010ad81980445450304 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 822773120 1250 822771870 822771907
    0xa0b040e04080c0a0510150621110f160b09030f1603050408061005040608031c0c11030403060504061b0503041124120106020304060f030f020d050a0911011d040b06 72
    0x1030710f501d603442c0c0008040d0707c602600b0001604451404400f0305070f05514a401740319003003c02c00589550f88900b06208644a01110010784000c4000c40c0c0b02c02007010084940d44802c0b4080d52031005140019031102000b0085510f03444542841c3c1d800e19020f0b0f10621902c1030794140480600408101c0440c0c804e03000c0000f07510400048003d4204a82050b09100540304154483d011591044c08005c0b501c0340900340c5c0300254095010002511140d0740000c44802c076101002c40c1460000140c08820320440d50055489a0301941c000d00c45180070314140e00d0340d030701d41d0608100001c1d030520100c0c00041c0c04001c2c1c00c10462004080d0701036104801c0c415641d10304000c0010506c1800042d80000d000f0300c0762445030044c078180c000780d03003400e10300710002d0140c0c01c08094540c10143d40e540200d100317030510703410340d00300400501c001c007c1c51174548019170080610f204140d03450314400c07000c06165032144010200000e0418a0450780042640c14440a0080d221015501450502c80e4030b100595103041c6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 822774370 1250 822773120 822773143
    0x120c0f0b030402030c040203072709330609050112140106020a05070806040807080703051c0207050c0a18020a030e1501050117070c03080921090a0b040e04080c0a05 72
    0xc29541c0c24180704151a011000003014052401401042042504151481c42c001c2a0003218270400d0358414401c205030304660001c2d0607051501d50030074503441750010205000a890320780c40f446000328400d40c0742000850f11840f400901150b1007400035501c540c4954086011000000c50200d504412682504070241c0080d80103070320000801c000c1c44010468040100036401c0649100c0c2000d1300c2d0708410344240075000e0704010703000403902c040501c10300890b00d0381c1c0c1c1c190742c2280c40c5c0008400300078041d41c410a019074451042003581d07500ba02d0401c1440044804c8030400c407072082c5020b41114040e412000d808400c2c5076443d00c5256502006210301c1c1d48202003a0103081d070560404c1c001400044d8038802100d0a02c003583e00b0449406e07040561030b02c40f80e030182021881581c0f4414036074940011009101940c8490740c1a03018044040800340c00c010b0300480750000807e44860b04071615010300d00c00c1d06590178a01c1c0200740410b840b0b03001042d40758020b074151101c40c0d1260710380c0d074503101d02d1481d07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 822775620 1250 822774370 822774389
    0xf051e0301090506060114070b0109090f05010e03070201120c09031203200d0507481518020303041a070b09060402040b1503041407180509100c0801120c0f 68
    0x4005c05503030710050303a00c1c080e005625070509001481d224070944007414018603500030754901c210428408600100041c25070700c0002400060b20b03140145840790481036049001c506118540b0034901128090420301440c25079940c41201d10b5070322020310300740030700c5480c10030315980d0000030b54949501d020544c12500301c2c01c507007541d480c801040032089460003824601003203251325041c00e52002c03000e0703146084580100c041c2a88900282c0113502402c0307003003c81c2e1010003d90095400c00444a451000000302440708001040d92500701c1d012020300782c1002503044d01308000034095821a0400c503005c0020748240541001000d07a119925008261181e43c002d41c8860200400c519083c0201541484241ca61582e409441c13000c10b200b60001410003061400d010018140f06242001a40003c1c061502c070380e00030309180e220050003464240c0e071001d0280a0707007010071444100c80c02441c601032070390350f51441642e10f0100d2072403c580b0340c04000c555403103004500248040703041601074041d014012 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 822776870 1250 822775620 822775633
    0x206132403060e010b07051204090510050f01091707050607030903060b150d020307032a11060907030b0a020403020303120105040b0f030304090b0d05010507110d03060f051e03010905 80
    0x2041944051540308442094200442406020b0002c6a91811502203c00143d210019072502a040800d07440354203c0440012a0001e10300440b81c10880c01860026032004c0201e0716a0240076101000000701404140441004c004c840d0403401e076204158291415a007016885400282c03555020031400d80004000200c00d206100e8248030741c0c03103842c3c0d044450150744d400b0002080302c680a110000d0340d0702c40c2e01000161405000c0d030412145560644038078411440b2081c007820506403000e900700300060b11030f00e0b00c0005150004005000313951600003007803403603d180d89114902c00014000400d00ea001c3c080000140c0f0304001410720503684043c505015030520782400304880c0c3c1c00c00d081d8464160100e030201c00381c4001c0104d6060341c20218020a0580600d80481c0e2465032450780202598030b0070b410400360030b40c41801c5032506c4903440c050ba90945181c1030101d041c1c2c0c2e030b01e008a581c220039955003004503180c8074050340400c1403c6111075100f400d0103c006401c54894400c25981034001c0c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 822778120 1250 822776870 822776909
    0xa1506231611120105090703080705030d050a0516090806130215070c1d062107320105030903161406070206091c0e0d031b08090306060402071e020613 66
    0x60f044803062a034000300172924011142030307528422403101030000640041d8907028482c050044a51013000c0b28070503c85400c1c081015401007030126560000b46c074a41400058443c4100d01d00d40c22100040001d00703054554038906154a030110b84104d031304c10441003003040c40111420140c205140180320a520013840c191002d080c04d03108002c192200d0401300308000c4130759070707203080c0214070080751240352884c1d070180155514000c102e8001c21001006c144a01402d001481c20702ca04840c0307141016040c9440340310042d00c00d03000503180c0c1c0085820502c0401000000c038281c607070071180500b91b1031042c103100001d80d42c2010f40a651483c0143c02410401845900421401c000c036480b01d0100d4003c0da40180d002403900410403e00707482007410340215418940b164030b0807002c482e103a291b000408100c078034005626131300056440e070081c025500050b940c0d180510030b5401054000d00c50003d04080040c003605210004c0314200c2c1d10100500602101041d0390381ca40b0050400c0050070072240e90790 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 822779370 1250 822778120 822778129
    0x30f12100503100e0715170c22030c06020d0c06020d090f050f151306051504060602070f09060e0403030c170114120622081905030a1506231611 63
    0x20b1b002814400c1c00c10003e000c02c59407041501c0500b585060044034540c540000c0800184540c100301c10710b011141d10b81c0000d0070f403d5503003001164401d110710301c005136403290180c0e10740b00f11012640120b0141c81d0105c0c04664560028105040e118030002080f0180703607500d028024001c0c07010b41c2c460b4401c032044035144c00100002074103a5580712000c00079140c07401131100c0585081600500d40f0783c5503c04604020051004d50130911b50003032041c481d154490000a680d804207201f00d44022040101c005029103140c89003006582041107800c41603595510240d02410031180c14500b0040200403448008a001d14103d01800ca04410360021020805c10000c05c0405640c1d907102c540c001c003050249000c1c900544058001d0b040c281d001d100030050800703110328050382e561040c2000c2321002601d0b4091748440114070a21208404000d00154450a42c8600d1958020301000c500520022804002000d03125100343c031203114070380d1801c40381740501507240ba41c603a0b084800f0000e408454015241 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 822780620 1250 822779370 822779383
    0xa0905090907030b070e0102010b03030708190302090f1521070f0512040b0403090b03090c090a091203050a0e1e150f040b25020c01020d02030f12100503100e 69
    0x442402821001d0544e140c1c60b402450140141d4148160301001150a074000e412101e08140b008003541d403a01c0c00707410088160340c86150703c0303240705442800120314207020b442959240f440c00f90100703035143c3c1c818042c0195180e0349040341d5140c180c140f060200e029078401e6650064440403804203c0b50620001c0542055207031421001484018042550b8024003014010b5110b500150350b0000c603102c90806540c44c01c1203812844048500108214034440005540b0584030400e68414101d55500d0071020100c0d019128002d1290742004540c0c03104621a4101a0308109007041c0000c065800d80c80041c68502a10044d200820382d072200d50001c01021300c034031108109250b0080c0c01c41d00d0700c91030410f8201c4006200814459105010940320202c8143d101c41c4801501018400d82c608848041c2d07072800c948058030700600c40c40003440202e51011040c0c51004041c0c18080303040500d900800c0340005802030140d40840c184450004013964100000d10710907250510004040202d01200c0b424143c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 822781870 1250 822780620 822780631
    0x8270d030606020a17030612060c0301060e011e031a040e0106141903060c030207080403140715021207060e070e0703050903030f0f07111c02100507050f0c070504020a090509 76
    0x42000c06440049195005035105d44138082c44403682d265600720015070384401c207600c0390025201d20820402060002030065040c1c600300c0c0c44600a050f19100110f071406e4a8429049001c402c0401e208107140c0640c110000380c0c58090312150111b0301d050040703400c07912082c001007203980d1129400c010749443e805160388c4c48038058600600c610b070303400310500014950780300081c4503d540e0301d140c0303114900c29815607542a90041d0800e0340d440e600d041c50b030740102e8025010301040c054920001011904004420000e18058000d490090310508041032540c102c1102a1103e075190400148131813400d00a0741701400c1084c10841050400580080888030024180780440c0d00400c00c4c418960180d901144c1d0081c16102280030716968643c003101c002d07804014001480c03003864020042001d560f03c00148224840c0d086803002c0b030b0001618030566030143c4407030000c6801004003c8054070764a0050a4820ba042d00300c0b1035403a5100085412a40302c4014400000c10202007444280341c071040e0742c1d8224 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 822783120 1250 822781870 822781873
    0x903030f0b1c030212070f050f0c24040e0702010c020601060e0f04090f060c0f0e0913020f0102071d1005010c230717060a0b0d1208270d03060602 64
    0x25110180400c2e100c01c6056421000503000c0c641002c1054401c000c0840c030b90186261664503000300707150560001c918110101c4003401200550780c0d041500080c0019007003030062101e020160710700c104054820003030840c60001482040040f030b044401c8490a13000304030f180d00020f090540d20200078244501a040700f000c01844144050f956940e01c01c480702c5140c0100c5002034903c1c0c1600d0612101c000c41c1100800c41814603041c0e032407a40d00110702444286e03998590285141d00300c1d0800050205c1180c4412503031004511420150400b400318501c03034501030048414540c1c407101e641d18040082c9010040b15420032082080c0d03c5d11811151005090a0904c0c483d0744045980329214007851246075000702014510101500c01c00304241d500030840c03031050240310f07031a14a103251a004125070000b0f41d182400072016841c10700e10712944050b80c0014000320210110b80040310b2800d40038004124601200403800e8281a80e00c0017001d00d00c100000800710303119107000103801c2e40c2507139005038190b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 822784370 1250 822783120 822783131
    0x608060907090e1c030c121805160b12062818020c030313020a17010212060d080a0c06020904050f040201140c070902070611031e3106110c010903030f 66
    0x20300361241102d5030386030714030b05022900012091b4110b40c0b5415152480d070a45081000c40000c800101050404550160095500d04014008400580f204510516140c0c0101700800e801c1c04084145140c1c0007032000717001c101ca0284031071081310342103c00b40c0a1000c5800c07110082147d07852600040c40c420b50000780640c140180200e90035101c3c08001e00200c0321b1045c010403002190b440201010140814a003614000e514501c9014004d402910a08081c0050800411514544506840d80d015400040342d498010a42c0e412100c610700d645044410729001d00c0305008540e01c9000d224414106502c0b102c01614003400010000c054081c0d07030280d010070410450305108004036000080d103110540150780c1d0300c1c5524000c1e0041c9200100c03000d2074800842400110300a501e003500e0035044242e5010040d4640c00055502d551420f1241c800d888200105003c202c5958508156020b02030b01000070142005228032610394004268180e150b5541c0c4800d03010942c041c814491145400e103010041b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 822785620 1250 822784370 822784393
    0xb0d0b10050307031815020405030717060606130e0112020f0405040201080621011104080d0504050f120313150f0206040b0f101208090103052212030608060907090e 72
    0x10310b100107041c0c14101a00c80c8603803422802c4c41c14800b811290300c00003201c5584043d2034034900039002401264842d025440b40021081412041c1595010f0300f8409410300d07842d00c800b006081d41c030200312414a601804c2d00000c1c1d42c0105e02b410f60081c134103400d100c44504600e204001c42c4030b8140202c03074030407841c09040c0300160368411111b545c440025107480c040411110303480003180814012002c920740c285600e10503480d42c0d41000d0300880e00c10900711500f410300c0f290165014005c60080075002040a040b061841c0b9001440720341c1010404c0030342e807401044918007101d0281c00d80040d2420f80b2414070307441d041980010100301044d00352020b01141e05083e41d82245e0458040e004182440959002c41c10840c4001e0308280200f030070015a1880c02064a0962465080b100403036000c43c1c030701800500400500d00c429949da00c50002d180709110341300d03524003c80c030702a4800c503420540c1d41c00c80428500300400c0107130300548101e0000c0c40464030b055020004d540400940c84076580000301c0780237 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 822786870 1250 822785620 822785627
    0x30a090e160518190509070f0503150f130501030c0b04031e020303040f17012703140d18060b0402040302100503070c0f060e01061e120515010b0d0b10 66
    0x5000509841d06a90b00c40b0042c64038811201c43c84402c5a00600304804a13003041c03030303400100c002c8035001da80f20710071540c031000141c0f01c610a00c44004c001c244204001030b40d0394141c0c0052862481e00904240c45610501c000c07402c101095540402080d98440051050122180282000700680880645002d081d0354401d9003541d030160142d030704c4d11151140142190307014030985000e800c0c460683d0300d1040d0389010026400f00d480000e80100d503c0e0421003c3d580403005201000d0107010a840700c075501c442da400301c0d04081e0800000c001d9000034041544d8a0f09140948030b000760414590135500f031030a04004080700c481c1c00c4a40d2050b4410001000161140e004100040100341070051320303640c41f0041921000159003004100940d0700c0700b14020031030705070310404003940074800812581d619403c0390045008214000c0400c0b086c02c20040040a480c0804032003007030b01c94015242d11084105d58041300444c00c1e040400c1000340450680c4844d00103104000d9851011114041e40084402028 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 822788120 1250 822786870 822786901
    0x60906040812270c0a0b0901050d020f0c1203070f022806201308010207230708060109290f27181504111203070f03051905041520030c030a090e 63
    0x2030940ad5008510b0007141c4000c2c1c019195081c0300c00d02034651101e50050582520350088404030003184001980c0c080c0703640700003018802196061100e11175042c0341c411030941e1b0803002c00c04890407500d854020040030380900c00d0000340104d049080351207040300201003540a03c250003080ca56841800040c0100750082400c4554120304440c510903144202482400d01c44e49800401d0603200740e0000148032403081d40001140342094041c44c02c2d01c900764150307144002c5010007080c0d0140400d601c507070451510600003e80300805050344e4070081040e604021a407038088402102c0c151081c030480d851100140320042e2000f130080d0b0051103030716155484040000007410b10f40c2c0100060100341c41c10b0b040402c100e0f80459000403c3c0e007038800552078000d14a51051000e681c0c00f0a160640d00c0e11a805003064038140c60000b2822080d1f101861000c40310400c52982c41380421003115014080e0060500c014602072900350003450781d0b400070b58000b0381010b0007a0301407000c1080e8034007001545d01d05800c2c81c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 822789370 1250 822788120 822788137
    0x3010b040f0b0a290307050706090507030b090f0a020f240306043c02160b04020a1d0c09010c0b0106020604050615011d040b1206010503060906040812270c0a0b090105 73
    0x910317859440d03407842241c0701e0003036520003014a03242c0140c1d0002e1010000c1c2c0f2a04680c803420650606588170004030740c42e00001d0f0840c004035408170348180010315090641c0d18a045001d4201c20114031540308030004070000844003503400308000140009410a800b600070015002c2014412151408180324222600051240d00c0c9210854012810030303243e070112074550101001c240001038082c02c2080d8113520944007240302d03012440000400121559506082e22103104086d00b01e50349d000740841069100000d41e504003e4158490800201c0000b509406410720b64002c0c0f00e18501854500d14000014004400010794034503400d607960fa00100d540403e0100c4800501210b0320000450007404003020360130751040c10007090040c15640060f1150403030700f0440441d03815890309090107465500589001e0070b41c990400c13440e4240c0441c10a000c0c2c101c41c51078921540c0f802e030b480002200c15031942041a542d00400b2007145149060340902c000382001300c822034984600703600003825604c5540003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 822790620 1250 822789370 822789449
    0x801030b060406050d260417010b010207080304061805030327010206040804170c03010501140328141c0c030e0109050901090f0b04020409060513060e06040b03010b040f0b0a 76
    0x1034100b07021080310200760008945003411748880e2600b45072310b2450004d10700400150301e44420704107103610000c1c60f002154683d0b07002d1407500381851f10440c3c20101c00c000345442890390b184005082e45003000103061140856050707000e801d080b00e0707425000c401d05440081c110340c803040500c004502c02d50101d8040780c0c0121207000014200150721810814420030b495895407a050000401006030b554408001c00704506035440d614056490200150038803130701400d034181040311070b40004c464445030341c06985100f0448591007141c550140c00024000d0b071040014545000c06420503800c502445e0041b031007420100301150425010500d4410f051144485242d00c3d450000201c081a40c8504150360001d0400d558858403007001d40302610482c400c40740902c1389110300071031108451046106035210110564250348031035007044050028039040e2607142d56542c0241e00540d66601c590349800f1101c0d90081604010101006074404ca107a21503510034110482c040340d03e4101e0908203004060701c11 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 822791870 1250 822790620 822790643
    0x50a05100c0209090f0d051810051201060c0c06050a140d0e061608070504291611040c020a0f061104030b010905100501090806070c02150a0801030b060406050d 70
    0x841c0e8507215690065080700b07599051142101c8045161000c0520380030443d0030000348400100c4030780c46200060100b461401c403410043e4a4105083c4900020900d08a804c08803020391030700c9070340801c2e441900480c0341003440701e0402c50703180321800041080c1d042c12402c01c010440060076200c407282807048a01400038640c588245190b100380c840c41d60301800c44103103103804007041c0c0e2001c04011413540400d000e035002039411441603007210706030f80030f0042055041000a43d0103400740914a0342700c803911f0b0140038a468894401c290120040c0c000c410003502c481c454828003003100d40f54084c43d02190011900301000c21240e0b07400f00c40056028000090300350001c0e40c00c00441c0203a400013040c4103035031400011408025003026015942c41246c5203055540e030001500e1008540c45019544c1d08402d0000715064081c40740141c1480c000313080e00c6c0e019403004044014545c0b01c84a100045542480148244a04039055690109066500f0030119041c640000c9030030f440308600605101101 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 822793120 1250 822791870 822791899
    0x150f1504021605010e0724031104090906091a010506071709090c0304110f0a03030f11030d060e0a0b03060f0a0b0603100e0708070e01030207050a0813050a080304050a05 74
    0x69048918903441c201028482c0d6560340380160190080003001e80551050301c0c40810028003c3d11007001d0a4164880807170f0301440014141c000c1c16020904404940040c813000905054038010840c0c42440789100003145a0035113000f03800c85601c0880c1a003c3c40480006001540304c4c2e004807540c49421040302c010f11041104418624418a52801d421440324803c2c4030240c11000003840c00b0f14070a80034069221a080203110f40340b030591110b41d0744500007000400c007107401401482407900341c80c0350403448034010b0040f0a181d81d1014002401c0c090340d0715003c010070319494601f942c015481c0c0f83d06200340c1040f180029075801024003ca40786e074001c58003051103940564451143c011010f0000307a1689400c10000d01c04002c28032401e2650b154600003d045544910b04481c8100060f40345e40c2c048500b03540044000b90825070f07044a0b0b91240c02c0140011800c5d403005820302500b0880402d02007400c14091041d0440c1d10351000c139403540140720601c0f040e5221030071503095031002d81d91840403410750b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 822794370 1250 822793120 822793129
    0x2070608130203031e030105180c0702041802030f070602010c09150302340c05060a080106140d02030c0c0d050a020a02130612030e1f0206011809050f030a02150f15 72
    0x2e56417007a80204208114088490050002c0c6040315000c03a0000d0350082c008040e800550411180400c000c1030401046006141a51150f000860034880c9244541055808070345010031041841071941d201d9201000078035424000c440a0000300e20748a0111417400c4c000b03003604610903501c2c030203154021407100382c240c003640f42e8145e4030854403240060413000017105001c081e162900030390740000301d0100402c1e2030504204845501246513100c19140e0718004003105d1304818042c2c1c43c503880c142002071402d21902800910300446112800c0d554444000b40158503111950380c2101c1445030031312142c5d031b081303130041001c90360150180c0784c1600c0c0506003800310008040c40e401143d80300f0500d8089100341540500c0420b05c4182c1642d07040b03050120100c40d01c03030800a2501303010040e840000140462040c00c070485000707500404c40400d41e540550b0f26103081c20b62603440700002c0c0c1e0000c1082d804060f81040100081c04d00e1034903140301402c3c0440541d4110304001c00c0c0c240040510b08e00480d09484 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 822795620 1250 822794370 822794377
    0xc150509060403030f180b030f0a0b04090303020c010c0c02060304110d120c0606090204050a0b0c03210403080a060b030f04150501080c092203110703060c050a020105070207060813020303 82
    0x205810341e03039503c0345406031004aa201021002941d038280c1c40948204400d82c590a8a105004807401c580d04c1800d601c0280310001d012854040c0c90b480d40d2102600c842c048d14002c03034843d49000d602c41c0c00c0825081d003164850107929041005d41107040e0056110714044942043d00030811099492900c0e0121344e00a52143c0300038120501446280b0310243c0c000b031440f18242c420b80c0300703101d0036035241400000d0b0b0040d406072691002261500f0444c0f04405002401d002d0041c80c140e03418039141c0925400c0072a06c040d00d45d41282e60490400040551215949900c28030036001007050500300758a00c500c901009206104003071034007000c5000d03c01d00d01c91881c01004008420b0000c0e42e103581015458150550115010b60003000100d0074110a0300d0114034074a501d0000040c0c0c42c03809403021606d80c032464240852500400340e002c400b04451303008051440e2040c0d00c07400c0e03941041120090031100020050030440d081a02c1c01d0040c40e902c004820b400415121441406428500000b0308520 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 822796870 1250 822795620 822795637
    0xe15092b1b0816031707030c02040f060609090203040506070e180a1d0c090604090c0308070c0e090a02090106260907170a080904151d0a0b0a030c1505 66
    0xa8101c80c1e003400074244541680903122070342e05403a40766258102c195800300d002e010041404a040b030600d00f42ca5803000150640c14024540418074080640115044880d0b88070b00020098580400307100d01c5030000800300003400c0058045280d4030b0b00740c940c01c2d1100c001805010400c00c0c020a8240c0700d55840c0301c940400b075601841d0003100d0519003a644000c06540b00c100c0c0414441c921030b08000d040100b891401c081014010165603a218030410000302102d0300110b503080c004000c0400442d0b81e2001400425114216511885041071a10341110000170300c1c000c8554411900c413001a211998001c2c111000c07420b04100d003000c83c41415a005c5031104001c2c00404240e820090240c400280101c01c894084500280a0400b018014bc1303500a155000d0f003001401c1005000e81c3c20a41c2c012000c00c007208036602c2619444103041d540a01c2c81640b807070030307807007080040c131090a580340701741c011a40c0704454865002e0704d15aa509078032400d52203129440500c0f40e0b0300e14035250040003201d02c0318 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 822798120 1250 822796870 822796883
    0x3030e150403142505010c060c02190f17090303070311030c0109210306210609080c0c041413080705010e0a030f0210020306060f1c0c0e15092b 63
    0x42d032103000040e5032409070445602c0035084a180e50216003c103003500713409441c01a91381c1d0018050980b2154090130200c4140d004501c82d180b614007025203150b1007003901e18882d0442e021400420309041c1c25042c0ca8144c1e01900e100200f040624507a40081210f20303950303050407c0c55000c2c5001c0360381d5003580144106c40d403031542404075640c00c000b200c2985162010b168052080c0040d038860307046003103030082e0040e9145049040840c0c82460301d001e00060b07006128040101e0a0403a5980d581d5681e0000c0ca280c01c0c16034441000c0800501e031601628002892144013205185007007061054100054000a4000b40f00061540c0601000303400c030b040e42c0c28411044580c0801d185c540140700344600401c0c2c00050090208c26204d81c03c8a00849002c2d00b4002c1546007010b409140f40030080d4000c01800000810843d50594040e030540a00800d0311183d17120307030300d20340038000c248550f110b0196008031540070200000394290b900c0911000e842d002c0c00c4040b00c0178039011160a049900000030143c03c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 822799370 1250 822798120 822798143
    0x109020a080709050a020a020d080903220501110d05090607060e191202010e1b0607060606030b011b2a0e040b0a0f0924023009060103030e150403 64
    0x24100006080022504002e004004940ea100310b17000481c00f50307421103030068201c0c00038544082d100d01c10003604100b07000f003a00d103012145060100d04a601401050503042102e108218640e00400f100c80c100ba0310038081c1c942c046840000400c14414101e050384200f8022645000740009540714045050008003142d10220106a02c054440c00030034040359244180650190800c1c410b000302064500d0920040810300200000b004039603080c00411038010358140022404241c40f80502002043d1513100014020041c80c00104040702c1c1e130085011403010030508800103000e901c500724203204c1c9500651580300380399030366054030880d81d03014048698140b401d0005000c229a4510301583c0f005204012144c0c03420006015910f80f2080940401d0301510b0b80c001709889121045150082103030010300e40581c800d070b40000004130160014104aa6000000d8000b042015131a002404407006104c80e40c0f650341c004041c4808606524060040250303051f0300c4030400d4040d00d02a55216420040707 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 822800620 1250 822799370 822799379
    0x50309031606020909061206010501140903060a091e0b01051302090a0305160f08060f090c0411040306051b030106030f0902090408031501030b3a0807030f030606200109020a 76
    0x107900054444e40c4240300d100b01141d0f25140c00d940d18205a94000040e044a03803803d8015512440840c030007010b02007040044040c0c5175030038024184180c1300c2000000d0361200d5410402000e200c0f41050707400005c01e084ca0407000c51805080c041c111041140c40c10451003403940303030710064000c0041007900642d1120011041280200b584a81d206c2518a42e04106503a034280041300340013446542c00b07540081c0041010703101c002c81d1a0740d200c0c800c0c2c2d003100c100002d01c5021604030b415a50494401b410042000d00c10007006009060b0000d000d030803142003045a8402d92095880184070785c8090550b5265044044a07164021a951903002442d41980d86000d0034548100c2e44200c03200d8000101d6908000c0056020384905004040d002c1c1c0001c0404505421045101694405155a06400000180c407600040858070a418030500026440e403603503290142204c4400580d140c141400d185080c40441c2e4070400104040c50343e84d410b007a4a11281800b1401001d0aa402a402056405e800305 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 822801870 1250 822800620 822800633
    0x7061109120607031b0801060f0905060c0d020c2b030c0602032d040c06030209060c071e090c12091b03110307050108060a030204020307110d0f030e0303160503090316 73
    0x40c4268510348003030200501d00071070420545c00516003a40426801d00c014050b6030700c00c00001c4a09580d90900c0348940385c54100049a40e0414050b2540d10b5001094000c070169051104001885040d514070820400d480c0780d80c507289084e0020f40c003e007980c410200050511036085061065003140c0e085540b41040d00c41c11b42c698090088240400005501c4006015040111148215003004203044040c3c01c091089001c0c0d4000324509074003000a010b001d41459042c001000202244003017003070005580380d9142d00100c1564420496503150002d80007016030081501501c0080d00c3d40e0014903002907180907100785900829081c03099603442c201208001c807600c44900100c004030115a4155640d41c01100c0500742118010703000640d86030200b0060402ea000707103802c12820b0400710249001c0c0e5000518100c05480d0010000f4500c1040070000e58045c450280c00d0100c0c01c000d14075520b40300e08a11480044c1400c1e040400400000055030040c09200766103808005101240000302c0350305004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 822803120 1250 822801870 822801883
    0xb2e1203080105010804050c0108070e0315040c0f0305070312050c0f06070201050907380307050717072f03031c0b030303010510050d0b04090b1b0c030706110912 71
    0x480c00300d040303940042150360140326400e11a66002c40141a1402c111004460252020385020140a00300c07074540442c0c1d40a11100000c0120018007032854a0a401d1007805000d40303034480f110703000181c00184007003400820210150703508405110b51160368004211400c1c8120401c0d080d1600580c201200701080c0402d44da40244102e60081c0f000d52602d01c4201c0e207a500d548150307130103002d8203e03c541c60024440611155424641c84200c860344840d88105400d500440301100007600000f480810407003903d040950000c44a6881401c1454550f15040c00c080c81d401082208503603600101541440a1808081c011001c0c095035220616291088012061281c800800904000e1411024200001540d048480080000814400c841416159680205001e291541d00c0706404c0d5032944440c060364441c60310914200b08149041c051981c0440400502c851105c541005208071541d400010f4035040e83e0403401c00903050518156490311445060b442035081990944020070074000400d80 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 822804370 1250 822803120 822803123
    0x503060907030513020906040e0304260601270905030d0c0801080d050919050301062309010b0f090a03021807170705070803150a03080a1b0b2e12 64
    0x50403103620381c2074040d825110212080d890300031000064802614025013100d4020b44041c00005042000c030400c942550f010350024180c0c262024404020303002000c40d0700f103500407400042c1c81d281d410244150707a0f0365213150070280780000d81812104140403c0d40f0100c00d1a81c4017003203a9840300d07049404409014000c4000010803080707000091418804501201701d49401e90360f1924010b030321010490f00398500c250600c40851506404107650303c00344503000192064842d540d420403001072400403140710040c000d0b400786555500400c000c2070040c046e1040740f40d030b460f0440e440388000300100b0340040310350740060340c40900120350134040c2c8d07122142c0360300984440da56a0100a070304152014410410307074510b030008100b00050000b10b08d03608007550304150084e6941c01103407030703400c000382d2195219007003601c92144c0000ca010100f600b02030481403e000016030b43c0340e52046904d03a4841820018100005107110549900c03800e018040000000a0301c03642622340552594040b0840d804090700 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 822805620 1250 822804370 822804379
    0x90a03050705040b241b0105040f0623011401181707050a080307060504020d080a02010e070906080a02090c04030803041410020906070f0302030408030d0b09011202060703051c0c050306 81
    0x1502803801c2031905060040c0f01010510066600804024416400a41012000201c076103042c06001028021230340228020642c0049040340c40c00c3c0351046803903103074017140d1030904810143c01d002d0701500c0490440e40c4002000001c40510b00040c0c0d862a01c3c44200b03440341d0703090306011410700c1066012400c1c4100b4481182e0f07169403100144078a480c0e0b18003540880d42e10a11091000500c1d68021640c480d102038003a1001020316611038070707240c020f40c039a2005030351100181e07502c2c41e41c2000003500505c9030000034020320b442d0207a465140c42d21648064001c8000c0c00004103125260011580210b0703100000a070340b8502401c0a103920000f0401090a9000d6042c040b000390907140250391701c44000600b0203141c002241e80b00c10300c03941418000c90a500003840002101807041c0082c0810502e241d1021400c101c41400700902c00c1e405800c07175180541d0000c0400e0160b102d0805548104e40d05041056039092100000c803940c10704038840481d003904000d48101510b17400405103010b040182c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 822806870 1250 822805620 822805631
    0x506031f1e0e1902060715060f0b090f040c140c070e190f020403240605030105150301110a1e0e0a14240306040207230708250b0d02090a0305070504 65
    0x20f600000000440000303075108005001060124100201703c0b0180410b803040003d03100e40c0c441c9080c00940c40c66010007201c46001ca00c0c02030908004841000d07051084904100381124990082c5c4228440a04102140d6021640700c0b81c1650400881024000c01402203005151a010141003140701d007840d68134103400e0110f0303a6519180e0f03000b0b4074140c0f580400103040040902001d014040e2000e501c01c01340540304d02001030030347c0b02840760300d004145242d07043c84044214824182500c9610002461854040001e0001d00394000900c0d94004100040221a0402003204a409264001040703502c103003640c1d07001940b503070200320802001105850500e40006818588030802c1d4007015100e241d05410400164103180a80c000c0070000d1084801c48804030500c4c1d002079058848000c24500c66014480600865208000e0b6061005003000ea0302100c0f194030075002e0400340340e48070310340c1135400120302940d5174034894043d40e444c4203028041011240e905d00b0503a81c1c4040a1190500652410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 822808120 1250 822806870 822806893
    0x51b0f490203060609040c0203092d01051e0309071d07030e0a0f020906030a140102070201020f160504051008160f050102010903081605070c080c0f040506031f1e0e 72
    0x1e0003540d218600c010901401e1407481001d010142c01507059880c2103010420607200306559606020b04074981108400000007007022140c00c081c600581224140403043c4403001250250000e4040d84609107650151130b031700d0b0000300518207800d58110700985040d514a400c0c60060070940e19210380101da6082c003442018041858503140050310181c41d50180f606040d0150905100c0311b504800094115900703646241c6641881508682d05074107540d40020f299815036904016400841600e90064140032a003002c01c200400201d10500703001d07030380340c00008800050000d010303030062042c80c090311056404e19643d03200d01c00960007991170456442502050711b504c14400c046140b0751503180d81280b0b848410308000399058556a150420400304050000905031004110040034128001c00d01c0540e540c04004514600d0718005006514040c100181c031368000441202c100000c4010483c140603085550f4003514601c102c9007403c01e8031107a01d1080c43e00c907901c00f02003040800251107140382075 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 822809370 1250 822808120 822808267
    0xb0d330501060e090414010e100506010207060c0b07120e010f060b040f090b040603120908010c0309152a090503070803040b0a0f030204050d060b04051b0f 68
    0x2e002c2c44000441e10404114541080104103030000d014010030401d03800c041628509450341d00910140036000078901251104040c060250800000d00140542c1c60500a0060104c2c484150241c52225900c01180b8107501810401180a4a2400078070584003008005400307070440e071408018440c43c2420000d0624200015541036650b001c1c5042c02c01403400c600c80026241406000c0d500946c2c80900200241a1f00c0099040c803003540c9512070300514040d1094219410420075105041c20107914400007240052a0180b00310600780c005014000c48120308501005d941e03c03480c0304a000c154207a802c680007262003088803c21000c80750348548800c29513841c5c2c0228460083c00036802d01c000a086401844004601c1816140041c1040d560300001811140300d44e000b900d01a0382c40c8444511400c2c50b00074940e2000c01c51042c00c0108000d03038000a1540700b03104c0c090708203040105500e280e0b806d1000c1407041d0b00c05a030b6943c0001450802c00318041c061030350920311000e8000001d4010b0f1105 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 822810620 1250 822809370 822809381
    0xa0603021002010c02060c28020715020a08190210140105120c03070303030b030f101a0f220b0901090609270f150e0f0d02031204060b0d33 61
    0x113030b41d000c0c1c2445d46074040407541d2904410364820f042009480003030400c201c40100c0805c058419801003007203c0c900a400100240f540e0b08000854228505590224003508115074031003070785800014400415520890400c80c503075602d10400c9080440c07400c40004101a45816100101c4014040d40c404151495880030f00c01c001e1354054110050800200b4000c2c0d10600c10250050255001640d0300062a800c1241c0a076102c00e1003075584160a0055001c0e03000d00e00813640c2501c6119081c015180054109a003007825640b220000340301044800066402207040d0403c00745c80f1050303950b15440f009003c1c0600f0700032000b6803890b0203207140300c081070032704001d16803c0814284140007506880d00450510641000c0d10701c0e02100e13082d14010800c1d80b1403020400d400c0c501400184600405130b50501150301400300455000b40301030091580303a11385042c1c004c1d5210f0400140f80c40544045100910718020151120140c410301a203540d58002844400b814822a002900b00e1820000d008488 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 822811870 1250 822810620 822810641
    0x1c030b090a050a0603050d0f03051e04060b01031104030b0f070e061804020f07050a0c0b0414120c04020f1312030f110c1207030b0a1a060a05120a060302100201 70
    0x562200110714044015444190000085100820210341700d803202c07403901c141038180400140b0480010241c541d403603c00c080d00840003868a18410383c907402c3c0d044815801800203040039030b603100c900c00c0d07603030095201c4c484507100507550070344896481c1400c0c0000e100c03ca40a880d008062000a40e000f8802d4913000c4082e103005020301d042c14801070802104d2050147d803107400c95070810124201c61b540b40301900016114500405c8013844500c0e0201c80410b02d98880900500b0a21041c8100000c40d6014140c615042c0c600006664107101d070149030600089540d0b802a10021300f42d45002440c0d00141100c00c4080300d003410703086d030380d03c0301020700c10580790090002048503c5400c0424412002d44205030012000c0720348402120700001e840e00c02101145480b030348014410001c1040300032140d5884003030480d007040b104201426a140200d03420303c486101d240c00003962680107004030140e170030744498100c40c00170ba482d03c5000b150041406010a0f131060f4000301c0720207202417050143e1566103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 822813120 1250 822811870 822811879
    0xa020f03091503040f0f0b06030f0f1015030602180a210308070e0a0b1b0313050d05071a180d05070e100b030c0d06120819030f0207051c030b 62
    0x18504481c031150b00e410251044807228000f091060200d2104561040d00c4c0780500d45614640c1428401c2500d40b09a05210018a4104018011000e540862101c5800d0b1072800c1c08906400b650000c501002c0a58000900a500c0442d80200714104110404211701080d99031017800d41e00c1e0490520000041400c003a03e80740c0c4140000b001030300c142107583c0c1040550808112147c1c0150005681e035400e03801031a40b00f04045050090303002e100d54120b050f1048400910724007003a007035100403004068000c11340905c08111050003081000c004200090101469014552105007141101e40e1b0103c0040c8100c7e80150010451500e09030f40300d0b42c40c041d8000d00501001e40382400c2026400c0700204814280c2030491400a000c5090500642c0710300302c801c0b15655180103500401c001c83e4440d40020a500d030300400c1840006d030143c8200c42e80c24200c0346043d84406015042280604142c46e088bd854070f0003c41c6000401000240500005000141000e001020b008048084880200499a20 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 822814370 1250 822813120 822813139
    0x206010f1a07061a1309020a0e1509010603050609160f18080304120c0807030218040f1e05070b0c1e07030503030c030a06560a020f0309 60
    0x841c6020711140c00c0c0036001d0101141030007200c0e00c44408030303115120704a00c4207200ea5442005407400c085200c4131140800820441d5024075001308111203864000e0310000b072680c2001c110812100c1d0032141c40b0042c0104444025030715980000c024010544007180900c3c01d10340810110030084940041140055803000d2f9a0810310100f1502e400740c82c1c900410199000c10049042c150500041000c1c0440e0041c505d2032403400e1904030b80701c40103030307004030899001a44180010303900e14102144c003008130b01465003151a207051604100384200d100514621038040300903521940c003808840386600800c203035011346548908101b0107224520000c11903801c420500c540d5465840f400000c2802100b0032100b61507203e5644600c1c0d940165450b900c1d610020080212120190190070081c104051a0003c10081902a4840c003040006e0720b074002e042c0c1e40c2100694185046d0b07001c01e120510160b071000c00c3d011011001361384c0d01c005414401401603100c0c0e03080d030003400808c580c02c200c4080c02d280702 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 822815620 1250 822814370 822814379
    0x40b06071112121c0c08130602160c03060c083606010603021b070302030717011407080a18050a020d0302031902030a030b1c08031b0c011a010206010f 66
    0x340e080c54840e0312980441000801c0320510b00800064012002002d10b46a039000c031082c0400e21303c1d95680c16442d0301d504110f0900406039000d0035540d0401020320019850112602d4041c0190066461803040c0c0c0c16446490410300100c41d441c002100e001d00700801c03c001c8002e40840d803902084a0b0001c110030200c20383c0040c4800001c04d400c8068081c0100c8004085200301681000401ea0001c00001d802149102c5c0c4206090900039030a100400100030b00c0b03103542c1c0801e4480c1003601c84c210b4110b031000e0700418080c0007074200c81c0001110115200c06841d00f0390010306000d40a6551803149450440c109000901c48407481040c0c94002004100071043ca50030010031514459048045000500485440d400072a441070208034050700035545030901820010111000301002034840c0641010350031f03079441c1012542e0410383d00001d9481e600da403122a00d2010801d043e001d1102d5500000394420082019405000ca85421840025030710004000480e9220004e015a0964040d150f20401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 822816870 1250 822815620 822815633
    0xc09150901020a0204060e090d080103150b060412030201051b04050609040207060b0a060504230906190f0e16020d02030f0703090509012301020f0d110c041107030e040b0607 76
    0x240ca2001403040702c4003071416902080550340301e130b8003d5101010260030300100b68410b001c841c8050005103800e9050f50b01d19141d91f08241b4841818520b10340d606c182c01c141944981c003c40703014004201d100000001c240c03800a0007044110b510102081050066151640d6000100c83c100c03000148407a04013024002040000d6101d41822100155288000391003911030498860040085031141520350749041e00781116a000300a07040701d04803007050b001215076141030140380c000c14241d611210705160000300d5001d0181036041204400344510000482c0c060701c03400c41d88a03070048444201c0c4200c00c1c0304141e03681c4080021110260f00180072804882e0524005410100d000e403409059481d990000300d00ca2000a0f0000d16185140024001008900380d401c80f060480038401402c030010385ca080651104525684002080b4190308440306540c010845248102c500078402c000703101903401902802d0340b260b14120b000c2009900310101070f01d02842004202e01002d44050b10303100e502e59139907 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 822818120 1250 822816870 822816877
    0x270604053703060c0305040c12030c0606121b03020108040f050106050604060f020d0f0519020f01050c0c1c0503180a0501090503041d0c19120c030b01080c0915 70
    0x348501d007000300252420300c0c911803030381001400c8510070a04908504081d020380b19030205003401d040c00d003020300000845019031002119034807803050507000317603a14040381c0d20b402001c005030206090150100e0b143e403c064050000381d10510040c444800460381280c100440d0744030203030125451400080106803a64a18006a403040b400000e0158640002401942060b0030036800603007007000507200a9010040001216249d0800030217540c0103050081c05842780030681c1c0c401599000e0704000c0c140c000c100760512850414001d200903d0300c2013202c103440d004407003061000c0c8a41d40c049124460f18461044950400e070b61024a19542d00204c040551068000f0708405d01c10381030034401050302031250b40802c0b4402c401444c1e503549044030f481610300c1980100c031240c0e4000800e10003802c1000049400c480d00c501f00b0800d0399044808262060f89002150400383c2d403d14a002c07002030382c10750058400440c01d80b103e83c0d09880f2071b903510059020f4812031942020f40100e5a14103603103c07074040d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 822819370 1250 822818120 822818149
    0x1090c17030f0a0e01171311030c09040819090807120c0b211506160501480c061a0604080a0203060603030309190203160303020327060405 61
    0x1200d00c2c1c110301881151059200201810005024041041c0c1d250f07171106040310281440d041c403280c41d040040c2c14015101d800b42004100103440030249503035031014030408420400091009205240c24104500709034810b818100e40d80c4a05081d030260030340610540c8040d16840802030040900308107420b094000601c00c161926180070100003102c0c1802402040c108541c0040324a40c170017000483c40c008a40589885094440c800040c207a60701d8030300982e150360900d819200741e2840c0908080340140511021520400b9a981c5402d030380c403d804c00c458030350a040101181c0451001c0d81d2801d404200e100c041d5000503e2281c3d4840812015004020b129111980c41d001c10f03648000024482d0f0311950102c101034004a40380003d51406000f0b441c3d000c1001d5002d10b00e14a02800c005881d0010102d42410030a20700000000390740b0f040180da00c4540c090f49600748059264140a540e9411a440c06c00c400724010341d80410400301c80031390f80c2c1d00d90b4003c1c25050400e0f040900300182844040350 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 822820620 1250 822819370 822819373
    0x150103090f08031308032e05010e010509040f0513030f17060904140f0703030201060b0405011b060f050c030f1b0d0c02010b0424060e0904030c1104060f080f01090c17 73
    0x1403003800300e84e45c0d0000318010719800740785001200c1c1c2d0762802c1480f641d21800d81c045c40083d0703510402c01640c21814a2907010404d10b0940d0f80c501907500000d00505030700c0300c081c02980c40c0c1401c000d40c0084564100119502036110241030804031113045a850b0140c840742031101070548045845410f022107801d400520400c0074800004401084514104100e0583e0341e60b42d000b100f04106040d020304c600c1d00035204013078070240f80600704400a40381f064203088101c01c0d4044a0381c0141800510ba0001e03010300c0c0340001c140a18180319460710550b0f0025510306100d03500302e001040200c0c110060244129003184821800d000031600240000e0003814070a9082d952680741c2000c841d9224030a030b05800f080141c040504902490f1103180d07035581070300700c03406000910407482280e65400e2060341d445607051410724003101e6185841c5c0b11060307030204402d0b0020f052850100711a00d124540f40207450111b412030310550104016142a41c4680802400b02010108203108020704110002c000c6c404100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 822821870 1250 822820620 822820651
    0x80705040f021b0723100c0206070503072001080f040209060d1a2a090d020d061d06061005041a0c0d0201021201060e0108070806010e041103150103090f0803 69
    0xf50246415030880c07880078950300258401c0c4180044001c071a1802c151004032500786078001d40c04202c0030000d0028180034002281680005c55440304102c520b8036a025064944603400d83c94420b440704600041c030f5813542a050001c2508d540f01c1c4038018401c860205a9400d107841c0e40e02401880c04010301419004680c0ba40c4003c0400c900303101c4103a84103803801c108802d514141100c40000660100040da13581507505d242d5003e2075101041c0d900891007150b0b00c5001410a02c0011750788144d54400410749400c0185084000c00501c104420000300f16080e59420b07030340c4104001201041d046d070180854418081400a2103001440380034480d0708482546c54198400c400600c0c10030041c0d86000141c0d00081d0400b00240b4503000b0394014201424055107003040c00b400a4452840109a1800c00c5500301c006078880c2c2c0700701d84403a04254098806c0111030000011100158822900f08207142c0a030082400654864401e4080d6103402015901001e01155142d0080b5400a0040804c00a003507 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 822823120 1250 822821870 822821887
    0x7030c060e0d0203190f0906030e0c090412021b150c1005160201060f0b030c0c01091b030204051f030b090c0303030709080607110705060d02040b030106030501051801080705040f02 79
    0x104019030030b00185800545d181d054003010102541c131a02042c00c1002400442440c0d090b401c0114074081d542d0904010503944a4181030078507010040744030740e920000c0f2400b4401800840004003c0c68080c950079074501e0200b0607440381b80101010012034011040c01b0540103020013110144c850145041c0079a101003681c102c1c0e183c152181509c0d03031104481049450320b5141e03024802c000041100c0c0c114042264a02021804140002840c42d0f410707a80000f012090340c0400c3d8009641c20394080401802034004035115079030465a80004ca004502d8000454402069580d022000c00c07140c7d041e0180303060940e070b02c41d200340c079000d0040b007011701c2403e0701008139907000d1026511038502c4e903a07480c81c0e0500d42803a01c1e262a201820079420300500914a0b03881c02c8000c81e0035010749170300351046503840340b022403100c000340b180780c0c03040030701100100c0080341072030b450b4005504039038003202c013112070000e030200b030f0b0040b40c00a01c58001c96922401c410009418260084040000c803c44c005003483e401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 822824370 1250 822823120 822823123
    0x2060409020a0810060e010c110f0306190c020f0a0326040b040b0606090108220209041b061d1009090903020c011803020913050a0c121a090307030c060e 67
    0x500900000c50f00480c1000841400011039800400841c509084440e80141c0040c00c480c40200c8054408000e4896684803a16144420703c2000c0e00a81118564640814140c9140440c0f18510302802d080c220070180c0c0510008500c404141050042c00b450560f6640075508a103600d00d41c3ca0403040e140c84402804229041858806d40c09108ac0c0c8140e441d061504942c160030040c0711790f10404c1300340803060543c0d03804150309a101454080d80c2d104141550782c1c2c500a03920b45600290b20614071800c010421410030b059101c00e00072440b50103105611b810042c1c03000504440c0744001490100007501d0306142c02039064941c0c003e04d0400e086820b48508140342510110107042c1c0c090303031080300d81e0b0703501c2d5034050051200300140c900710b1841103046900107107610a000e0f098a4050a2441e241c0c400d100052004401d43c503806464401d025035980d000c11000d00001405440001034101d42801c2c0c1c5803501196441115544040c500d03000082d60151501c0e1456042600c00310750724461154020b10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 822825620 1250 822824370 822824377
    0x90c020c03070902040911160b04170a020a02150307170a02040b0a2f12030c0c01090c061b03090902133204020405060f0c0f060408030108100e0d0c0206040902 70
    0x80843d40960f4030740c01c014845050798074042e52021500301c10003c1d400808140c0540c0405103a01c03005100340c940343c90820445e81ca01c8402c5152a40c1c50024000c0400790700000c02250440c8246d88500300e01055009000850104481c00c40c041014240300c07403100c10865040952080358000010305160f01e800d43c031401d9420ac1206079002c50405200c18034661840b03280c100c40440c102203c0742035040c9803c8482d8940c1c001d1050907907460030110104498044203803d90b40844100c0f0300802c0007440c039043c1040078500b0703841382038045207146010384110044c00798482045a01611130307014031840c16684500951000c0c4001345526001d460200301003030304900849440514024200721004644002880f00d00c2844800c2c2c402c070320402003041171b601c0d18001d51340503410440300240c443c2404201741d401c10b03403517480040c0c40780102400c0001708580c190103036050f03d10320001c0701d40341d5a00d40d041c0030440c0e0041c251590a0752017000c04400b01c0f031207002c3c22000d03d440500428101503449804a003684c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 822826870 1250 822825620 822825629
    0x60c070609051203330607080403060219201c0507020d0b060f0d0b0105101403010f0312020d0207140a0e0901090215070b061c0803040b0f1003020307090c020c0307 72
    0x207800400d000880c075140b95807100c1c105c1403c0d0080c01044201195189500074860380e60300421001c1140c07818041c13803800743c1740210f800c854259985c841090282d20111901d024281c0441c00304440e15140c80b540550aa03956006040244079102210041142a000301c3e031269007088400c2145400685910300404191803052042c054141002170402c80d12400700203d0900460385224002c0104d03ea941000341154006d90307480c0c00c4d078054041c0407150640711814002c00082d000000141d800e9a00140d04c0469004500c1c1e1400100c241d44200d03100d00d090041d6400503481844140005602d810360f401ca4032000030701c01d1817010307641c0300500d40e100000c45080c55140d41d106139034030a5050001241c2c2d370341d031480000c1c140b9144296480c054400d601070411401803801c1038080c00c090071080f1400e01d4464024581c581caa03e841e29000707805502c200c94000100402d0b1000c92003c0071f142e83c8010076240d0090241c0015802c00c0c2680008011030b03504101184039030351608409880610565000c1c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 822828120 1250 822826870 822826903
    0x140a0312030b240f030a06051203180402071505070203160303140702012007150501140a0b0306031b0d0609080c070b0301050604090c0e22140405060c07060905 70
    0x1c210074042001241d401481440d040345031260b1284403c1044040b42c1ca07038040321026503144e41782c010140004015035001980c01200240508406020010181002803040d101410006810809020580c0203140d001030101c0c00313a0582003a40515600099030109040c4100c84c00c2007107840c0e1002c107001d4050800d0b00401c0c3d1f900f01c2500e0b020352406000d40e11644a000a20208860465060000c620b61040001051000c55003008002603603803040c072200c2d203058003800039503129048880301c4c0000c885202d1241400c03000c0058080d602c1e0080d00e104280040141c10342106050040442c9092500c105501c41c00241c018030018196101c1c1480300ba002d110f00a44880c0284081031401e138940c0c1180031540c8092004012641d6030204032000d4944504011845090402c0c060710080303802442e15a00000c0c000606502a690084040d110062202d0038441c152142d6001100400c0580f4040c2140c1c00210004094100040080213070520903280020710f04219200ca40c1824508070345005803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 822829370 1250 822828120 822828131
    0x30c0b0c0c0c0609030c0111030c060c0315010903030905060906132603090904080703120f020307031112070302070203071203021e060603070611281416140a031203 72
    0x95101004050050b101c2656110310304455100040e40d1138508100d03050402c14a040701150010040c820307101c00084042c01c403070701030818078410034141d04110707600000f070460710720042125803081e4020002c494040e21100c41060900042c0203655220302e13505a00501700b00610340f241420070207864010141809400495008030701001040340c090010030210307a00500c06a001075070f80300030031508950f00030f89039590351010b4a01910392600504d001c44c8010310707003e146480708800381c008608c11810342d50100034466580d650b2035107900440000d1030740310707442c00001740c002c0307002e075000301041030005007150401d55880e4000f00341c2100c10761088005801c042c19240843d00450440c4120012403400390000d80b030b020000c40c0c1e0b9001070788074071030410100c51b030850103080080c80f9008801403490801c6844003911040460841000c4008480804d81403040301c8008401040114141c00410515000a0b1401c00b655401d404801c407815448692000d001000030607880c0d102e5442c054035240800c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 822830620 1250 822829370 822829387
    0x17121305010201201801031d070311011409060c01021b0304090f1a04110c01140f1b0714070b041706010e09101d03040608040512090f0d030c0b0c 64
    0x940b040808222401180044c0b1615a03045407030640b010b29a600c81003a82502c50b820048020300044144000301c81c10480100620340e20110350441624002d07004c02d01b0106d004130044503c1580c1c92a2175005e480306010340354151400e00c00505403900e2100c00581403194a1020381c000c003090b0700c908070303981d80006030030002c4503c2d6000c0d040d8a109044c0c4c003006180c9441c005a030740554158140c600c00c55465180142c1840143e040d01e08031000304000b0490306900c0e01d0725100320b0300169081c0d1070400303221000420004000c0046802a0707238803540c0d00d04011817652003100c07014a01d421550b1a00a19801040440000c0b001c1d00040140900000001107124a014101003068000c1182400340340104406d41c4800101c21034020351a18000031032030700400502c40d40c1c1e89c440540d003075240000100064140d5001d141c45020754018416a071805031006e100618500c105200d094001292205880380d5103844013a03460014007031700302002200000d58440c01c10305070848280c000580302161200c03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 822831870 1250 822830620 822830623
    0x1305010e0a06120309061b0507060f0e0f15030702010f1104180b100c05010605030a060212090a2102011e1505090c04091515080601030b01020604020a171213050102 72
    0x801420000032003000e580f816200101052039a000c0e02d000d000c1091184080b00d42c0d106400006143c00c8800e8803078440d12454010440d6200d110240d00080c1c0c0c0382c0211007a8540100560300704000249100c101310540c14419482d41c20042407032055560b01c0082000d0303c0d0a6000c1d0000112a09141503644c509208441050184a2495482c40da00d840540150342d101c0c1c190400c4880c500e03003000c41491109143c01405061143c00060301030103613100381c000708003940d000340c4440c08419aa101250b1351780420556a80c0040c040503104400c1d40c481d501851919914110020717032107100124086104500c0841034480061040c41c05694071111480d22043e903401340c4024101c101d0340c107500390602080d820751a000f1401000f18003070380d0b49581d207480e4055040400003001401c6c0071a41417803149a000d0040682104c00030301181c245440380d200e661000c130301b030384c41254000c04810704141440300600900d0136040308494140309052000070b241b100c030000380c0b01c4415070300400070069040c0320009 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 822833120 1250 822831870 822831881
    0xf03050c0f0705013b030c151b1b01030203070909050708010501080c0c060c091903060e07050405040b04120908031b0f0109080403030e1801080109050d021212061305010e0a 76
    0x1014170810000140c1c0032685404103100c04100c1a140f008038004460000381011a443c0c403d60f80040100310200705204018041c208a1030801c02c249981c55604203030680381d0922000c040c81e03107044001d840301107600a5010f1034201400303251503120300f500d0b1030501040320780a4a50601040100c4010030056030b10045007a44414000340c96800c21044559151740d42e00040c0c131003521801d010410a005031100c06920110040301e60b40746420701d41d02e040410003001c66441c49145400380000201e66400c0c580981d9000b00c0c2e0110440d0036079911500d598804902401c0504100103540c50300081d00f40c0300308041e100d641d112602a03101c200002c9491841d00c00c83c1150500b00303034146050f40000c105110262800c60b0317018204561049000b00c0001c0752443c4800c410744852030700f42c0010031500c04c154003034401544240100e48101c00d0110044e03aa80c00030040d01268140108000310b200c00f02d030002c07550081c40c05814210780d440e032884080c007950001d0304000090b440007810031400b0281170164 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 822834370 1250 822833120 822833147
    0x220519090501021b160e0408070606120c0602070b070204180803270a02010203031314030307030e06060a0302090114120f06040515010b070305090f15040603060e0c070f03050c0f070501 81
    0x80c42c5039882d180041c044901d2034410421142815400101406000c8e0700329074800750f001c6000c001180e00c64501c52454031908405841030500b4020114041d80001003840c15201080019810f0019550812002c1d2813001041c5000c0c524554800002a1540c006580035006144103580341d134170b19000c0c5a203011324010701c40550740d201180c41c00c0587d801108030b9401241b2030240a0318440a13040c0088030b181d00280d034083c40e200000410000a83c1540308007140c514900686845032100d004200c00c0150b1404040d51100e07401c4010450700445100c07900b90800c01078070002142d0b20b0010b24a09000588907010070b550046010401084414003e28406a25102d0070100d00d50601010801501411303400801b8820700181c20056541c50b46c40320140391000800b41107000740e81ca480c0c41c80700d810030f102d203402190a0003004140c01d100c42000c203105040e103801c001d04103410b54480e03d8961425020aa00303005042090940c2040140f08407210300701480002c20045150600060400292002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 822835620 1250 822834370 822834373
    0x2c0a051f0f0b0d062c0616030b01020c0f03010e060a0b2b0b06010e060d0f050109021804050c040b0f030f070c0f0308070207090606030515220519090501021b 69
    0x2d00010550310711810340283d0380c00080c00654441031155000600c40a48002c00c042903241c805d01100000c0064520f00c240079602c80d4221f0400004020340c140c0d8415200180540c010510341c1c022402c08418004500d5801400810130005403c405800c043c03040d140e0080ba6611102808881e044c802840110304510300d070f413444444202920044c020200310340c020f04460498012400581c818070174000c00c1d0344024900d0340d81e01030791010000240300400d0000302d040c0c100800000c440310548203540000703844403072203042144600100001040002c10108460704244001f05000d40c00101505c68041c00304030f85992410141401c0d55441d0f401800c681c200610b1100c28400982030b60040120349a043c1449540b903240c81105900300700c144c0e0004c1c850305190041c00104142c4c142c1050740070303210096420042903201800d0001d08490780d46c4041414107c0c42071144004419408198041c00d440c44102403080620241000d44020140c142e038160f40224490310409180d00841c59880c0c145030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 822836870 1250 822835620 822835631
    0x21b0c0a05032d070e1603050a051905040c0906120b0c030606180f090a0f06080f1c05090301090821010f0b0f09041418012c0a051f0f 59
    0x10b040b0340c0d12246400d2031880c01030f041114020041410404d00e4040c0107099181d1041c0c0c07804408070000e2031280603001c00004e04003c0402e009040c248111406489190103240d05940499144000340002a100320748160101e00300088902e160f01c260806070907031074502c40c1c640d9090305007440340c1e85000d0201d5214101c1001800700c1503460500b01c0e102e9100c801001c0d0b119810000019117891864064217801c6403000d0b04203d03014200c0d80c4240c4402e0841c00e000c0000d07907203801c1c101d030b620030040715411b45562004407840c04014076401140389030340c410300d0040d14080c410408a800c1d10b4511504070703404d90b804101e40000c86406a41000c10100700c0d15903503215850407203c138400342e0082c80345555180000501c12044451a01140c0240c40d0241090000707580000407e40c02036000c980050003111006061140200c06016a490308158072040b4010740c54207143c5140390030100d40b02c000c0f042c4507412401001940138014112040320700641080f101c1d110040d100c0030303258010300806511385880b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 822838120 1250 822836870 822836893
    0x317010603060530060a0e0118020603070302280f080606071109130606120c080d02100c1709100f060506071203140f06130902030a0f020301021b0c0a0503 68
    0x260f00c22295050b0811010b419030030b81c1c404c0307601803c0c0d01401040303140503510400051503120341202d1103900c04c4200820441c0003d250301c2c1e042c98280c0000a5102c3e00420106c5c01140c8250050b00741c9003000d80000c00d074040c020100c0030301c0f80c0c7d10440c07541c00310b0919040d2684141e080100b10f5400700080c5d9415181045641d2007554103442000c80c0d0b0320505550b0f004c9000400307407282c107034040742c0d00c144100a01511841c07043c800305030743c0804507a0b41f0800304000c9007801d404101c201a41d80c540e0000c01820003035481c61000740c80c400114400704010908402e43d0b240c290b402c614010510b00014004031382c40c04901005655020b11031800c83c5081050400c20760b1540011180724681103401001060310f03000303040b030142007503005134410501d8000c00d0015995207024480d004140c21039102c0c00385900140074500391605501d01a500d500801800d1011130b00002c14051268402400185400c411121b40781c514005001003a0b2158000345083d071650030100e0881c405404124000c04501469 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 822839370 1250 822838120 822838129
    0x3170405060a091b240e010804260307030b1005130612060308270109030f0f05100606020703150e031c090b04030302091311041202030a0f03170106030605 68
    0x601078031003055454254000340002c0c2d0007581c114020940184c00d00c20364410314a0f000b4a5000540e0494044002c50344407214021310303000c4a100d00613160340382d40380e4942d1100c0d12846c000050b041040d049034605407105030101c07002144241c0194030700184c023278240402d01600c0c114858542050000401c2800d100c0840300d06054116a2185802a142e0b406051048090074150b8001040d940011401e4411005020000d0f28000d49160041d1400d1504100444010074284405456286545900404a0309140b00710b00c0650103201196551140c0203d04000c60342c042d4009401a0080b01d020310400019203260300c945403036518184002c2d428112680d8883c8034403101c14040d00c244903410301c2d080d601c41d0401103e0a800020360519071501c0d040141c06035000c9090f0700d1113040308803520b01648840d48142c1c80f50040b4903403981d040a0400c0d84100013100190001d0368503205410f07098000645200801c603003d0700c41d641c2e840d40120007561a2036140e90682040c5c080c1414108103100e152a07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 822840620 1250 822839370 822839383
    0x27010f0f05072c0102070b031608160c17120a1e02190309020109031502090405070c0f02040c11030706020c0f03040303080c090d210207080304060507150e030408010903170405 77
    0xc20300640c600020040183e242041b1070b4441c0c1c182030030100800100070030380030ba81e94506280f5115008165104a0800e000e405036400703a40100341508101c8000c9000300c080e518500a003107201510305031108041e98107088049409040d81c0342c448152042d02030004a4a00c14040030704015810105154111314504c1128686041010b588241c00e0303055a05c60316485006641000c038060440850340c136005d019510004d90540514104004610040e200351071540303201750895007a110000c1305908000140020701820000c10503110b68401401e1030074001014070a00c107100050340c4414080c4000e0420076103268481c400c0d002800100046038100c072020341d002034540703a12030791003603014000303a1a40c43c400c402502402c2045000c01e075414949131038900300c9040b60226803c907907507900c0d8156284614042c0c140041c90511203000001c0c807601b00c0a06050043c2400b048010700c108040e45140c100b5800150700340e46030500710f014140c204240412010b444c0d008010f147c9415183c085e910300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 822841726 1106 822840620 822840677
    0x21305010c080327010c03020c0106060810090c1403090a03120219050c010207050613140a08191107080d022427010f0f0507 55
    0x180100d028000307556101c40814596602c00100301901500c200744261140540320780440349080078040d8a900d610a641c0060b1213001c40e00181c0e0958000c1e0748900c05102842050001c2455070075201700950700c9112011640b00c0b280d01e01101c41c94640127001503000b001105100e0080c001184c1140028029614145860140d02810040340b064106411140b050500585001405000903103403000321007000606001090b1501410160111000d00e01c150a110a04c5d007001034108040c0d034001c0390f820052483e01700c0d03a9100d56003403241450b04c00303603840b81c0000240c01c40d220b00146600c9410744401e80b5031450b80c952140ea0b50300710719454200540510018a4101d58603100640000300017410103120a444045c03046004003440c0f00c0d10200c1d503c50110410030341303800740951400d81d0004000003865090308464101101c1001e01803104000c0c0c45200075030050180800b40041c40c = true := by decide +kernel

theorem cover : BRFrame.Cov 822661870 822841726 := by
  have h0 := BRFrame.cov_init 822661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 822661870 ≤ n) (h2 : n < 822841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
