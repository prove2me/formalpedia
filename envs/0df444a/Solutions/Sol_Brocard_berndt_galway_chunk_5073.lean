-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5073
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:39:04.681542+00:00
-- url     : https://prove2.me/submissions/3f574771-ddea-4acc-b777-766e235fba92

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 912230215 ≤ n < 912410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 912231465 1250 912230215 912230219
    0xc0305090a030c030605061503060a090b12160f06030213032013200a02060c0d0e160810051b070f0c0803070b13050c010c110a0b040f0602030304080313020307 70
    0x142903140080d13070003100c02948480401049103080020f1940c11410101c21501d5840d040380020081e00f058001e0594040c1e8a00505586407a440c101d009001e0086040700c09203000941c084900003072a1141c14031141a0400200b081842030099550350000b071441c0400c5c0034210b569420181001101c030591b0b00401b40505a803a0382d408000ca0400086030f40e000502900d5070325110402d0752050501c14081c0c0c0101300c0c00201e180c0c00a01c01d070f4884000000036407242043c018541c0600800c00744c0007401d1045180b82c40010307507055624411200c0080849000b080c0320324074a81555000c0b1100d0540c45003d004031b00508050b100140b98003403042502c0ba1030815259590b10811f031140e04004501d50012942208000511514039002102c460389401801020760382c069813405400c0d400d60401c100d00104604122004901c0d08010000922450748985c462540c070b4200d0300140705807008505020000a8181d0000c012a4000d581281001d480c558038010342c0c0c184186c4404040b601807140d00c0300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 912232715 1250 912231465 912231473
    0x160e060103180804060e060306090f060312030f0f09011e110d020c03070b090a0506070513031a16050c0304050d0503090a0b04030204060605040e070e0a1d16020d0c0305090a03 77
    0x210300344a00c0f451106846a0a082c0300410026803812580d0150700704000b0700c0b07200c0c0e60f00c0300c1e030a40c044200410004a680d805001ca4200300030901d18403402080030040c0204c4040795208544540c3c10308244808c60380c2d4066000c1c0c00c1e50b400a00106100c2049804041e618080d908120001c02c7c0c1c8441c461b09d040c0070407000008a030b1100c80c1c006043c2d080840c0309020441124005d5421140e54401004098602d03101c0503282d0201921230010b02c100010b80c1145103141d0321142c4015900500e001e00740c1d00f40f240051144d40bc04a8403c1c0200c00001d008402181c0124261504041380000850405080c8030a000940050000c180e07150721050000200607520205030001800910102d152220720390300c18001a11615000340381406010300050215a54041c110f540c04000d520744200d864124402040c4820380f9500034904480300d180400c0009601546142d02076444542c0040c001c1e111150202d0b1a02c8841200307800103064402a0b0010a110b84040d200e20350300201429800ca559580d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 912233965 1250 912232715 912232751
    0xf030f030c0705041b0f120906020a0302030f06060c0c12030c0d120b041802040914010c2c030a080a050c0a031101050603120426030a03020417160e060103 68
    0xc0d901501d40e01480d400c0c402070510780544401c1400d051030580c1e45415056000e0125840f01c0e80280412202d10744c24841c0c81101d401000308160003001c115607034072050b900100a944221031100240d1000004580903081100840342404c900030003a101c1107007003400304610100b0307203401e4084510051007030040da0302051106000c004010348601c600c0004901c4403e042d1801e075140103208918001c2402c4e20070240b00410600a0750448000841141619003206010010003107141190300e418650324074030b0740081201c001c1c0703130398a08070100703000340d1407001b2985000656005404d5003118801000040c40d00700a444441c005040843c10510300035185450701c101b211043d800a501c84a20300341c2c151082c411207410480c142d020b130070642d2003030b050764883c1c0c8528440d06035521400140c00007041006010900c00c0b80c151002c0d2170761141d80d42d0001700030750010300408000c13882c000b030200c60003080040c1c10844403040b800c51000c4a881c200c1c0c105001078001b0865810300da00c4401e12516161591 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 912235215 1250 912233965 912233977
    0x607181811030901150e04031205090a050708010209240d020c070314070906080114011e030b130b01050d0506040803060a0b030907060e01020f210f030f160507020607020f030f03 78
    0x40c00001c01111700f84100c20001150340c89491411401001d12000c01d80c0880202001c000c0c120011840d078a03201c110710324000601002030401e0248542c0401c0c40c0d0810f400034014500101d03014150030cd8140341c03011312004210701b0141400700c1041a082104020f801410a200c443d0050302c600039507a882c1c1d20b0003054019500d104c0ba810074035050110010710300c200005004040020081d02c9100c144090099106005a5412044c01c86d0000ca82d0b8403c104032030040c5030700210515140c00c180c0b607021807404080c501141c40c0c002c00d40020519091001d41500302d42d810000800c076a4449807a8010b441e800a01215084001580b01094505c1d1080003940a03034104030049c004545810001020700440303200f2103045400803c1000c101000c00108410038451000500c02c81121500700e0071461b10404114040440300031080000d0040d400407814400d0f40c0000d0030768120580c02c0000c0b80c2e0b6105d4200006c0d8041030600556000d402e15000018803c8005800c550346070303590f5030740b6500d5900301c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 912236465 1250 912235215 912235231
    0x6060f0a1401050c150f0f040f02120115090605030f03030708040b04080d02070b04051005010501050409050a021b0709060f180507020724030b100906050c1002040611060718181103 79
    0x41c0140460310711403c11b09135000303100742e594007518145a90360070583c003a43d400280c440c140000641d10311100030360000036448555008440b200d07940e0604000540044e03c6070600c01e005d0506003902d0040c010040300d108940075503c04102da611503076448028038010700291111203061241c00d019884038030003804480e014144018041c6001c0c64480d18220340d00383c0019a06007001d0040106907007000690302034485454002c145a510042400002d005400182039025008016286034007000f240450945420034814403142d601c0e0046090040301c1c600c2003003005030304541011102c51007580629000007032841941c0855a80e0031094100140c9031412941800503a01c0707044803207405118503030701c4070400d8560107440c035000c11029001c03d62902c140e000b070180000d40fa00a8001c02e0118402c210b800c24011034840382c03694001050000c9200b40440c161080c1008100b81c1c0f40030360002c400b0420605a8481464107004400303035604032071744002c0040c903180c0010158808013803014511500c0d074 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 912237715 1250 912236465 912236503
    0xc03070b040c230f1c020a030b011e0501080c180312180406080d0e0d0b0c04030303112b06030f05011b050a0f180302030d0306060206060f0a1401050c 66
    0x91401051403a0030f803414454034080c01d011242c00c16225408440a1510202c0307000700054040985010341c4903041c40b00a600c5015110f01204000106c01c00354103030344040b800d0280868440c2241546001d080c0076590108440100094510a59400620710151440c20400404141d900400d18080041528101142022584001c03107103071003089510f00704044074140030312898074884079100d444003050070080046600003412180c40d07081428001c164000407040c11490040984070b9207030032501040b070009042c07049142403c01021b05441004000d9442c0b409400c1c01c11040c01e41d8014a00f4411081b60344690002000c100001c003c0340126001d440049003c142c02d8841040d228035101e00c00040c003005000c0711025640c0100c8405996906086c40005015a901c0231400f038012513000035850b114241c100b544140c1d054000d0401c803034854084540755100c08040241d2050040c2805422035002607040000e11441c3c40619212030040c14010700d820707040000f150400100283c11051810 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 912238965 1250 912237715 912237719
    0x804031b08070e06270a0f090213230903090907030506030319030e240a09200105070213020a090f0602150a060302030d02061006081e190e1b0306011401050c03070b040c 74
    0x203c0e1f010340080082d084404011044040d400211110110302000800660303603119206406803105000301d07a0403040c0040d150a2904000550b541e61020b030500e40aa406100404c50450007805404d020380b2004014504181082c0315129070700c00e42d054082c2c02c00d80c07140301c0310800d0032062103070300440540480c1146003050f606011011071100a000706001e540342c1900074000c5150f03481d10701030081c0701c0b01c1202601040c0780d004032158002c0181c082d5005c80865294400f0038034943c0184504502a281c200700c4036551805100040b18510440d0090b17081007400440f85094030404a510452900c0e0004069442c0d80200c1d00e0402541c14400260703010700144901c0e0a12070300311100401c901d10380111030b8039101c01045a40b0015100003015002e601c00031a0b03040041e1901810810388004007002080d41d290381c41c0e41e5650381c01d8201a41c103036202c04d0f01e82407400c2c0481c90754143c6d443d20200c01c60f1243d0680044442ea4000e001c450900e0000f4021200010b04004150740114001c1c42c6001c0118 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 912240215 1250 912238965 912238981
    0x1c0902180907030203011b050901050d091a040b090109380405030a1b050c10020a0f0803060a0b0f04050909030d0e010b0f0102190813120804031b08070e0627 69
    0x65907c00504058480000c050b4482541c0306044074030b1000207103042510303000d0903552000074041c1014010920040d510031018903034a0009598403540c0600c0d030040a0762145c0d80c0c500e007264541e40000d05000908400c040e060a0f25030351801c4011981017401d00b100c804500d030348600c210142e0b8112125040007450341c103495480303d00304590029522000c4204842c0760f80d180e903107480d4540414000d100320410301c000180240502201950400d044200500b0607160502c016441118841e101e04003000000c20300402c4a01907074200010201820701d0142003800304940a02d004100d881e071b91200300207040c815403040c0102c484000d0714030008120104030004001301e080b196090141190b01c404160a403030036010781c1030ba96550b0803c1c00190b5807402c2e00000c0416000642190711071400034903691080060410040c01164081c04008d102410b29050000000a49200710700700340d400b2034410b103c0c1404030b034005a000700d00180500109516040c80e1580c0f07040c084014464605d603401007000c08 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 912241465 1250 912240215 912240221
    0x1513050112060e0d080a09140d0e0103050a020406081902071407150e060d0e0f01230106050304050706030b0f040c0e030f03040810020304080f030408130801021c090218090703020301 80
    0x4451078409000c9842d042c4e9002401c04000903d8240081d0b02c900d0058140b201e8401e410380b41040d42ca0035940da0f003182c100041c1000210140321400230340703403c00240310b481c140d01c2620241c9a9a0b03803410b0180c1c07900c0c0072120100c0b80d000340c500112582000100005562410150803e030b034048007400045107003803410303400c0714400300d101420310200000c2c0154542d601001c48507188515031000500582d048400e518142c2c09021000d06580703402c0503140d03095845902e20300400c1140100d000d081c0e8884204850301d002c2500c00034980d03030100200380810341c002c0d0000344440b00b0150620520119000015040d610341001c00c9010404605031140c0b242418002c18240e2400f60300214680b074508001166107605500c2150211a4040041001c00c140761045900442801009503168201381c180401250f21400080d900d03d402e07244002507082c410700980d101100c9000c87c01e08504c84440d10b01d0081c00015030100d9014400003048907242c0301108409000d03400000080a0407800c6205250031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 912242715 1250 912241465 912241481
    0x90c0503010e0708040606031707200f01140d1407021c1b0213060b032a0d110702030d0e1207080a080a1404231008151305011206 57
    0x81000820040c0034601d840b101d615089a01850039480c04c4d511410300074014010740d00010002452440c0181e184090700d80a0500140243e0302d040000c00340200d0600103544100c20380c0d80141f94042c00d00619809503140c0d00340120424000c510341400d010000d41220f908a100018001148040c0003040c0d42c1044000d00c41c034641001d0045140071031102a01d240c03281c1414126011110040c2c40443d240c0390303903d11007001042070078441d036a2101c1401000760412103020000d000f8500d042c189451030f4000911039500915645407034501c3e440900c2014054190311030284080800100c401a01d04000c82ca44540145d40c0d502e070340c1031120040108031062a0800c106682c4121400d009081d00829a206207691016545950341034030b1100b6150004a11410030314064003080c0080c1c1910394010003051544082e6400441c40d10328000c004020101d401c18600040c0300c4000a46942400a42c85400c10b50007000200c001214542440a0b03072802d0700071301e65502480350310404001540c01441c074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 912243965 1250 912242715 912242717
    0x230c0c032b0b090c0307020304030506040b061c0b01090c0e10030b03070501210b12060907030b0c030f0a0e0c06040f030c0e010509040b0c090d03230a05070f0503130f090c 75
    0x10b000340500028103d08000c0d00c0440301150020118102034020000c550003143e10000303584c0c1514050400c02c80000b401c40340940106810701e8059542c526148040b203c5680c4210f0826090b401d10b40c250008180f0a0b1004040c0705442c41c484241b95211410340c0541d001c196008905c40d0790083c01c0c5410203200c0d900c40b40c18000d8200c01c0b205481e080c050b1000000c8450640010805150030005290640c1400c070002140581c006000000303201080c600300b520300600070750b0490b440f00d00c0340310030b00c2c401201c1142c119080e0501103800d0480c1500400c080358a0b02e02120740f52040b80c1c000400076846548954040e07880d03628208204480001d10400800d8a01036440c85980750030042910b00e08d00500081880e0201000180030400c1070043d00d0301030300081c3c032600d901d002c1c42c0740c007410010b80103150b06420100100d0034007000c0303c2c0d90b00322484179020b503a40d00c0c1002c030160b64005583c90310260484043c0810300090608600c03511003140180941ca5190a141c0e02e00780c2000221409001650 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 912245215 1250 912243965 912243971
    0x20705010b1909050613060b04080f12090d050a080a050a090906060c120302041d0a0f050106090b07020102030403080c0a1a13020d020f03120319230c0c032b 69
    0x104510700d102c0540c0c01103c403e00340204040c0e5130000000c041015115803401c08518140000c540340e517480000c2c00989429408a8101740084482540c1d60102840c0b1550118020000d40300141411b14010b04050f124400310b40c05205195140d41172908100e1030000018804603030ba80c0619400085503000b0700100000b040301d0b50a040300104001c07049c82d0b02401c40040c070040040503030b22031740c1114028400341c2c2e135610542144036030032008401c0903501c0039500d5041c50900a00b84010b48101c50494859882d8004030f83c3c030301a6906026084030310280c1c194002817000201146118000f80800140e0501800f500d81662130000000d9038030130f07141c06200250000704004070101c4201074810750b070112080e0075061210310014940c0881030649030740600a40101c0d40100811202860013820b0130039181c41400801c80c0844200c0d240602d0352400e08060020726008a994184447d400c00c0404880c40d2404640440c03040c65640303d0011b0342034281c202c403003000711103014480401030003c00031030034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 912246465 1250 912245215 912245239
    0x1b2423070e011103191e020309280311040b0603010801060f0b0408071a041203030b0915090109020304110a0602031911100b0102030c0706180b1e0304030c02060c01020705010b 77
    0x1d030349004441022000c500710080b810105c0d405004410700380d540000d141e460722215510025202c0d0441000f0398062035940c9c4252500e14650300000d00848034940f0241c000e1491516040c11541c68003c850360856a250490700e0030f41c481400550181a02c0c10000c00c0240ca001104001441c03294005101d60f0800d07c1700388103542001c42c030b000031107206480c1d410b540388902d00b00c1009403140c0e51161b1440906210310034100f640540000c41d441c40200d400c44d07029501c041e2044c1d9000318900013158001c2e02c050040c01003801c40d03805160458020704904042008440104440c1c21641d00160007590010484510410440414221605640c50094000103c2e000039a6440600c3d00c0d00e920300c55140c0e0440c05030b9910802c00d4402162001c811280300540d5541d025100c076041c1c0681041001e00d00c40007040d43c43c1003008450b0002c40104080c00ca0342c11102040255810141c011401c1014031201d620150ba03900002c1c00b80c290701d00e0001a5200118a0401d0031682980b1307406014003420425 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 912247715 1250 912246465 912246497
    0x1050f060708180117041109010f180504142b0c0f11130f0905070f03050c12011503030f081f0501031a060301060504061b2423070e01 59
    0x36a0340703c92425030415506016000140c501c02e82407a400000d22150504010901c103119007104034440c8180d40801c1c10381d0300c03800100d481d4070b2035002c2c20340c3c4000c0c80700300514a00361903807003144e029006043c2d8003464082600842d08101d0381001050303000c480c0325520010120040070711001600a41400d0022602990311554130f03884065001e010090403c1c0d00084a8a442800b0411140025010484071440c003011b40001d19036900c0588140c4500c1c4400700d1440106c010100503290860020620000030004201e40c40c11242c522035610f54a50800190302140f91320030070081d40c171a8035038801850702180000c085000052200844e1801b44890701004140041a0030070b42e5020720f40480c032040a85540c0020301001e0b240617401250000002550030b611501034401c1c1d92041c0e079102068101500212034440050034041e0111310001203007550220b04541241c680b10300c440000c603420041d0703007189164001314400000c11781c0c0c8400411625a0b408000d140003144d09080000500e508068 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 912248965 1250 912247715 912247717
    0xf0b13061d060a0210141e1e060d0807060606110303072c091801140906060f12060a050a2712140a02070305070f0819030909020f0301050f060708 64
    0x8156070082400183c000c1001d8800e000c0101e000060400c1031041c000032010104840030101d81100c940d001a03541a0501d601002659021300c54110300c8043e280c1250510404a101c003401d003981c86028001c100000814810252044c41d009020000780c0f20310349403025201c0307118444d81000341d4008200b00701c00180c00c011031280c02000c00755076071400703807602c0741581b80c9100790300030326901c0340317031641002964142c1c0140c0000c01c541c0c400080c014030740c4200c405910070100b45d83c041c5607500071400189250800d254030110b032060003006501e09040d000078a030700709442a29640c031241c1d02c5504104040443d07005107503060700800340814946040817042c114502d2000ca0092130b1080309914609401e201c5c09107070b2001e041c03446020342d988410074000303956800e41d44800c40d050700608000040b441e15204041c0200d480800240c0081042245600050405088100d06000f1018004201c038407961010f00402039180d06000d03980d504240070400e100107210b003600c1c071407941009000006604e02c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 912250215 1250 912248965 912249017
    0x22203030c1b0519050f06070317092b17070f050d021902031201080a150c020708030f0414100509090a0608060406020421170a03060f0b1306 62
    0x1070a051420301c1c00803a5030b801c030b80309580b140341c0c030403403103100680da00700305281d610111541120b644800c0000c8209102c0795008640e80134000c1040722147d803900d42100c5451644c400c05c0c0303c003518424001d1349000d01499011014075100100020031150006410806102002d18032012140359840c007040010004040d464510701040400302da604543e00040c2c043c1d4000749081c444040004060182c000e54079008041500c3c4c0c56600d901c000183c00c08085403041c142a000580d8504c05c8414145110240100e00309440c03c501c6000c0d400a54400144041c3c116618249003003a9154036000800e032602100e9022148154041030381c240145400c907003150307000c000030780d00b2a210340e450000800044c001a80300d41c405000c3c007401c00041040ea903000b0400d0314000c0d60310800030b8004007001000e0484404009140d050f880100443d07100610014008a02c243d180206266440b9082588468035a500c0402030440107d80c54400c88590f100903400341540d40b5124010003413120495010850507 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 912251465 1250 912250215 912250223
    0x516140d0303020405030d02030a090f0806040204050c090306071806020106080709110705030703030f110a0e0108150d20270406020f03160915021e0a0b010603022203030c 75
    0x21201600825000e030701a44d00408000f001d80300495000c0c00c010391a40d01c14199100095042030740419659540304046007a502950700400f0b09681d503a0a0000401028041c402080c3d400d00070312001e55420803490703102c0e113500c0d81c520300004015040304c2803101c80c039000102035904001081c071034140009808411070303c41d001c002c98224040320302a00c0d10b10900c1c01c060000d000c005042c20505405070882038454040d024200310f0b03600707003010401080c010039107041c00050441414003080c5d882003c003181c00040c82070700505803048000000d014000700400440e04051960000003804060f6941510800c3c0c0035110841040f50600d05080030a0902c803003000c0f09058100414244001541a200e0341000c8a0038580e032424482442106401c0b403424100c00105a4040030604c03a4031002207000e01001034009001543c0300107a09500410300d2500402e55115004900000c0303001441c1c501d00920054500603030718041c401d60034041000c54070b40c00300000c441c0d0408000003613011040c00002904 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 912252715 1250 912251465 912251479
    0x71a0a14130e0703150605040803070b180a150f0e06040f1a180f01150527070503240607080a0c020604090c03061a03160c0c0909051614 60
    0x4044440c0c4074400a811000302d2001110410011a0f0903500c5100d014111100714040c459490070100d4492259000e0216260001e00840000a02e15414117810220952a0304000204070281525080340000241c41e03048103688501d4010445100d0100c9000c200d00c410b008100301400800c2d56500054001420081498030380d10a0190200303001c40c50031a02045460a030a00075000c0c002c484040c50604040d0141600d41044000c05201c1c280d0864030484030140898a04400c100524228495403c1ca000c005514a260f0a510440b081d100e05403a0715485c1d16030400c0400e441c40140c180320072059a10340c100c0203841c240c0d83c0b202070b213419a9200c500700f40e4400006c0000c88140c00c0592000790000000f0401003184106500146440300055504020195455a815050061035100307000700c2034041001c105008811070a011801c015424a2100c403211b5598a400d2183c1a40c4030a05807036807805d010f003c001051209903110710501ca007030040c89040086e000312070080b5034402c03807140070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 912253965 1250 912252715 912252727
    0x1b090e180d12090204140a1407082a0a0512101202040902011806091503270f08030408040317070203070e0613060b040e060a06050d05180d02071a0a14 66
    0x100b076400c0340c01100d60241043c01010b2038902000120001036400c40c903540d0801c0d9080c900b4032454041f65100c0e1042c1c2d654245a5101d54541c5100300d070343c007181d88044060740d4070244541d031450340090020b12184e540c1c940d0b039881092062810140050410b460280ca01c3c20200090704040c800760400640448000408461a10069030450400140c10031400c54a6070005541600105da40c0c00b02c034400c0894051940503c0021000c89200c800b04460801d221800302600941c01000700c3c804c644100c2e0000c002c0051501d610105420440e4200c4810030300140610030060b40c40c01c280e030790f8104180e480d400c000c00c50b130000707485e07200324000c000b825008500007035100d50760101c505114210286003088895100c00c5c440210f40c0c03160080b03000c8000c002001c1052800e06132607940495803140d540e036081ca00d040b030010015040140564074000c20406000381011000e105800c00000c1c0da40061562603c3d0220402031020580d49195220400344603e0243c40d800c130742c00700660340c6640210faa0b01c42c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 912255215 1250 912253965 912253997
    0x51801060513241e0507140f0a061b0311031305011b05090a05060915030606040b0d05060109090b0d020d08161202060112030915031b090e180d 63
    0x10b84190700c8804070000c3c0e400318554180307846440d0810b54070749a0b24030008013141035003400a41410201040002d00c100b103040040342c81c40b03030031625801c03000301503e60803080b49100034a408158070003500c80980c0e48805004229070104142410003542c18140519200f28800f80010701000b441c5c03a03000034040d4560410018207510003065260100c3d501401641d80a00051544d0442a40c00e401088058400f0805182250a40e28a400010821401c0d400d00030400341440d00301a1031a90800d500f0700000c2149900d01c4e010380035010a02a000a442c940380b0001880c0d07030159400b01207601e20b4420011000d864000c0c1580c91a074050307541601004440c0f4046219200d000b0f001c500d101c13102d9100300c08020707a14080420701d030200c1c0d00b200c44c01e90b2100108403a6003000c4000401103142d01c04108000b00f029400b00c10f100c0c03401d040c0050450540340c40c5e41401e803400408100005c0c02000e09009d5070f0100800d480e00300c04681c0d414102802d03000034076030740c3d030f041c0382a008184a100c0d1381c08003002e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 912256465 1250 912255215 912255247
    0x32a040608010815150a0b2704091e1a16020d030902032503060f0527070504180501050109021e21130609030e18070c0318030804080a0c0518010605 65
    0x14203803814496940e50482c12002a400028401c1c90700d08c0d140e4480111803840e00b4019441c8035500107048900314880c10306c0b0f000450400c0c2408503056054031008d000f1201e02000741e0340c400d810468008000d030340e050344001e04010b43e4040b0041070614011b100c0d0096180043d2401e40071080c0204400302590781103a580340c1c860950700041200382410744100c030800319038120b14014400c034805800d40c0c0c5104280c015502c030f020300840d4103d40c04004100081c0c43c183c5c02c075008451050000d03030144600e50700ca160075039509030801582190000b449101c0c201340e0050b0420b1580300107148505022240070420001c010100035107245142d6800814005426804040d00c800e910000400022201e440c1c09441c407800343d41c09034480c0170f000d9241000c1c0e210285460740324150a603290410300b44966006d40c1c452030002140c5002c140650004400a9400401080607081010080c49001254135104081c01c80680005000d00c40013004658040d10840c2c1084c1503d20a0801680f40c91020080541c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 912257715 1250 912256465 912256469
    0xe090a0519062f0a1b050d08070c030c121b05010e0c0f09370b0405010b040803160302103b060c0903161508160212032a040608010815150a 61
    0x201412244244200300740003581f0201c4114580340c811141d81c0e0381c481612010040c01f80900440d12140c40400081d01e540004048584581040082107030340d25040c1d1440c80031460221003c2c1c0d5a08030156105c54100310604003000704a80c1c48103864500c5010881c00d40029201d4a003141039010b0b41800e482e0000c240b07070100c15070140d24090350002c2803501000f402840700007a008526000006c42d4102820048a00341c41e000c1c1c0085140076250943c461201022480035800c5001c3c2c10081d05c0240c0481c09040042e00907111025a140361001c1490000000e845044280c240602ca03598001e000200e83c442c3d101000070741d0151035041d0100400e0a0000345c0001018100c092200401d41607020350300c00c811100960354070091a600d204101030540f181c5202d18016034040000749450340004001140d01500149680f8011b10681000146200503100490301c2e6000109013485860382c0b203c200c5005020020040c010f800c9035080784049024003401d40c0e1402074114580903499284c00420b080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 912258965 1250 912257715 912257747
    0x10180506040b0f09030301030f080a0903020a180b190501140d020f04080c01020705060f070615060908160f0b0d140106020c030d05130e090a0519062f0a 67
    0x101e290620307050280d00021910055000205008203000c81e400109803411703250700045a4012152544414440f5005038080708100070720100040f00688030790f986000144400000303d2903440c80d01c04220151090115098029045c1e41d08040b078000d0030307039040c1c804c4400a0824402d0340d2080544c40c003c5200f10540d91540341d0000540206a0718440010405c480c04141920f242d501130710012610790f901489116400441030000a10500c10b100080c0001071003050001402000e0000d0365041e0010b0380d000c2004110140010400d00301c0a00003041c081401c0580b440380da0f401c1c141001120f6035207008810800b04013103207403041c0d1072040e40035100c142050440e020703666940d428001d40d9070864081031070003809030442030030080b8004d00c284d40313040e8040074000d00d4590500482400828004000304404d105943c00d4402081040c40080c403182030404203d80d042c2243d080482c03e45c0d0354101034900c08001a40b280d24507005c007140a8460003c407904c40f9a43d00f0207000308940450411030701c08 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 912260215 1250 912258965 912258973
    0xf12030f0703181502060a020d06090e01020717120406090609080c061f0b1206190e07090f062c0a0f030212151803070f14060108010e101805 62
    0x405050300100c1c0f0222052060004614554071070b00c1d10b1050300d000022030f6002d40d021202260040b000c640103812649907110700081d543d5070301c00180b0107442c21010304400c165400a001400e2000d61605007184440205010b03140141c07500600e03440306002040542865900d10700131080290710740201c800e0744d4004e0107568881250f0b405c0203071111020344003101e0682c0b0288031800000100b13200b550468840044a0f400c11a003049804040c03e030040103183d000d180c05800903d10389586034103074003a01c581100c1c81498540000098010805078000806e019034800040002e940c0c03205107040c4500324407100b814150108c6000158545052983e00d601000e850004580020341c50205c000b140c2c001c80f0307407541c0030160f01020b45e00c1e441d000f06510710f030340c1d403490000b50400d041c1da0421003501c0645089a14003d81c54603200e92107448044111140e40c40440140c480e0202000442d002d05001002003086040c401c49050b940c100050310054003d450303003c28410360710007001140403950880151 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 912261465 1250 912260215 912260227
    0x10b031b0711130c02070501020c010210050915040507060207060e10030c200c0f040c080f070207091b12061503091511070516120f24020c0c030a020f12030f 69
    0xf40081d121030f41ea45401449118000a02584001100b00b000d43c030680140c1901088100c3d0702000e045c0c0203211034060b110b0038081203021405184028441ca000743c0140c0440303418040000e04121883e8840f4003001911b4004804036500c241240807010703450309002035055400c00c2d050340ca080780d0301003024480c130544c2000b40c80c120700424a0b0081002c202c4012004441840401c170860740b8410360140058829800105c03000c62070000b40c0c1e000811401241e42e4296244004000d880c46d08480342d00c4400506503003207945400c0400b070f06400c00030f1041408250301300b0081d01e81804060424404254a911800e400e102c00d00300001c8840b100710009204004000441d0031f50b5501c0418201c8003841440c2400c0c01000140310b00c00c4c00d44204034403500068145843e0100e600b01d02603001e0f13a0a107203200000f11600c407040c2409281580051001d62234100c110581d500303200e80c50301c01c02c0c0617400084001005a4a8803481288100121a10140c1c1550b0394401c62640c050b400e01d25411038030002c0d103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 912262715 1250 912261465 912261499
    0x41b0b31030c060f080408090108060625030905030d080703020f041e0617010e070c1a1503011a0a09020c010e031c0c0e1e0f0307030b0906010b031b0711 67
    0x2402070f01c4079501da003000d280078107400b00e5042c2c03c2201c0280000b030b0305005002d000d6105024075034210500800f010301b0b09884010980d40f009000c2103511740c1070038490090040541040c44a8010f01080b40a032641c40e402d80b002910312038000b04408100740e03000032860b081280c400141e5001d1b0280131901521152070021840e034050f5240a6040441c244184183d40048a00e01e001c0c140da81d80704299040b5110003900b171ba14003c16540c1210a500520f40310114540d4440e1200d11501508888515400c07560f002d0608507001825023624203031658000030f00b41c0d260f400002c002c60b100d5000041c0d40310301034000f20b80108041002c240a50000040203120202d4012601e201c444041800f0040d85012050950380324891064050700210404e9240110500301e200700140c088016108803108102e00c80041e0400896401c2200c0031540c9200740140c0140420a141c058110045424070714208030307d211405004c0d20301c8100d1003400000300002003144500c880d070b4041001903c480c0c110414050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 912263965 1250 912262715 912262733
    0x63108071701060b04060e0d1514090c0a0b030a060e0112060f0c0e0405060d0231050403021f0e0703080702041a01080105041d0303090303041b0b3103 66
    0x7181c060315405251111062034818412202100d007400c1059141130301d009800d8594079a00100960701045d17007c0214042184020151400703044408001030b0303403031140703419040c90001800500699000c800b481c17076181c6519841c070080d46c00c0c1c00d8001e1b4903695050310240240c01141c2040348800e0310b500002030b8006032035402c40d40b40c40c424076041c0b0401620303806a204498260400c14000b0f10807060f00c3c9800d0809611854200301d02504410b080d0721180c0100341e2858000507070301c2c086100011081c000c502600384048148001100500241c20907450003555000d958100040c00808903400100454084c2d1000e00d41030144004d42c0c11650762800e04001c00c0e08000c030182d01550400001c211000c0140114201da10b00c144c54900e403a03400d04003800014081c525901c0c09149040300b400100c032a040005c0e510480740d544c02940d4030b00e4140340000f2003400b488040c0e03410002110003031010303807500070a5904e001500000c40b8210618445085142c2c0b407151526041c0928044d000310074000c0c180 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 912265215 1250 912263965 912263969
    0xb10020a03091a0d05330f0303030105060d0203060111010c09150516061805010f0605150301230a030f0501090b0c1303120e130e0c06030606310807 65
    0x41c0700c0210781a40c5002e082e80007a2041030404042d10308106103158444ca80c2d10a58100e4404805112005443c80a2003480c243c0f440c842c0d074005040010104051130300200b9402c1c0154154059819540f5141c089440b40c018100c8244640d0303008030014000340d2048913100a0f100b1660001d1112464001002d02402c84034001e24000540e2084010001809002101ca090401001d0150840304a4440303000500d041403a21194000303844403140492024080d42c26408188100055041d1034041000a00342c4e018116903d05070f03047c0010404545006924000f6040e480c005440444e994000507a0700301054100030000d0382990025014428154018202c0707500c0360410b41d001d525218510410760007009084483c2d001010000d100181c4030254254404000c0e00b0840d0791b001820002030001d200007541c1d03406686e5104c6178000041c4c0104826a0907a00980d5128a50704200d80850700c64450a214540f54490b00e003034140d8208a032000890704080d103140c040c0ca046440e5104240c64003214 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 912266465 1250 912265215 912265217
    0x5030105010f1718121c0615020d0c060f4203081c0c021f090b060907090b0a02070303030b0906100807020f031b100506220b10020a03 59
    0x20b080d20280305014010342c600c00903405020444035525110350014140410760210355601442e0388041c3c480782818003400056581c8428580c000054030707410000c591182d40902c00500601d26246216500440c1f4a54529603a103060715440110b41000d802522910074900146446c0c114406000300045110960486a00c9402d1801c01103044200c2d60f1090305a503440e0122505000400000350030b400102050401804964110004801c0480848035110080300240c0c00180d40e82da09840303103c15a05210b01562020040c0704c03016100c08254403401007500b0b01404050010541160007107404074003d1400c404c14507500c11580000a4a83c2018401280440d003000300d1900d2615018400b10b10802000d8100c08190400c040d00701c4d001600034100f0420760155031046500544280010810300313003c214024010820003947c0ca00d00758104048010310b82c03402e0b051000030365404008950590414000d604800c02c250011350040010341c40361075000d411051301001e101d4001c501d2010450203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 912267715 1250 912266465 912266477
    0x21c0201030b0409020f1912230d050a12020d1a0a08060105030c0f0d080d090c06080411041a090115090602190219050303030a050a060803070503071712070503010501 73
    0x60380d0305000130359420140c000d41c8000c84c1000000700c3e081801010b0205c0d0891a944000d1070f0380e841d1900340c0003c00c90420740d00d01c4500410300421658100306400d50262038070041540e00d060031401022401043d004008220020107000d610605640603603641e01e0300c10f04200319144280305220b44070034401c0505806940020030010715001e021400303504841024000d45210400001041345000c491949a640b1072404080040454002e0001c4c00d107042d6401c000082c0c546407404d048603070011590180040043c59000c12001985980382191580700c00ea40102d120142c585860302e554202040240e0132000d8203000150707820303500c240112071024a071180c680860725214102d07240d00041c16412910240d02c1d8044005080900d84034049035105004d0b2044541ca8800080c11540240c031003007034164580c01030040e4500d2a05c0392900401207200154941700d026503031039440f17004c0e1b41000760115844c1c68480c0481940380d001c5030449a0081201d01849c548aa00a801d40d002805100c2c00580303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 912268965 1250 912267715 912267731
    0xe010801083003190c0e060f030604021c2a020c04050a06231c08120603210304020f0909070b0d0e011d1005042f03030a020d02060a151a0403021c020103 67
    0x8010022451b09a202078503a13458808a507400c81c1c040e6001402e00c07034000d07600b00200c0400034080503ca88a0b41710407400460b90303005500040030a20300c4160450320900d10b50b0a88010349800080310149007806880100e003035618103031520000c24180d4005580321407820b1010f0600003403071020070001701e8215015154111808000d82d08506481d1005040d02c00410060000e4404031805541c8038400030129482c502c002000d800c021040070041c0101845c001c400d0004515162581c00004481901d0208541ca004285903550718054883c1c100f81090000c0c403c00c00d424a40c00018034154410024402e19004280e407815014900303000d100c80b40281389201100c40c1e100c0c0140743c000e03900600122000d081c003a180c4c4400707c0c2060a90b9a001030408614001030b1030910103005c4900c45a005014204c1c2d0b5468041c0c1031000c020440d40d042494115490b1481d030003030004006452501080340c06d8080740e6585090144103030741000e50300c50700da010480e00c600441155210058400c1c0e0381401111 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 912270215 1250 912268965 912268967
    0x10e0303101e050301060f080d0e131a030303090a051207120e01050d09060f11070b1302220c03060b090f13060e040506070e010801083003190c 63
    0x4041070300c440000110700c0c04200034012403680c40b598240011001101c0c910355400c0000d085601d281c3c40600b018100345000c002d00301c01840412200500d9080c03502c440d82c54480000ca141c207403d81e685c020103554081654000030124191007013500084c0c2140d41e00e04000c00500e40d51504800f08681900c5603c10807900c04468206130340a86500031100746499070001c40542c1e45030542c0c4030751410044144003030b4440b000b45004d405000c60043c200001c1e03440003c0c0186040d2511210124594201001301c4d40005045042e03da61002c4010800d8007071004610008001c130011180c060344400340c04046000a250540c40614162541d80b0100480b41c6e40b2010b0b5070b41030007068499640680140c0c00d5000c03d041039520700d120125101c01c0018041c3d21307034600041c4204161404c2d5501d40c400020410340e00e40061000030101000d0910700311540c50100c41c20364846086901d40c08035400c04062005e95142101e000207110402d80c40c5944a00c2d1254040e4022403903184010f6510341440786ca42000307 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 912271465 1250 912270215 912270217
    0xf0601120804052e09081903050306040b180406020a23120a020d020d0b0f0108010302090703091a041407050a1d09070f0612050a05010608040b1e01080d02010e03 71
    0x803a0380318007414149858401080f20f5105856403010305402c055a600c2070754001407506184202c981e8586529090604045514002c0c02c06100c0b801144848402800b03e40c1080c1130b0383d0300c0340d011a40400d5100f8a10007040c4014104540d1800e1380c08000b0500040001e240c0160209400660710744405010311400000640c0d00d8600c8200c540d0401c1124001c0000591403c070340c0500601000b41c0303001e040c2108503080742e10070804c807107e00307584405420003860540202c81d030151007460104c9a0b5419500002c11182c8003426803030030305983d0720309501001440012243c01000802c1c03880d82d145054100544000b981c0f1166044501503072002003002d00c0c4c2442144d007070f1041d00d800e2080c0c40d00e40784501501c145c0040e201c550f5034444d0400020750506041c075001302034901b96580d00c0301c505c4040301e8002070b1840901700b05010b5082c00014007449034440402a03000e6000b00f60300c0740b00d844604002c440d401941e4003c1c60003103111800841c4440000940303405610166008000201070b40041d2038603 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 912272715 1250 912271465 912271499
    0x140402090403050705011b05120901020f0f0a021f0e150f01060c0218010f050114090f0d020117010b25110d080c030c0a031b0c090e010e07080f0601 65
    0x2010803110301240c08680300e50084c00d90244150000207029a4190308030000e00040200d04000490000e1490f9030344000702c40c03282d04100008025400e182134031840340928040c20440f00b0940c070001c5890300c5014400c208042000b5903d00c091a01108114104000781c014109540d8840c07040c00082c80761604420102c0e032042c0341d460855040c80c0d0034400c0c2112a2000242e06a9001130070328040b00d00641d180401c3e60091001c00d40e010401c0340780c200054a032041c1d042d001509401c0600204000341c03142c1d00c12020054049401e070402c90000e2006071503035807010007203c00b07906802e00041408c85d10140104617454084c00c081012a419055020984144c00e2001b00a1400148454181d0400140c41e5440901c5500e00c241071080388004589180c0040e002e403003050384084580c905154010380c003c0e00750000c0021480385280c40703854100035000d0601c9500e10f150703501d082442e2620000e500c02405000008141c8503404c2d900d040083d544d00e880f00681900e406a200000348200c03540d01a910 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 912273965 1250 912272715 912272719
    0x106150e0d0206031503010218030606060429160605150d0c150c0209131106040e06010c020a080a0f1e0b0a0c051201150206010b040b0715060504020715140402 70
    0x1e4030026035800c0c0100c80e0400f420b4840c4003c0030146517001c5a40a00107003540748865913180900319640c10806142180c060001030055100304424044403401e01d610006c100d0760366001c030f40481162403041c40c031403040b1004468000c904c0174101c0c081003650f1300034070701411703043c1c509102c00c4040717000704144400101001011200401001c02040b4100801501170740c92600b0300c0d403940c11081e00071640c0350307008480983e442003070f1000c2a810001d00010420400c1e1054502a0915040c00004000400040c00d042d051010701d081e400119034036850303039030040d141d03500583d900c00d0218501805148040c2c68121665010310b0003205c900c0303012050441c95a600700c03107440c0464944c0740780c00005080100c0d8031000c012040008229191550120a00170410051400000c2c0c0105a00a040c0001030f0080031031440200420400d100408040ea5400c41c5c018a403d44a149100b4264000f080b43d40d00050300726001007002c1d0103004207d200103240c61080d081c02d00c031294a682c0c20f10f424201c1100c2c000c1d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 912275215 1250 912273965 912273979
    0x1201050406051c020d060612060e06130609210201270201020a0b0a090219060e0f09070509220501030c080708030d05060612011404061a0729090106150e 67
    0x3c0c03c100381c1c4501200e8942c00500049481030440d203074002541c0fa243c00c550b401d560007010400400c90148161042c0390440d5010341103a06200e0100d4000b00b080482c0030f8900ca440d800300c0b40c10b00000c0d01302c400b2207224240e1690812201610044e018100d240303030f141d8001c014441c140c00ea002c0c00f00d034444a0190305038003070b04900384550b481042c4d810000d03002c102025038030032130200140c5640403400512100d1480060081e480c2003001031401c0c06025100340141e1405049000984a2682c203603003089481c00c0081d284e15040d00410306003c0460b000d50014804440c455036100000d510140c1601d0040c04186000d1752100202c0c0d540340b00c2881000707800d500401403040101916030101e078214034010040c81c03400c1444100e40da03940c00282c2220f000c2420380f982840d01c0349840d00c2004024a45840e41d805c0c04120141d840402e4000e5540280101082e007100c01d004003080c2d640302942060303010120703a0707a0800206182c000e0610b400750105980107001c00030085405a401444080c100a20360 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 912276465 1250 912275215 912275239
    0x10140303160b0c040315050103110d050706201b030f150a020a030b031c03050a09020a0e04030512040b091618092f09061c06020a170408120105040605 66
    0x101c0c0c80041c00503c1946568000c1c0400b00c0001c0ea00c95000304200303c00b06001c24154110700300341843c0e12195403803500c149080003a503000168045812021616076003803801200260307001400c0008458a8500b80502800d0321158102046102100702083c00783c003121060815030020307039502c2d444807000980801d04a00010712243c0c00340c004008039440c914010603a0700390400401d00c2d08409099000d40c200080303d1507074141c2d5062107041c0d4011503155003800b521b03401d038010030b18002c25400b03426a0716540000040130f1500440451300249504802c000b40c1e8507081c00d004003098400d84a110081c000e4101c0030700340400b049890400d54400307562031010600340700004c1e002403202160403141c04c50200c4210116055086050889005080a90082e013400740c0410180400c002c00e020701c20346c0c44983e0000000a9100001d45207075002a00590f902e644010031b44610400101c8408021110740401c01000400e50142144070101d0454902c581d8035401040251074883c0507094000e4005208 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 912277715 1250 912276465 912276473
    0x51c140a02070c140607020a03150507020c011434030e0928240302010909050108060c030a0906020a050c1504151d030c0c0a080309150f0c061014030316 67
    0x135191600c400800052405a40344e0115484c2c406a5000390380074064503000011241e1035000300d50740040644003502142c0c49203000a0322412407003c25840c943d001280c05c1b1503000070585600801410a042031104003c04d144000941d5a031b428214009032480740d0078001070a29011090150300550120880c241440010401c01001c92214203d02c58848032103200828060710740d43c4143c01e00e120340c80300c41821400094040d0140f613100c0b650a0b843c060040107403150124400e41c1250b00c0700d5200b5075030380315107a0044c098212401c000d400b05200194011070345070004010114a02d09a080d40d4a1540e00502d488044070122005020303040800c2089414a0b6903a2243d40101003480303424801012190b580d030300d160001481580e403980b01c0200308025141c03414400c0010028000110f00c1e058207031300443c01e2105506e0702e81004100100e04d80110f0011001520000d65084d4100e801c82d1a0183c1c251007034592920032205200380da43c1e18441c0c3c0307080100842d00001000da02101e0001000e980d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 912278965 1250 912277715 912277739
    0x70b070b06040b01052701090e0f06092503020a08010b070b0705092701241d0a0905040f14070608160c0b09010905060105041a010f051c140a02070c 65
    0x10040c0c1008010400070590f04444840384c1141d1042000021b4802101000503000c0542600300c40507030440d100401c0f0112030001d03034490307010b102901c0744105612407028415462200c24034000409080e080003c0450b949a40a0b010844841d42c41040036641c0c1d448410481c4901d0740007528240102740050500381c001d000510012034050880b4044076109200c22015440c603441091481c60440010810076845001c000d0f808095184c008000602c8600013401d140c0c000880098000c00310155488036507280d105000062090315800d10a92501c0d14100400c143c00e00011101e2030b1212185030040100011100d003034803900c2c0c854601c1030301c83c4000030b46440d5603203015008102c07100320350b0400100d111070940d021f000ca45c80003150b50411450818100349050304641e004910f0084550040030350022813184ca0a02030034405000e080402c0d08481501c00e00b90300210340d4079a8034001900380c2955001c611440719181900e4402e803500143c5c4401e0f0301c60708074003400c500d84060382130210300c51102c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 912280215 1250 912278965 912278981
    0x80117030304020d111003021206010201020c072112080a0c0503010b090d05010b0301022106190b0a0905120c030f03030c03180106050d030c030f08060a06120b0301061502070b070b0604 81
    0x841204a1140c40170004246040c09000b90300025004588043d46601300c00c1942e400c91001d000039403c0c004590b401c0c580e9200140b0070245a845100d0036540203281c005c03070071000c245c0c10052600796200c0c0000301400c40003065921081880c40c20420810321445902030b01e050300d041c009903030b24140201c02040b01110f0b641c00151019540d1382e0f4415420740d0244000c2201050385100c44029242a103400800980004c0c2038034001c00803039441d070b240f5505400b01c031802c1e590640400380d22031b10b4010307007200d040405400498201c41d0304913148544a80020b00c00d07170700d00300481c211504116100303605500d034041a280001401020320104400094005401010810100001582c2035139203000074800c0d400d602054020844401c0e40c8010726620466828800b401e80c107200c9001e04003880890b407080401d01c2030708104110541c030000c503080150130507045941c00400a004107a21500171100b09601000340d0f0b009403148950003c0e98109400503100b003ea0002058421a5111410300020f40540 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 912281465 1250 912280215 912280223
    0x151806021903050d241d0106111507090810271505131101020a020330070b070e030f12030a06030b19050702031c090201050403170307080117030304020d 67
    0x40c05080e01d0f0303008611640304240c0000c50a040705540c104240841904c1e590021001c0c0251058501d06d826842c0202034119611840d00200111586101604003004008680c007205200320510050641c08840d20b001e40341c2e10300070b8a0802d4029200a001c6443d1227906480c45010b40c401d26000c00b035101c80041c00e2600940228010189003030003107040351400c40344800000c040d0070200c400d00517a10241d1112b00c0c1c0c2070001b055002503d400190f60742004500140342d501000c41da80c84420924541c0d412440c0e94140f10716100c0e41286040c032001d540403945440081e400004252540c81d00240400c0540003207005400c2609a42a043c615903000510b103901d07517030302c5180000c0040e64000d041c40c4504c80c00342c0d035600212034020701c084c140c031006040b07001154401d01274070030310354000a0b800c4c80c85e803130320500002c994141d4401600c41d40629400a0711080f02c4001070800e00326104001d500c00c070280c1c3d44030140d582c0c841100e00d1f480324000031140c58541c4148002401400d0080d808400c01d405 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 912282715 1250 912281465 912281467
    0x15040503040b0309060a0c052a100e010518012a020118080c01050901113712110406050a05090d150606080a06120201050307140415180602190305 64
    0xb00c0140203440d51040e1540009580950108581c0140c14410b00004901e0392900b140307016008495504884101140018444a8040b1011013a04100b109019140e68140240074000b445201d040c02410b045a64041c2e6081d415043e124030001807041e0314001d0310b114030085281107488150004032000d0b001c2041550f50701c0c1740482100d181020390032001841842440e580301c4401030441e081d2500900309000076818062065140c0080b0030035200260001c1c0c0c01480700c00020301c4103c0d401191260a21828080c0e59201400541d002d02e034503840255908040c0f01462406864120600c142d1241d1000200c0078842c1d0a00b191042d0700520340c998009100e1303a01055640c860780b4549034035124400c001c40c0c1d504010803c980d041100c01e90302440302e00040252030315000c21035288032401c000c02410010000009807100c0d003d140c2000d00c078616100e1840d112900c4000f400b5040c20101c80e14004a0856205402200c0240c420107050b150300d640904180740b080100041540c1032440308500340f080c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 912283965 1250 912282715 912282719
    0x12120705090415180509030a03020d110310170a211e020609010f0203010b0f0a17010803180f03100e0f0f0d030e12030609040212030304060606030e030c1504050304 72
    0x19440c090001d00a04580c80c030400f5514040c050300851102400400e0158181020407040700c3d0007000341c685121443c100135990306c1c000c0c04031000400c0198000c01c030300d0380044180300d00e038110381006400352003462100540140207201e11a9869a140200502e030f480080c07600010003009940103160050740e828045003800c4000c5147e01401804580c0400591101f003c000c9030380024000c0081c0340c08052002c51031541803020381c5545210704494001c96040c0000e82008085c81111151411800340e4007140c45175031500d1540f9100d900845002c940c0f000d49130010803642c502003611450101006000b021460400b00e021000f602c069200d00e40d142c010004030000020701403080203a8243d62002400c132031412140c0160807140c007134810700c1880d40016109940c0c81c1e00c400480e900f0400c00c503003195140e69070f0f200186081142c4001c444140c040401130008101840d002403058404070788051103000d0098440c0c0f0350301d00681100703c0240d48000c0503410000900ba04c10f40d00680601c05032480d01d6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 912285215 1250 912283965 912283969
    0x1d0c0f04090b090a02010815090a11040806012403050705070f03050c0a1506080609151b0403030509010305060f0a0b071a04030c03090807030308011503060f0f0509091212070509 78
    0x34100300c0300381041c4d03009103000a08642e4094034159101002100e0083d08440350390215104a20042c22818695541c2d5500040c00c000e013025200141503200868044e5070b101d81010411a40b06080c4040007030300714075a413000342c5c003d024042c41001255117850400c0c003191a00e0300c0f0848030140170b80512204010090784500180040607080740113451040140000b444d81804480e0b1036403100d45d40d4cc00034003c5c4401c0172400303d0701ca04192003001400c0a1902c2d6041056a01001c40d100300741c2441c40028000308058122003d41040e18003603c00f0006642e404041c001c0706490107c5590f03100300f4002043c042d030f02444010704182409000b5004030038494a407800ea4100058030190081404070051104060b4800081e401800118019000180c50342d540500314a4060191011400d000071001c46101c0c03080d4071282c0180003044a0000c12a6110591090707007241c1d026040c01441d1100025500d2500000e103070009824409419152800300d02e200e6416040c0a04003404004082009110369 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 912286465 1250 912285215 912285233
    0x15150a0807060c0b0f09120c07050d0605010602010506010c03090611012301031707030507061d1f0b040207050d050310080d0201020a030b091308031b13091d0c0f0409 73
    0x908103580398585100f8481c2444100c420f0020a103021891481c0c007004400c803000305181c8803846041082d65160f1008105040c1001006d40106410000d81c441d800300748103168000038100c60054000700480e80b100401143c00811825014000c02d500c40c104001a0344142c0c07606032200086c500016406003080124052000343d800c030021030b280e03504014005d2003c005580450000c200420782d203096915078000c2c2803405100c02c00f5102c0d41d41e60a481e09408420884e280e40099000c00303449007032002e4038001e41c580e500103582d800e043d4031703056645580f4200740c82154003840d0042c0c010660104106400c4402d980014210080d03040300c004001101a000c2003031541c44da44640000d03032a00e1725541c2c01400c5501030072250344101c07003e609100c4030880faa40200c03001078010b41e04507940c3e902ea1501296001105480310082c050001e4441610207000c00d101d016648682000c0c08507003403c8072041c02e1010004070345511070300b06035080c103000d242807000f8009960001c3c1021a000752562100c1d008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 912287715 1250 912286465 912286469
    0x60c0c0c040203150f0307031703131a0a0516080114031c0c11090c12040204020f070c08100e060a0b01030b06030c07020405060405071403130b01080f070815150a0807 73
    0x4000b01c01c01c0100b05a24180382c0d0301107105c00039401000d005195444d0180807076141088190a11070000128002c00e54004502c020303180c01c41e003a108480040e4003a504101011640659030074036080209070700701c03003410720401c43d2107469503a8051642403050000c1c1c02119402c24a50605c2850300307034950700d4a00480c03284e000b0b40301d407903034007200c001418412140750031680054441c0809804005d41c1d0441c560a0354011311600b210200d1603580c07840803c2c001d20ad40e5000321800000030074090b007000351440e00901610a1001943c842e009040c1c04201034030340603168200d0541003d000101c069201d548000e40441c0145002310780c0315407171008a002540700ba981000c00c50030000300d040650510380180c40e0402d0090b10204980d1401d441c000340645240541a0740742400000850200300786d041d005070300e454101c41142603550b56030286960b0307030030b103082092614002c9540008052101059000c3c4845a00b12004440d41e00c2c003040c000881d54000203581d0295511001007400c94080100c400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 912288965 1250 912287715 912287731
    0xf09010e2704050d020d200a0602040f0f0918030c0c030b01030305220b04091a090a0221010f05060702040e010f020c0c06070804050f060706050901021c0c02060c0c0c040203 76
    0x80e0310306060800500f058104c080d9441954800c0d00c0850100d680700300c201213551090f0041c0307010318164903000750400341a400050041400810003051030390001c2a4201200c1c50f00d041011185d17900e2216106a0360020507034002140104c030300741c001c40d010b01c1e0290f18552003900700c60f03015512965142410803080c0c2041e800114040760900b5203084200d100042e0001031144041c50a1800752010b0381403081d030003031201694903480300311600c0d04407110704181d00c40000d1814520749445d070300400080d040103065020403000c0c0c0381c41d90072070044419014180c81d107544000010505010a010041d4010801260026a28500200082030a2086d103c40320b286100250b0b490070210029890b203040d900d8041d200728020840c01000401c00412981181c80a9075038000caa00c48400041c040e02070b201d0701500c058240710804c00e4002045d4010400140d0400280481804c0756000c18110740c0b40a4800c03000d80d0005000c40c001c48081d0b009095070787d41c42011180d001c9800000304090340c0065500d80 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 912290215 1250 912288965 912289039
    0x40609020a06020604050601060e0301090204060e04060b0901080307020105030601110d1d0105180904050309190911070f060902040e070e04060609020a090314070e0c1e0f09010e 78
    0x452900784101001461648014100c5052580315291102010b114002c14408596500000e58600303400c10960703c3e40043c420050580e55001c07814141d02e084400304d42451503c101502e080c41c3c41c5801c40d041e24503c070300850401001d0b60042d500d96102034881414030420a0002070001070810610001d810302e40ea520000544101e601e5503241c0c4d5492920341480000d000c055880d00b072124200401510840303030180c00b1345507401e04509610425129580198448501c0f517502c0003254207000894500c110208560740d01c481031061240101c0800818200c1c4688451010075020340140780a140018000184485281d40315464111b8550100b00305440f03000030001480910302c00e2000402034044294501018400e004054024034000108040c4a4145948014030f00b046820301800d411804010b040c00c140c0018109600700e1070172642c4192035403203c0c016809000703090f904120180d01142e801e0518a800548080020a00c1e05410003030f091014005c81624442400c40950030705003071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 912291465 1250 912290215 912290231
    0xd0f05090f010e010c1b08070503041d07090e070c0c05040e1e01020c0d0c060e010c0903060e010605060a030f3b150414010e06070210060f1d1e0406 65
    0x1242502c82c071800007600b0f039140000340c984854200a500b2060641c102d4020748180b140d07e4a01c1850150143c00b8005120108010503600000148182075103c1e80001014560b100312003113a441203540200c132042001900411480da024024146540e88594250801581c0325008581107643c6088031220641c4200080d080e0301940342d43d1848400c0c455030082d49441c101c03d1065943d0080318204000300044c40301e1306002d0102d07a50000c43c01c03d200100901c8899000e440c003c00031030983c00107440359407620000d6240391105100319412640c0c0940910304142400c0c50075001002911850070380c0756143d40b803800d1401201308164041c03d107011307070131030f0a40f000c8039501c84030722244041900c2580c800d03000000c031070202d00c103d182d02a90208902c414400d0400c880382c094080710103451582c1c840d806c10312492076008158628281e007900402c01a0f15500d041411f405c1c03800e841400c4443e07110700c051200701c9801150321340d40880420402030399268408a0300c05480011901540c2840d40d954030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 912292715 1250 912291465 912291493
    0xe101505040c090e0609091f05010e060103020a1202090d1407063207030e040e0a1205090d06020703170406020c0d0c080307080601090f091d0d0210020d0f0509 70
    0x700c1010048500c0c1554503d4140341c4040400403015100c2131041080c44e00140d0700170b4080100070306841e16000701c09458052400c0c208042c12080c02840721045030b043c00103410354840d209071907103500ea0313580c0c4020a42c83d003c070204c000e6010034841600b2000c600c4d102408160215000018840c40b08024100d561418000030580341d0310b000704240700261400048402c2d044440d01c80d41424801100c180e07a82003618055850780d483c410456081801c0c1200c8601d400310108440b11000e000d18100242841c24000481b078502c1503a0300c61782d11159488071000410700650140000c0b610a08000039400302030740300b244c1003040c201c0e0b003181c21640028001c80144400c2c05103d0148000303003004d00982d62565203207c0b55001c000d20442c02c00201c0701c0060072680c41703046080f009040810309089400e45480c1d240000c1c0010b0600c040c41502c0002c040854030700300060400d007210381a4007400b1020540c0104070007950012003e848859210080058480803c0c411940610141c030000c01c0c2c000d54503e4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 912293965 1250 912292715 912292721
    0x1209050309130c0c0b060d120804110306091e0102040f1203030b06040f0506130e161106061c0620040503060609100b09031c0206010608010b0a020307060e10150504 72
    0x148400807800c0407145803000b908100104d143e154458085025540e40401003582e180010350043c0c004007580700200c00064201142e503020b54029855807448141807824183d171100f040d0b646003150f81c84550004241300b0584410b40e0340411800c0094909641c90b002c2e05400007054110841291030441c010007016014030618280c40e1064030132a051a00d08900388014204a100e8980640b0000550061224180c1e5100c8007410310000048002e080c50f40c26800c56141e02c148400205407030103021121000b00003003142c400c0000034800c84d040c070000340000703002c160764050840303940d80c448400c01044120480c2912400c0d1f03582e45000e85541c906010503140c1240503007000d00440c8490240521840074101141c2501c02881030959103010950104c4e00c0c05480c00b60300480b00c240d54400030312540d40400c1290485001d035076145207690300c5510607040d51281240708800750740304011a8000034815000a6002506041900c060440f400c1c0d0035030aa4190214005004e074401c4002d0110780343c184 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 912295215 1250 912293965 912293989
    0x100515070f0c0314060a11040b07060f090c0906140306060411130602162102060a020304050a030f020a0e01210c03050607020715020d17040204020721080a0911010f1209050309 77
    0x18041c1f002c6c0000840100040c4075071300480740030200001d0280148061031300038907034a00d01500104031951090a10401e802c443d4002c0a5181b810b0080002d1864807812500c2d1105000030080c12281e1141420400100190385032010306110a000e807540254000b289074004101c65006000110780213010f0f8808101303150042201c60300e0544404209052046541c6485981908c03525500e2078807a200342e2542c001c1d0380c880e9a2002e4180004000c00c01e480300504000741c07003aa60303402c07107a882d8245840400400d00442d004851809011041660300043d0011128091598045041d84a842d40e41c10100102c480101590100408118070700c0e01d180154406400c1d48090310407400c41c07240017000d11a2207040692900d13130a0300031034295955130741151603007903001004070321100407510184150451411628045090040047e12300a010b00980302415800201c00c0f400a02100c015107540c81c14070200301c01c000141d04500004079013841400d401c58021002161101050310412164001d05 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 912296465 1250 912295215 912295231
    0xe010e06270604270b1f2d180f1103010b1c0c09030206032205150f0f06130e010e01060f120201051e070c031109100515070f0c031406 59
    0x50250340c4109240c1c07040c0c42a14582c08610b198680c0c40d01c4d00e5061108000c100340701b120001030300c0c0005841c110b141d452001200c611055984e808584070000841c0240c500c914026030b074540954240b000b91542c40841c0b5002034610005144a050360300c0803094000360445101c11a0015940341034104d01e2010a00000c80314905000f84220500001c0001c46a484003d00540c0048045201d1080304c2c03079015111004024851500078043c100307180e6a082441e03401d220027a0000214040700c1c0e2209856106251100c2910020f443d20b400b84400b54003100c0104183e196a00700c240d0701f141c1c1c05e0290f00101d03260000041211418140c03103040b080d059900030500f4003690080400140d03040f80541e1501c0c140c40355043e000c070384021810b12040c401ca15008080410a2030301100f000021010b20302c0b07030382e03040ea07580107140e56103813100c40301c0d1020780a8268030401d44c00360510a00345503001003001ca44164a55960720381035a880640e114090307007080388e541ca5680002590014100300c001d900c0007030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 912297715 1250 912296465 912296501
    0x5010506090d050309030f03040e011a04140301090510060f08010b100e0102070b0d02190e011e03200306041116060c0e03150708060a0e010e06270604 66
    0x24080014105114009646008040009411052040501c01d40c0d0348081c000c0d042d03545006042c0c04c1180c41c2e034414000c0b80000c0c80c05000110301741b40c403c3d0501032091100850680340504042d04c240300103144a040961540d00d40d989000018000c5c8102c0a04001201b4007250044c14581241d000f000d6941000d0f11076131601d0003580d03817642c1c0c0013448448800c580c206031049030f60310300040f0304006164001d042c0e804000103040d1269030342907000381f0500500c88404151400300403070403541038081812250000d10b01c43d240887c58000509a414051018100020340391000c0f6280320060310004001403d0020100400400e410b0a01500c038000b06200002490f21030a40403d142d141098031014000c0350340d070001580c4e1140a40c800c0000400c0080440c0c104268080340020000001c446041c0040d45100205606003802200101501d9222002d50810380c01d0029003c0340600c001c20403a4030060074242091103842552090034845c07506206060649409801e100540d81c50442c18201c3c0a030b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 912298965 1250 912297715 912297719
    0x1c0f0302130302090901090f030e011d011e0504150e040c020a02061e0405040e0a05010c111509070b070506010306140f0103032f07030b010504050709050123070f150501 74
    0x1041d03414120590b0340c11151aa40c80e01c5801c1c400340103188151004045040d40101507080c503800a6a00040041c02d98038030450b42e6a040c94609400d0486415a0105060f08011420701c5507002e110003440ca200e1400c1c2e4106640c4480d81460000d1454450703000c07c0c3e000c44c49001600301f9000d440000daa80b400140710040c16507022418510800a0800003103a00c00030b00b282540c0504211001000014800e000854901151030b80711400000304440540c030b080d02c0d280b0b1a9000e804440308030081e10300905203a040101e5588440c4100414186590013007060101e81240941c0c050a06a80110001c2a0070f605510340241190520428010540070748810417001205a00340f00e41034903030603d820313003a490040c541c40b03c7c103081001542403400c80004144c09a0f110024441080b20b016525400d1039998a0301070001f00d0380181d031150700140c0701107410f00140d405034000030108141e022402e840d00016a01002860700322200c2190005082c911040a000b2041401042031030741c90010080b0354 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 912300215 1250 912298965 912298987
    0x4050c030d1206080102190f020f07180b0411030601030b0d0c0e0714040b0708090d0b04110f0111030d18060905010c0e0f010f120f0905030903150405060712020c1c0f0302 75
    0x1f1003001c000c6020011005100e001c1a8030a000000312004c41404880c0300c10b459603401410040002007000e1045c2ca440c901c200b1a00c2c1901901c1c2c981110400c2541c6540c855900442c003412504400a0b040030070280104002021004080c0040c8100d001402890600d0000244094113030038203041114020b02080c40011150412142000e600003e016910041d60340030a003100404400944840780f00410007007844203040301031036620421240e00705e02104a030010b41e0a08451380380c2201c55441480300318030000301903105402c03518110617030b121201240c1c2e170342c00700b516441001114140d4541f078061180030b030051581600118100c84030380d90794030440002000d40c4012680351f400c010509031030405440e125800b441c1c50845100d0b0500080119040281d0b599200d103201500910030114440c264204401e07489024a42c0203000d032001e51941d403400c03517001c02010500e0058a42c02c002c26120300034200525200d080850710780c2050382e4080c4001078207401c0e04400d014240740c0104081c040381 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 912301465 1250 912300215 912300247
    0x71e080409050411120d0e030712080a0219080d060605090d111504120b130506280c0f020d050421080f21011e0e04050c030d1206080102 60
    0x144a10150000c2c080d9030314103150301074004100d005a00414140b503808040c0e02c001c80d01d030007060b420f81c95804204040304281556200719114541031090900442c03000101c030003000b050084018412611070700640e0251000018050904803892500021030401083c0d80d40507803c000d2801b41011410082100041030191011007001403d490500c0b0440c0c15079079405c0c21502c01c031b50000310b00c0e42d1200d40f01c501c0e910414110300c405440d5400c0e0040052129203107052001060740d8010041d11003500e17500040181030807240c1d00c401c0c40d08110140e07e035020b145441541c07282901a5607110201d92811006070800074108503140401508000600c02c081c1c0310b81c0b120072000000e0a51b0941c1068030b0070701b0006400b95924000103080d00164210802d0356003400012619180750b00d80900340d996560018030440c105040b00030000811104020064020440940c080c0c010800d0f6034007000107800107420150100003120100e1030640445403041440d00ca80409041d0b06402140b414084013406020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 912302715 1250 912301465 912301469
    0x90c07020607230d08090f0a08070c180203040b130b130201050409020310080712050705060d0e1614012f070905251d1507021302071e0804 61
    0x164400145101082000f84904052500b030f400b58030f60340d2881c06400ea031501c450300c0c2000700060f00403001c510340782d030041204503680c031440c801131000da13415503690000d607017003d401541c440741090000207424a010175000310140110400607902e103000e05d0041030080e005032030501b03058141100c80b4000380044112541060743c803191020088140d00c0101e8441c4a039030080b0306107a001100380403c1e25107003600c030f0054840190035291410b4440e000702484817030400700580307103038003e24003080542411030040c040030306d5003170000c1001a03000b26000e2034041c0790517000891311003807481048400242401c1039040c4c00709182403405031b007231042c0220064200e40980500795610650080c081902001100000d05072070509108514003004103c9001c10b001a00310f00004540188002e05480788560071006980c0f14488008084494240300b040c1207072180d0074460000c10400100966102d004c0704800a0305d10901507610542460864901408403003052044e003140c20304000011011420707102 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 912303965 1250 912302715 912302719
    0xf03060b090f0418050102120f0112120f050409090b01080618030301090506060702120105060f040c051b0304090212040c0b0a02030703080c1905070209090607021e0a02060a0914090c0702 82
    0x107111300b0f104101c0c6500c1d0030141c0b0000d10300d41c8001403040c02c0d441c07807020443c801c00c0c1c1d1010011740343ea40d07000042040c006071603000b8003440a0449030080700d4007a072003407810602c03649007550910761a08084c0d002c0b201101e0042c2c60f00d03001500104100300c4100910b55000e031856504000c411208220301c2da581c001801402c900d1511030001a503a03403501c000b51148940c00524000b19080360a103418003e280568455000300450b800c13149880c1407a0080440080b1959100ca150010a2085002003d035640e0341c00e0160000b00000100020140003600c0c80031882c803841c06150905140000502445a1010307201c80b40900c10401c0c12a0088117481c0019014184001980c0c2c80417001900d5100311000000c03030140e04400d11003102c4e800800703450403034803e0b01d0454940d12900313035080d80c4810845917000140e00039410b905035111041c440d0035424200d041150702112056000401d1604003030030102c001091090b041000c1070000c04446840702c2c00352281082c904001002404070f00c50000c001e4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 912305215 1250 912303965 912303971
    0x15060e0112200409050105011b02040b130203091b0d0b0c0714010204090c110f0d0c0c0e250513060302090d05010501031b050406050607020103090c0e070f03060b090f04 74
    0x5010880582040c903000c010003181c5402c115036540c89030b96a0700180a1050030718545000442c0300e5020f841901846c4c940c0344c01003115040b003582048058407a0000280d000b0001c04546106885a40087d500070900840a0302c003c01010130f14644910f644403d00d4481c160b02d440c408085036000480503006025541d0050341c8806900707040711003600c0000c041ca01d640c03000800040d960100d90100749440030f42c1d950002560b81149480b0b07681c2c501d41c20314612070b40141b42c844401500450504072914400c06020b129140c0e6180b01d0f20462a003100c040340d4400d0040c01201c04003600140500c03100300d06003000c07800c1c140982c0c030f000f5a022070707409141c05150703002560440350350303521503221611980030b0024462581c40385000809450146485014146000f01c003040518250158509680024122a0610344540c00440151031448000c2e9803d16402101091200b4400e03c0c1c24030400064a034030b0340b041d152440c02000c546846d884030761040c070305003e141925a901c40d04101d800340304039004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 912306465 1250 912305215 912305237
    0x180d0305060f090f01170a1a060a05120d030203090a06060e07020708030a051213061a04050108012013150c051e060601030c020c0301090b01090c051c0203041a1915060e01 75
    0x62440e1541e07407d4080c01046248850034148602090030030300ca440c00b6a6105800d40c4d03201c040c44a007885155210410350842000078030300b40e1203a4043e40c0d001c13066400311420700009850b0401155401d82103010a22a07840c10442c400d50104500030042404c10011813421002c0e15005180c0c3c007503540392142060b602e2000c42d02385001200d5001e080350300424104403a500307181101040c2c060344a44980154245800091403041c184285031150205400150b4102072041940c006503120086502000142d04404102070b03003150f500100da0b40060301d500380305050a05000e40382044400038090303246502038000c00240c0d00030910f10b80040b020700b00880c241d07012007000d0b030409802034120f58140d8a8480b02e40305111616040754102d0f004903804000000c04920b0032541c5102d1111039070a525200201b015840046500469006010300c3c0c411103a9002e015441d0301640064400e250080d405007101c2e50078113410700c40c0c0741c24850b180e040d0000441c82c1c4100a00130b00d140c400c4045c14480c00e00c40c6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 912307715 1250 912306465 912306509
    0x1203090305120a0209011413060302090402131502120a09030b09010908190e040501030f0201050f0c1903020607080114120c040c0306061404140603180d0305060f090f01 74
    0xa4480c40b54002903100720302d150096100000350804080b03180007a074508034145030340000384201e070103040d40302458492190a140095000c1d5112803803164110b6402c00202101d0940c0c0301c03804016007030110004100c4e100c40403000f458034446448000c2d80c45000c1204924103908003000340102d9500110319050396680008280c01080d00340390181020400241103070700c003124202181c2c0142040d0312a01c0c02e00c0441d00520080315001d0000a210000c145c001c41c000d903003e580506244c40c0c010000074509680c03402404c2c00c242e00e49403540b10044180040504244c3c05015003a4032003441e14240c0383c5589042c2c05a0380041180e010140144445048450f4001d4140424a04c1c5d100c050b2044c40903094408004004111503c55000000d0742c00e090030202100703038400c803401c03542c022400c000784c0340f4402d0030015143d2000c0d20040341600d07d154554101807051043e40100d403820b481c00241403401ca420b000e2041c80c0342807460b2185041d5030802c252402040c04082c191900001c00886203004480 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 912308965 1250 912307715 912307717
    0x180504081b0c10080f0c1e0d0204170312010e0a0920090108151501050d0510030b0a11342f01020d181e0f0608041203090305 55
    0x251001e203540c44402040c4055a0001d03401205030000e0b982c81000c4401c0042c21160713a90705452010b01d040c2c60314081005012000302901c20000d00002110250782da400381c01007541c0c010900d0746c8100b40c02040070802485074452a03c1205d0824015500c0d02c04005242101c00a0500481c2030394034400e030205004001c564400344900d944040100c0780d1915990700807480813101d642c00c601c2401c50a0011031720400104e0110304c3c11004030403080050303c405d9102d07400411090001e604006040c001ca010b000c0341801424000c10b0540e2203600c0a43c21401c106044650050031028040e00b040081035607880c1d0201125603900b03441c440001c07454400070031110501c0040c280c010301d426185030641e0501c0388a0b0251402650b0001c01060340d00c3c0e0818900d544280e00e112600d0160f0012180c00e00640d000300101c0c0d00d00c958003c00c5c030220b0ba840300c04207a041c40306054000b0540d40d074010140b02c0608034454080c05028030b402e18018a14140e42d420301c1d5403501c011203004040c0c40e01d065804240c00350b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 912310215 1250 912308965 912308977
    0x30807120207062c120903100c030207060f0b0d0b09010902030717150708040b0a0b030102043f080d0b0d060e011b050a030c0e040e0f060106050418050408 68
    0x40302075540d40071600b4164054440e402d540d01e0010030414500d02102c85401440c11a01c100d440500407546100e5504071070341d082115100c0e01801403400400c5e59002034814241c201030341e03450058840c4503604102c005c64205200f88000d09103000f030004503039a1540e03074448a4951145c011700107030781c942030f80ca4054818400000e415115085011889505048060b82e52001341e0013110020341180340b110003080b038240c44c3c05010840a8000c607010800c01010725901002e14a004030b00c028804000c01c0c02c9134060b90284d0540101000340000c450810001e600b9000007000c011030503c150f40f20402004e1000600061031840d00180042e01443d65412600040700000d00011404071141000805000c020361076000551038001c11410b401100c900000400842e0340d9103904041007102c041d0300400b44000e152060041e059005110740d41c903405900746552038000a070800441c011305452030140103800c03010034040240000c0c4201e14002d040c0d00c423022211440803483e511a030411082d948220 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 912311465 1250 912310215 912310247
    0x417100908070b0a05040f08030717040305090a0b1309020913020a0e040e06041a1324060e04030c020409081204050705030d0c050714150a08090105060d02010507030807 74
    0x21508018481c401d005020494064145801c4035900e010021084981c211001000c0800481242000c00c408002643c0d01130f9141c11b04440701041901002039044007201c003100060303400506000f503401c3c180f04000090481040390750a151840c181160303440205d01402807000e50210b01e4041a17980c0401158211080388411913032940418402000c0c03404115469020b40d08050f01d20329050720000340f01e403240d50000c55241201c1102e40802000b620040e00c80d2019914508100001c9a81c600210300c5004010070780c00280701340c0406d00410b69242d5404030003c4041c038400c101c0031a4003c100a4100c0f541113400099042c2d0510b00214180210441040b0303001040c0200300030084000795100030b030307502142150038020813244200c0f0b40038441030001b0300c1d03034100900c10807908aa0505051141100a01e000d1200402f030a00c00c3d030030782040000300005100c1001740500d0307541c2071107419007212043d68408110100f03500068864800c1001c02810407994500180c042e80c41207046540c50420 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 912312715 1250 912311465 912311471
    0x3060f0b0f130213080f0c0108040506040b0a0b060f130510050304030c0c0b030705070611250804050d0b070e011407080904110c0c01030501170601030311011e14061005041710 77
    0x40392102d039a9481206081442c074495007030481c47c03941c041c1d40140c1c0f149611000424003a036641d6240c8110306006004580d00d50b032105900040c96030f9260103040e00350708481000351180840c0e43d00102c00031095020b14003400b03481c040105003642c0241180c0d4000c0d09814a00d10400e06468003100c202c1541d07010365041c800200c14006000e1f805002000c03098000c0c0c0e0b003800943c881001a4000748031715442c150103a94600001c148407040c0408942da010300800181d41003a80d43e0012544601d0015411507a01c0862400c1144481e00040504078a4000f8641141c03403098030041c85c10345200e01c1001626034180131030300c451241c0d03558006030405022a082a500c0f84e4400754042e907104262884140402d06103800441c0c51010106c100e00d08a1001c7d000384400d92840e107040e101b00100347d14500440d500c035060101e92100031800701400354903508000805641c40302030f98000200c042e2140b48121117220000d4100ea60150584059812075140d040e4440244010b05d454046001d503002c40043c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 912313965 1250 912312715 912312719
    0x1050f130b1c06050604090c121805061b03041e0c03150b01081015050d0923010e1c02070305060f160f0804080906070b1003060f0b0f130213 62
    0x7a44001d4074514542c0c8218090010900c0e10107001d42d403640c054580c101c01c0510007001031700c056401c01c07410380744281030003103080e098909443c00350b0324161900c0e001c5003a05c0000c0810000108a0647c2c40101c5500004801040c01401e111502c0081c002505100c04a8001a400010400503030400f6900ca00d425120545e24640110480c6d64802e0420740907141204007030481d402098414440c0405030660b0300031b1810300300c60092086a020a10040100034066150700540521a2400c01402204103d8080116130070540e03054030070069442a40e41031224403121b02000103080385182003400c0c9804072142c2010002c92038544250b00c0079006114000501040809007001c0e40c2c00b41c0d10303400d00554071030103020054070415610520500012030040c0020045000c0b10040c22482d00010070b0b4505d040c0309500c2d01c10500509131103e40d00140b6542003081041200d202e14111100081c400303018a61800380050014004ca204560088a80700c103040402c820603411103001030780c0d405440350416 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 912315215 1250 912313965 912313979
    0x230a020105040201020f0d050d0f0b060d090507050a03031b0303110a030f060806040b040305031f090e280b0603031b06010e13120509011e12050615030601050f13 71
    0x700e4180d40070381c00b5000e42440141602e0010542c1c1d00e52000d1500e4441c0340c0416044108003c1c03103105020b060b035903940c0104174215038889005010380d002c992804909014036040a90402540390710440c4100068081080000d0300301400314100009200031000e4820582425000b40113a40a000040c0b90001900070205405600c01d602c0046c1c000703020003096444980c4150b03101c00941d07024102107007007000140000c2c828401035500c881c2d21007a80110384c05510030a03001c24a00d4000f1fa1450f0386a500f2007420100c100a41100402c2130f0766520003403680403111070a91b0702070020141c84151403100180050300d040089458403403040704014003c8207141410b545802080c081d80c16604c00c4840403901100c814880094117607000300007288503031782082c003da901c0c0c2c1c030081d8424180a411880c84580d11114041c104800c0c50948482e0a42c610500340c0e2811600020545e80c8643d03446041e43e09c1d030b04d5903c429a41d01c010282040c2d03664030441d0884101c94090b11310040c10301c443e0040045021 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 912316465 1250 912315215 912315221
    0x4090309030b01060c110a0308161110080702010506030a03051804020f07050a030807020109050d031d01062601020f161703040c1503140c0f0417030702100f0f230a0201 74
    0x41d402203c038a0380d610011b408010000c07401e0321000c1d01510f018032014080003410031503c03140d0b5200b8446503807850110070102e20b00608121082d4041a0303003004110807560203014441d4802c80450280080302c1032942e018040e405009107d45140c1f100c0440310171b080c0c5a40d0b04031448410200d810644600881c500503584620a02084000807011400315488038014010803080300d0380311014040b142c0044400310010040c4024094003a146401d004445c0d2400384200406400447c05001d21034401011240c10040400c03020b801d6a8410001007059120541c00c3e00e5529015400f1410401c1c06130900c4580b40801d1031441008032800070500c41000b0042c8140c40444e0440026690040d800ca0001e50850f84034104841d400407070789002441e00c124200040240b4070b00d0024040c2041e0301d86580c166a46d0800c1059000e55000140ea8815407914103d421040d07081032030581e10369040e402c4001c10200751a8900c0091000c107160740514100c031070400f4151044254002d644400329004000c0c06 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 912317715 1250 912316465 912316487
    0x70911042112050421020604090903020601080115060203030c0d020c03120402010f14030f0417070c03050613030207090506010c0803151f02121804060816060f08040204090309030b0106 81
    0x242d0040c44240a07034541c01801500c044074020081540380c01d4040501c1c03140364000d44400c9070700c401d040101080004480c860b51100c107006c1e41c02001c0c4c0b50f0404080b542100c010b013400c0410400e4101d81000020f900000700d0350f00a18a020b01e6842c0c0100d040c100b0302074010610a040e081c040070403642c1126808404151055000341d03120100360500b1141529948100307112012039070802c10004a004507500741c1941c10a00c51014404e50ba901c00d070b40fc2a0701e030040901160503014800e4100244001000180e4000418400c084a050b9517079401a680329540d2080c1d03ea5603072144002126a0b0203441089840d9400105c9181d80c1d10b0800d01240c80c4650b0f0502181c0b01d940b4150050b0461038041c140140c00b04da05800810f12110000c00301c890540120810303c0b01d00c9049400701e90a62541c5c001c440050021000034107220039680241002003a19400480421241001b016100351b07120b010780d600540c042c2d40014000d0440e04080303500b01c041e5040074148100010002405683c04000d01d51 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 912318965 1250 912317715 912317723
    0x31b0a020d0305130b031003261306081e1b1306080612160501030b150d0603201c05150f18060f0c0f040f03051c110709110421 56
    0xf00341e1a0748100c85d01d07000c20383d44000480300e07114040c00003031060410900e0b60700100009200c00c892030701004070701c2c0c1d1081041d502c031301c0d140c1136042000c3c07608031042c2508001007400d03c541500c03440d4166080e68000500704032a480e40c5036a142e100d0a106011a01c506040c585800000e54445101a101c0b20090b510240100e52030b40701542e08580115003900d0344039050440c4001c1501d854011005041c0c1f0200e43c5030301c00b06084400c4107401640c80101605401c501c40404c81c0c0c0d29504064140d080c050a500c920b604072044035548580d6003d034282104071228501d4000c110350790a05a1419108680c1d841e400124401031000e40b516000b4030a11030700100000404045031489003030380f070f004141c41c0d40004c20300120101d043d075100c8101420110700308190050802e50f6440700c02c0701400890380155006d8101c03003202012407100c0070680380803d58504090b5000925407004695602c5280f00b12500e41303507900341c4004818884002c0740d0060103800c8098104100c070f003451110000340c04000721 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 912320215 1250 912318965 912318997
    0xf14161a0703021e031003060b010509121b1f0528090f080d050f03070c0b1608010f05010813030306091d01060807050604140105070b04030305040c05090108031b0a020d0305 76
    0x44807a004904c2161b10540100c04802825451580d902c00079120003910113051000c1403280950302d0722241c100e08008030f050300080400d00311081008041d0080108000e00a030190214801c08608105064129410301d2030201c0c0d80c0c46400da82d003008410407032100d803c600142523108140681c444851015100c0b100c4805ca0b10603902c8084655920b09160214041881882028000182c402c061980185079023001c01400d0f04540c1c1d803100704c010481d4042d201c000704040c103565956012000c5ca024004091540c00b85505080001e00821001403003d07094458002d260420103101303400800060400140501c40c540c0750b6003141e0403181c0c0c03145911f0b0349c640c80d00070001030341c480000b1a00704451020340650724090404902e8000c240d03800729614140801000590000782d002560035204900940d00020103042500d003150b074160703d07a070005106400150052141c03204c0481220802412400e640d034a40101002090400c02007000103944111007071140400e0642080003000d4001c82c1039050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 912321465 1250 912320215 912320257
    0x1060b03070f030e0705030105010314010b01020118081804181e0228080d050301052403011211130b032503030f030b130b010f14161a070302 62
    0x10284a0004880010005842440300c00310540207134040ca8016120342c0684420584403c0864250b400a03401115000a102c00541c0d421200384a4042c40300801d03c0240a4140c05166501009011000103400c1d28400588803c422402d41c0340c064003042d010300180510544400c4800d03500401050688001100450440c1500628001c01c0343c00c41d401000350300314414034440100c407003840c0c0c0790702c5800c0307d0010408550740d10b00700300104030100d0704e6032502da0f6981010305000c1500f00d41c801240032000c401086441c02c60000c41524103450300b46021140498880c14090130510440344180d81008040101140d00c0119400200740a1000e400325021406041040300081c0303000e100c070707240c0c2d40c4411005100091082111a0140c40c0368580411400c80e441c1c000307540c00c40188a98190203988190403041943c0040640a0003c0707142030441c1d031468640700745c203014440d0340401c40304500c04000c500100017903000b514100780e20311230004030325103003024026000b540300c68a80040003401c07940c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 912322715 1250 912321465 912321479
    0xe040e0d090905010524070f0c06141908060307030c08100b09090c041e050f100801060812130f0e0411060301030f020108070e0d030801031106092b0c08010203090106 73
    0x3c2c0d5048031030262409070b180010300d20640035003403142c5c600180040e081003240041010729550485490280c0a00c0ca51185804c1e40a00410103480c01181158428098141c082821008201e0700c0080d500301004242d440d41c00180c1000d240d030b04002c140c050600360205141c2d2000650105181021008101114075041044031010003200e82180a80c4120f0310307003400e400e183d00700ca1801c03402600720441d9010b1900b04041921000c640c1c00350104240400c001403081031010440041100000801c4800e090894107a110302900745084450400080e803010300000d483d020100074600510070460752030320344403061440c1209803401d48070007100311002402890310004507030480e40d0080c012840c035401d42d40155860720000304518140040100c0d608074030780301d80300b241c0c2003944a40c1c0d43c130000d503040d8502401045c0c0f205400e80d0007403c05000403038860b21504003203101c8252000c0b1449000b10111301850341d0948000000f0100d000c0807600160804054014502a100c0c44e070082c080f01d0344500c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 912323965 1250 912322715 912322721
    0xf1605030708010e06150406090207050a12030203090c270c03070f1416051c050a091202010509011103130f06080916090b0f1009060807020c03030a030b010e040e0d0909 74
    0x6800600c0f178104001040341c02103c2a0010800e40014001040003a5a02c0721941241c1260384191740c0c40d040b4140c04410044e5401c1410801405802d013141141001494682d94944150005001b005061000b0380070703d0401e00e08021035034810900703d3320b80c030700b080c011081604143c0d18200410f9141c000031890328010710480741c041036407040c41c9080c00881c10200440108901d41038039240119a1803451030252404402c00003c1d6503100e840d603445800c0c20040c00d02c40c0d5035101028480c1080300280060381d1040440340f22610902c0c020315070a80400d100c0d41584a010030100d02c407000340340000f400f00004104001120340c2501d8100c90f942c1c60100280e20f580d903401c80c440090408980c107102441c0c46500c14050400081c060034a4000d00c1c03004100022a181503070b0002c10703001310b42009000d07800400d41e544070310ba82c4080c1840c02010701c0405d03900d004000c110424580c07070f90b01f000c1a82e4419a0b01c440c111000400600000684064141d2181c841102a00c005840e0340e00100e04400c541c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 912325215 1250 912323965 912323981
    0xe06070602130302240f0a1e08220b070c140d21020a020a140703020a17010b03030a020c040f24150c0507090e03070c14040615081501020f160503070801 67
    0x50301d0706d280204a4041440c5507010f030404d0010300200c00305001a0f444807134100007045a560321204840d05051030b0303402a021028400c000c450350140380e030300300045210402541100c00c0b03081910805c1380f0b80c40d00c001c030345130b4500d401480c82c40389005410040e9882038a904002c0e0114030a1551003500e203131004181d11419042030050780c07041ca80800041e00c14814003410000e510140c500050316503001404041c0745900817848480003038004080018280700c2e80b1a80f4034220000d514101d84280c2c003139110b500c003050b564405c2ea40d644001c8140130306900f00b0000b080c0414881c07500e030200700703600c2e0002c1d40321400b0b914482d4000c1c40300d40400354081c01287d850079400c5401080060315000c2c40c44090a030070054001140018040030b400508040303c4040a02240e007141803200391060f0a001c1118019807120303156100800d2840b860320b411126003038002c6105100d00e0200301c41140180d140a4804030030100f00e01c2141c840e1418641154038110940d54102c04ad10303c1b155541d0340aa00340c800708 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 912326465 1250 912325215 912325279
    0x20301060e0109031e03021213090c08061c060207210806012604230714030a352106030303060102120309071206060815040507060e06070602130302 65
    0x30b9517400d50407070790f0b40c0d801c0113910301c248110780855000c0c00419000d03802c0080303171110301480c3c64000d0186600501a0a4018020380b5000700d5514204e0005070107400e4008026461030310f059000d90602c1f413180c04486820307070840c81650a000b2096034100d05103412440c52000100710a01103021988074280421206882940301503103451812a080c078010000f503c221281c0c03040301a8602c1d086400d121010100e024200a0302a8a180003c004100c481215205120350090500400003490820410880501c02d402100c406005c40c070f2220303a03000c014480c05072a04404245104268640140c50300f1034450781c0680303203507904e80c1000d05699002c2558031350f0146c1c110309020300d1080c01480107950b00c003036000d0803034840540d11119028460308034103082c0c0e000754844409001c01e00c0d040080b40422040355515000c1c6250070b0300e40603100c1c205c9004070001c10444440400040c0d0701e42058075981600850110758909043c00026043e003080e10040340a0128501c40040721510041d650b0505512 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 912327715 1250 912326465 912326483
    0x705071b050907110106030203060f0708100806013006050a06050102060103080d092108370e07031e02100804050d201f0506030d090918020303030901020301060e010903 74
    0x303603140c1944e0000d50030b50344140c1c81d0340c1c4040000260341c0400185006170000e440c60010790900c004000c040700b1005040340007074082610200071002c8000f440340d0440f0001c100410071090b10700031881c00169140d42c20b0748a8102c1001400921503170f64041d6000b0f040c94074041140540d03ca0041e40c07115405d12003d01254030902034411100368503008000c55902c150300304030251240906501045051161600009020600b00078009170560f0184500300c1c404204000040011514922910749803003903194281d49948405e000c0b49801c20030b003005194001c190100100c040e4800c203034140800e10051340729052030702c5c0b004a0180a4001e00740a507820a010708040e0840308405e4590505165101c4c200c2c2c0c00b02000c2c0c0704014801c0c0210050f030319042d02c4106403007138421440e00541e0b4000e04410700c280c000500341502590400d1041d008c032610341501294000c5141108405034600c0034020f50180000000c02040da0010740c015410717071700940c480111811100c0011190407046002c01898105 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 912328965 1250 912327715 912327721
    0x25030b01021c08060f191518031e0503090d1401060f0f0e06060702130c020606010806030a030e060403060e100612020d03110f0313030201020c030609030a08040305120705071b0509 79
    0x204817a05000f0f00c1030240510202c0301044501150b00030540e0b00100700c5410b901c804081041e80034180c060b1820442c2d00d18207145017181ca40395000c102c0703c4000c082c00e400c15240c0c1800c02070305000369801484000c0100240c4807403414010343c00c11b00943c17031440d15480d12101103065105103048400b41d0744880d6001c4c5c22941000f800304181c80c1c02070411644084144100001030303607401e6000b00000084c00c00890810307240c0c03034060304d81640608035905100d034240030000309890003c0c0c0c202d030854162078010300503049000820211303c555000500000c0c2048400d10840c000001c450640e01468034082042c16590b540d912010b40003a54001c3d40300e4050f140c0080440d11448521003200c9004041e5040301c1c0c0864401842c40d40108042d03421000e11500410945d138042c0040f00745403000394041c000614000700342d01d44900c0f9415280041c00700343c0001c0b0703052510642c1621400040005031100c9030920ba44007810f10f401c84841200c40d200050301c440348070300004545204803030015104103000c2e1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 912330215 1250 912328965 912328969
    0x30611041706151002030403060c030e010b011e0f11030703050705060a02040333050406060512060c03131a070201050a060b160204020f0d090609021801061725030b01021c0806 77
    0x213018581300b401144410302c404404108544214030441c03805032000200c0c4060f03031440740d00317683e8014000c82c140106540c800e00e8078513040103110a02400d0740f17440240c03030348540f00540da140d003e285805d4540c40003080c0e41080541040c000d009581c09842210741036551144c480e0140c1c401c60200900307903001c030140708003088c00c00076402c10300391011003084000c4000700c500d80302201d40c1201c4c01e80720281c17034810401c40780c206094078849441c018005840f292810760040022840050444046004800344000c140310701d84250100c8070a4840841c0c4044c100040300071b018103401d44900b00c0051406200181403c41402101c0b061550755080081881c016002c0000075001000304420000c02005105155501d620030991498414031000a00ca06180140160201800d501000340e40f102001030012a40003000f2100d40345905910200701d9403141d14203800d13040034085072a2688d01540301003205580507001a081c0321021390850700c000c0000c001134203500e800301c03a001c0c0100c4d04020100d0158 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 912331465 1250 912330215 912330229
    0x12040323040501200a1b05040902180714070507050907080126010f061707090e03070b06011404090515061c090c1a0d060b03160c0c03061104170615 65
    0x180c65621401304d0502c0c2030314003905000041c403003100c20350b4070920809801030819040c403003e00310544080200c410b00354089920000e034844039145194a03c000542200c0c0703c3e94400c840d80b04003603013103515280f10349006039481101d4090548605c00c08000110018807c2e0700483c100d50720002541d003011744168a25000343c20700301d81500c030755403900303a072040f046017a02901c002444403086160f8050700e040c150b18204256038102d001500d0a040c088000d20200106441c00207412214a139040d40726400141c60b280401031240c801d107100454001340150f103d070b200c00e10a0201648a075001c1200c1e40c1000000d1040c1c046e03100c40e41b641d8206000d440801d0343c1c48405514459400c400b9103586940200c401c910043c250b084005900140000f604d209031f0250b0702c010312a03480750b0f90650600e81c0130a40400c0d41c0359120310403c44513900b10002e01c8212041c800045400c0304040045088250009285600c180615400d003039101e40c80703c08038600000e503039104180c0f01c0303031807041c42002808004070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 912332715 1250 912331465 912331487
    0x427091e060608070f08010608030414011b0c03060609050609071e1b06020307140403050c310b010314040c03080921030307030f0207050a140f0312040323040501 71
    0x16907664003408240c0d5201041144c0107403a40c04050040c19140040c600d0035194250000011500309010401c02072400c1800c4410600e401d08140c0300903602d109620304d03d422042c04c0a800c1c1810034000005000c081d901c11b0060300c00c2148203002c0c95548605000404005442c040300054060400300310400589040f1030a9003194580040c03000e00340c942110a00001050950700b0703660010a200352190000008113807a04d80141e2a410b140c615114180c458161450580c002c0d0945250203100600850280018011984490103008c040e40d000c04003d1104a8119000c00e14025000590183c00b0410702d00c91540120b00780d402508680d1400c0407a0403264459810801440c04003881c41291041001ca40f030300c000c0210b032207160011000741540c00241c044800e0501c1001b00102148020889000c0b0790703041400b41c5485402c84801074036085280d140780300c03540808240c9900c92140c80d24810b0045000c2e90f60500d01686d007042000d0b0207245c0030420b50749500100001c02c40c0354007038112005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 912333965 1250 912332715 912332723
    0x601020a06050c090901060c0f150e0f01090b0a0b091501030b0909010e070e0c1e0c030a030209040614060313020a150c06061a07080d0609020427091e 66
    0x889000c5550301d2006445007510b00402d84407020600002509140000600500645c946280e220700139841d00009000144406847c580c1e050700760040c0700303880307030843c406000540c011540c1c21130002c800903000706100d04d000c441c421901c00109002c000b8a005e40181032600070304100807605d481b0546034a0844007410941419205c42100e1040da0396501c42d184126024400442e176041c0010200e030404025400040c882c060032424002d80f0081001901da84010b80c0000002d580e4a90400146e18012030307d025081c0d1100244012000c1e50580280034010030589090200f1303074413190ba001d01004100da807203030403041c20b1000406a845190805104900140c41c4c91182622034060a011400c1000c058000c1040d2a00050070071500c0d11071080182018102c500c03282d0540480c526a610a156026105400200382c0e0302c2d10b40e04c244d01590050003090307000c41d0380380c3c3d0b00c504076148404560503030111750052100c1105882c40320300030b840640c0e90150448100d6410742004188003914002c00303032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 912335215 1250 912333965 912333973
    0xf06081e0408180415140a0b1b0c0a0312080a0920090a0912110f0607020d0f030902060405060d140901021308070e0604020c030f03041109010b120f060102 68
    0xe42240c80c441038450040340035801d1566240000d1a01d60990720080d820203008a2810340c841c0465021021488290b0f000d1440c914506130308100040c1d62110b07141c00800d001c2c3d000090240c010800b03012038481c50b2107030b0001d459440e00c2c3c0c0c2d020040c1d0103100e0b110180400042c152005241c9100c0c4010a5000300d5180c3d00040c03c402c1e680f2a1208500c400548800800710600d8801140c544940615844548104140481140742c0d9442c0740c81021f002c1c0a10510484c0344441d401c40b80c0c00d0010740303a1086600b0849800c0d10f09104005c1d5195000e10721100400c4180c0c160f245810311034002c0d0040c0d2500038000900c0c040c80c140602c0f000b640400e00c40d001856440075105a4021034528060240d01507500240c0c1355450600c3c0c42030141c0303950307120b481c03e5800003208000f035003c00301c0b507ea0f21001c1260700585845058288a0a5110710083d503c125280041003004202c03420951102440003a1001000e03aa02c031071050f078030380c031590f850207428406000015200031380c030481507035003c03070184140c07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 912336465 1250 912335215 912335251
    0xf0206040c030b062d04060e2514070b100f060e0609011101090c05131e0f02040f060207030b07110606040905030405190911040b0a08040f0b091b0a0f0608 68
    0xa40d20fa05101e8901038000b800c0c2d01c17017103081d10b07140c0900809000d00b030301040703514103105a480f4854649801c00360180780300320102c940703103074007401d010080398412500c560340e101402e24101000710000ca40b0300342c1c0d100004902251108501c5004810f40321380740c507202c000e0113072901080503c0e002400d405041100310f505c4d01505100a000300700c1c00c20306c60518000302e541802c0c05c2200800c030045908540f0ba292005031002c030200d18440e01c03c20150b45c0030001d806000c60062401134032941d006444400d44001c0b00261a550020305001205e004015100054550003002c5038901510860b400d80e075405000898681d24090740251801c610803030440b4038003a940c00c04070750341e107500d900c0310046640b00076010000800c2c40c1c052070f4140d101880c50280f030141003c089038024080c42400320200b0021000240800c01a85403d428103070f0460450a0741745040340e030031561191030303069101c2c034003481d070008000b1401d00c603240302c042c0c8020365403c100d1035003404801c030b884600080080e00c410f10350b00c80b8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 912337715 1250 912336465 912336499
    0x180f0d05071d1033120f020a12020904020705010509071505180105090103091202100b03060f1801090602030f06190b0d110f0403050c1e090f07020f1c0f0206040c030b06 74
    0x2034860211340a803181d002c1c450700d0030641c108850394804c24207041e81c01009428080d40e4410b500250300e01501d030006841c0c1380d1213070105009000d070b00310040c0136603e84014030071072003030000c0c84504070340c41e88012a05400c05003004540b18065100d480e0151900d1454808c2650b0041c0c0142c03070085018940051849086d41721212400810340500015030400034200000c2845405000503144041c1d004140500b011070903100a000001c0c8001c0b1903458108170322680503800e4020103040da400c00c5041d500e0b403c00400608840a00313482c03040c402c4140407020341a22029500740422104000121806e1291420140014012464108494450400624110480b54400f03000038500800003448000c10300300c1880b4001c0545003045408076115a2030441503038802c112107610288014000388191110402a49001410740503100345021f003242011142e54001041c40c24140c03145da40b01880302d0480c070241e07220340050760080c2c20300c1103140d000d0000c1801002c0e1150070200281c000000b01040441e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 912338965 1250 912337715 912337799
    0x6071a040c08070b0c0303010608070203190305190b010903060222031a281a040c2106080316020114070501020a0215010b180f0d05071d10 61
    0x14221000681d40905000002d403c0180401070610303101814a46401c40030b019580c1c1c041485004c00300301d00740c1c0000b0b0341c0300e1082c41503e41510b00200d4000281c182d071040036010741401c807218244e11700d40b01d00c07144409d1018050a0456981a103454103450b003540c85600c00380d030285020f6803284c0705880d040e58200803030220703010095014003001c00507079110303040000c24000040e110840740c2050310003040c41f00704000300c00c51840880f5000025a00d40c804403400700144060b8040382e000e0b180c0512444055000040410441079100d00440483c118140c10000c0f15503e010b880181e074811322403c240c9800285143c95541c0c0141000c80c02900b200d80402d45d260310506d82160203940208030080c0c0b9036010000e02e80c1e000c40f010000709a0307604004808009018441c03105900b40e440c7c861444050301c44104c0050540000740014051204505106540e928207200d1548915400441c18911704441c04604d0b00440c0d80c00709102c155032424628925603d80300444d287c80b04030a0291001c810300443d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 912340215 1250 912338965 912338971
    0x1a0a030506091905070611120f0315031f02071103071701051501080403081e1e010503010b1f0e04090f0552031a071d06071a 55
    0x612070703490b0441000b41824600401d150b0301e802161280c40c00070b132010402e0070503624240b170b200901c20010301e0300502c0e14025500ca400c043c0c1c0c1c005800c030600c01c5088010340c450904102070036011005e41040c03550b50022a6141400c40c1c05100303403102031b418560010006103005105101451b503038400040d092451340d074000640c9015a500c0940d11000030b00916a004503c10501b22441c400c240000e045803c0003440203040011a80002c0c80307680c2812940082c0d5608400020100d2500514403100b40c4d4403261080780706000180005128501401a00d0607500007030304106d005601003081c540c540300b23120052014441c1c11030388001a44c0b0746200300c00805019511400484840d82001814070100c00e203c04d440b10070140382c2001d4005040130340401100501c0110303a0306820f02500760040c40d10a21a1112144155000801e2140030004052a858044101810b03a2980403059810540c41c01c00440b0080f0b031904103030120702c0d0a201502c4c0f0903001c2d1f0003140a40407807001c0c101510783d0071 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 912341465 1250 912340215 912340223
    0x10b1c0e03040e1803040609050411120103050606010210020c0c01030c111603020405060603070e1207031e05010605190905070909020d050106080c120a11090a030c06030f1404061a0a03 81
    0x641000600c9030b0f0f031400050384c403840ca409149480d062060007480440d450286c01e01440e10340490324040489802125014040e020907a4084d5860b4038141d61900400da40b0310f40188030711020700e401d183c030f04d10031540951040342c01890005200c200541c0508000b40c00b40301032000311110020400c00c1030181c0084109079502007500141180304200440b01e02824660060701e05004102034241c0203030682641103070440301e00c0c16800c1d8034036030b031807401407150802000411011070542984440112000071207100380020b006450721038040c0210900c842d03500102814a280041201d04000d81c441030308805980ba20b410616292032120701070342d1280c0100d0301010303601e000400600354001d08403a046888610342629003944424114004900640504409030b544c0c0e201d0400c209011046824881d0701404c1ca0b8405640c07410b020b20030307886611030200401e0504d001540c0c0c484061003804010204400c1803040c1d901c030341e00c1e43d00041c0403000807550039010340f0088182070b50324848014011482 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 912342715 1250 912341465 912341489
    0x3112101091502040608040605041e030c060c0c0c0902130906080d0807020d0c080f0d11030406110a0c03080603010e01110d0f050c0a1101092001080708010b1c0e0304 73
    0xc1c1e0300d041c9044500740504402001e02c140001d21a55a0201540d40c02c540c001d50046159141d070f0402550a0190032000701131105e01c00b030b0400815030000340440005000714010081900e0124090f901c03490100001000031001441c00d015030350055002d41100900710203050511070300da01350501101c0c0c02d9000202e00d50b10800903c1c5106504c484c01c4c13a8025010f02c0604032181d14600081c1002107020703030090a02c40c0115030100011000015107004426904041c09060300114544400b0340c0190f034155061410f000082c07220300c8688040b11104075072580c0c0c0a080c403041e602d0440f148c400260144c0d9040d500d035080c0100341c4400f400350384c40a0038494422543d803e604255a000c50320110030480c2a0b074241002c0120200d140d07810707160101032030304004203107800001d0164010b140b6010010030380504d406104203820a103c2c10900522800e880b00407040d00e82d000d01f640e000809105280c1503400401280031484509111241c030300c1c07021f6002045004900e88641d0454005030460018146 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 912343965 1250 912342715 912342731
    0x40f14150c12280f0e060403111009030507030f0c300c080406210501180515090105010f050d110a090f030f02010302090d0816150e060103112101 64
    0x71030100060b42240800c03802d80028400f288241c0c100c14034102100ea2240d589007154042c0404903003100c40740c1c904d030b8000e42d005072401349000350985528074803004061069203c2500030740028401c92210a402d41c0714141800441d43c0c040b0307000d0541900b0b020030031000e20403003c009508407401500484840041500485101c5103040e2295035020240c020080300f03c0d44840031441450031201900c456240c002c80018071055060500b035001c080c4005540d240100000d2403a1512401d0350199a840000f44000d03220b554200b001c10100303801b05a032010000004100d030b50300a140c0690341c80d120f420110709010f8070b00c0032a412a1091440041200300001c1c801d601c0c1a8402c0e0694081c0443e0f5205064450840e01c60303441100705480001c0c185036001074807624541d00c08500050043d48000a2603455000c10036034840c03809200300031103041418101c0d000d00d0441c0c1c1e0145540800c800d200a22261313103151904000f4a03240c440807a000041c52550404ea542100d00c4405e00c6003a090000c28012 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 912345215 1250 912343965 912343987
    0x1a06010e01020705060910230d15060503060d030207150804140607170604020906041409060916030f09021906090506070c06082e14030105040f14150c 66
    0x241018600d00c0c110b420903482072260760307518801d441e070003902541d0000b2000350314241a1041d07510000f400502c030112441000000426038010068452094018172045c05800c02c07040c03500003180900c0c0c0200b0b20600000700e20b400c000420f50318030340c000d104035040701d81c0e20301e00d040414440490010003d45101c00b00000e100381030700400000b11305c01000f003c8600c1c01100081458103030302003d150310215007020540542d19501070f070b2101d00c001094990b0f501d13910001ca9000c90300d44a070344e41c040c0f400100056840d103040c00c1c4580c400d082900c198918001d412100700e00819030203103a001119500c506070000f580316a011070714840c07204907034003100790709120001c3c0004901c0d82c4298030805041140c40c000440c40302c4040121130f41810b2003129a140c801c010307850000145000400055400f050242424031010b00c1c104503a0450700c0503411400c0721080c0340c02c0c0d40040b50050071403552040b102e80092003484100300961100c0b016904a039441e1451560031400640c0c200d031400b0000301e09a1116 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 912346465 1250 912345215 912345227
    0xa0c0216120512210405070302090a0501090e1f1113143606030f0a1b120807080921010506130209030c21120c07080f030304020d0c031a0601 62
    0x83e60200765001d00304661081e0f89542440c8001d40040800100b401190802604000d08006581e0081201d40e040c036140d540e440040100f44200001c290070820794041004000c50395803035180f088081d107407a0540700b96009c00503009840001200e070f40308100300d140d0380030743d14008400b03000c0b40c00e84200d443c070300442041320090511001001e01d03420300d500300c03290038100e0720811030021407034174071035032559500001a003400c0075003c852590303020f5416120200702350041080f0f80292010f6010001c5901e43e03a443c01c0c440d04284000380b52540c10030503080480d240e60080c051042008064001e1200d0308110402240400a003074084c0360344030001e1041c1c5242c50000c0020b40a01000c003141403090f65000a81e548094202d114054001144109020b01c588030050400300e469400326107602c02050742030100765000d141661401c1c003e00b02d0109010f140810b2045015a4150046007903031116020000e90b076946460486050100382d50000005049010b951040389100808200a19048002505d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 912347715 1250 912346465 912346483
    0x1011091e0a0602070b04090b0a0314010905010507111203100302180f0a02030c0304030c110d0f120503090d051c0507121a010207121407031506090605090a0c02161205 73
    0xd542050101784190340510041d10100c8000c2000401c2e00810440450400c15045e040a0034810365040388841c11081500104800ad20881c0200036a660b5101e080340c1c10305445454440c1900072801216244210801842d004180e2055458038070f07549074002120300303c104085008401c03d0341c04205e1b0f110750040380c1c160301018100083d881c51801c01c000d045d007480000c00c014107202c0c4c84400c0304c0511680001c100b482113005031072954100c400381083c80346440e5641c0122600c420f840a15102ca51244095900401c100001032180010b0350310305681da50000301c80c01c1c10207842c807000c0402c0540180203072030160002da207400c8a5507102100300001d44450b0040784884960100268000366400200142201c00341120344010310502d01d0302c41800407075018109200d2140070703000b00c2400300c0c2580c1405101e118200400500c0c1c1e4070f9000c0020b4810382e10a280d4030114007000540044031a802c6241035440728410b44207001c0007603e02c04040e1032079030001203904940705603510401008003c2549 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 912348965 1250 912347715 912347717
    0x307233702010f0503040c030c12060e0d05070b1504020d0209101d04110d0213061e0818030c0f03031504060b0405010c0804080304060804150e1011091e0a06 69
    0x40d101640c0c001a02c8100070500390707000c110f4000006004e102400000801541e84030a0074100703543e85409044030b9400201c0103481ca54035210240024803000144002c94101da600c4142c10b09186840c1d036040d145008069080e203a031142242c8103507035111310044c84071200c0001c0c01a00d507031840c3e060004240d000c00305042840840d10401c0882c825102042e0f4441100f102c01250165880c46040070764016007100000403030010400054500a02c4120350640300c480d40d0b03000d001c0103d0a203100380100200607240120303103a400440c0d0000841080c5204051403c03048920301010303078000d145043c91000c2d1519042e0008018459010840d401220b0081402c440500000c0d0800300900c5086c403403032140c1814400c05490440400000c1801c0c3c400410164040c0d9454681c0d17864040c0c1270300e8007100c048138181d0942d01c03a0b503c100c07180e208a143c000f824100900c0f40c40030940c0c00000408000050107581035040c000c1281a40e500c000c2e0700c8900d000503000c030a0320b0070f082c1c4c2849483d00f401d8100ea4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 912350215 1250 912348965 912349063
    0x3120f1b0f3a05060402041a180603160f110a11030d050408030d05090a0803041a13030e09091006080f060f2a130303050c0d0e03030723 60
    0x2400d0880c00c100040440d41c20000005090b4032a130000a0086c070031070344001c0d500c011000c1d08108845108003d09140c0518061043d114803c00e01041005d210803105441c01c103031911080d00c1d00b87c0c0705412003802a034031800c20a04800c181c103a007138640540d42404403a40702d0568030030121401c041c0000992141d141c10071a003000e00300641d85072070340500b000c00f0000503610ba0008010710801c004c1454403c0e0084070707050b641e0519040445114482225881c80c50003000040303540c06e0081050040400e80598481c2090358001003001040c5401900310f12440c07144002d0306c842c284451103050001c00e4040003d005144640e03584505040c40100040308034000da41c200025100214800983c0c00904c0b098030301c1e00000c15000d9074042c0071b05150010b0b45010b000b8007008050f00b02005001c03010300300c000c60b001c0703100e640c10440c3e02250305400f041c0c1541083c48564001007480030868403120020300007091b00c0004030303001460507003603c030380200040300c0281c02c80b54012480301c2c0300c2564a10351404 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 912351465 1250 912350215 912350287
    0x10e03030a03090c03021f0206090304050a03061508060108071d2a13121e20130f1407020d050a1101021207030f0b010203120f1b0f 58
    0x80e103a0103078184001c1855129014001000700c0903c0310800345900410340083c1807640703614151a40c00841005002d88604004038401e80400002e40b01100c000030301540a15040d942c1e15000741c4800484000e00c443d10740d0300071030b2000040c04070501819414004000892814400d1084d01006200c40340c900000c500c00d2104c00314070450400c920a500390b0b02420540403814100f82c280c41440508202500803420110300c444490848100b800c2c001c41c00d01d0500000040403098040b90410000c0010001c050116500d100b40d031595601140020100300c18030101c0000744080d55041030341503020035034507404919040e4442c00070035040940d070703c010810384043c02000340052080900e040d0502c40c902d60130f804001000d40440b422815003407440070440c00c117100094050407003000340070243d608100c00603500b5440003043e543c1480488c0c000c610980c0b1010f03a000ca25001c080c2103803603841d41e59022074606a42560003000d80a54148a840d5145400381003190390030017654600c0440ea00b882c501c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 912352715 1250 912351465 912351469
    0x182d0509010e06011223011d06011209021c02011812111309030c0201121104120327031703040206090103050a1e02040314070503030a030b040b0a0e1005010e 69
    0x1420741074034441e0011526584501e801a0340920010308850b1040c4d0915000c2d030b00c2840c0c0b00303a8a12031906501c1000a10340d0f22491000c2c400800071602c4042062041c0c00103800717600c110600320321210001d000246c0902c40d82c010503800d43c4614032210000280b00710703039821541d10520407a21600003501da03101d0541000c807040002c0c00b541c1c0b4041d020302d5510303031050f09a6450001c031180014201d141000900d10794600030f03020559040d001d80c0403030413002c1103c80b0001c0c10300490704e503242461000d510b42070825010721603102003030005604100340c0c00c84c0e415403030703a01603980c0c11041d00040071540010b15620f0400d038880034608004034260400d00600c801a03d860050b00c100060909011480e42e41e141005001481d100101010040903200305840c0ca40713695004106072400b90300f581440c180c103040310310ba07120075621135240c142e402008101c003901c0c0700e070b405088190f20041020401d1075031a00000c0105e41710384c0040031052000824000d4181c850091a0300520382800c045c3e000f4440040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 912353965 1250 912352715 912352729
    0x6030f0f121e0703080a05092116060204230312040b1605011e05180703150209040203190c1805062d04150924182d05 52
    0xc10001c041c4400308006490304050a001c2810324801c211040e01c4904a042c004c00d502da0030390380900003038505030100340b0801002c82c0150040800b40c44080d0389e440c07500005d1038035501100000201c81321001070380c1c1c005041400107100906c0c0c4605101740101200304017102c05810709881903c07a60100040702c5180f210702c8195001c85000c003011030340300c00a10640b06586410760000078002e5290620300c030101ea4800c0d002c0009180c00380e10070010f5580e140c8507507245107030700b41d00c984159021302c50400000d20407580349013078007005000141c10b0808003408141680c0003502d246920b02c0d0340440090046000c0c1c030135900d18002c50303d0000a005c1b4033f240051680f40c1103004480c061400003c08441040b0b0704800d03403006c0340b6400302c0c1d04183d0101810700005034016016002c07004070502c001c0324000d84034640a40549410001e001c0121180a01800c0400340c00361421090043c0c2c14013607010748601d4840c1c08010800040040444011003052120300b11203074201e01c90b81c00840d6010301580e11140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 912355215 1250 912353965 912353983
    0x608010f0506090d0218071805030c0d05030c0109050c12011506030c110601140a1512020304140f060109051f0302060706020405090c0a1e0512280506030f0f 69
    0x16445079030352982c3c03901007100c8520541c1e005e90050b4011000e00d2644618010442c49400395565400c40260a80300f10f080d0102140305495041d4440c820502c1a45800d40720041150300c03400480e440c2c00c0112030601c0c01e45845400981d0941c1000000700c0090424000c4840039562040c02002202d10341030f0101140d200d41c0c007490b420582e0302c890041d40680203400c2c0004198070441241d8041d0382d115001c609d0074000350b00841c0102803d0701e0000c0c00201d41a2145400d20711600c4055810003041c2d01c80000390002007080c0e0b280c4540306051382417804180308885114030b002024000780c1d030401c40003105484004d0400081c80d040d1144503840c0540022024060b2541111202d82d40c0d1250309059019000c1c80e0480366021030404207004824058600402203186030340c4840414031540c01e014403270008500302850228808000c000c541d58450121298030420101c50141d40111580719003084648124000c0d0b840c81c1e941c024400c0d14a002c0040b5600512140c0061010702c640d0340c185c070b8803203030f0070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 912356465 1250 912355215 912355219
    0xa151e0806010206043801140603010501080103030c02030a0206030408030702010e0d0c080c10050705070510090c0e06121b12031e0a02030f1201062006190905060406090201090608010f05 82
    0x61022403c001515200c01c1b902c00000000b0750040c51030011140308644203120b080c4040d418908515558105030742664100e03441610707001400c1e071171070f20306940182d0307502d1040360b25006580340c1200594403000514011400342048544914002d80040d003143c000e90b07000c45c0280d200c0e460307190000c1d91049101c40f219901105154031501544019031401d100300d407110100718100003c0000150340003020300341d03c600420480b10318801c001c0d44e4074121042034401419210711094280040c02c00c201d00c864220002808061042000141141c104104d1409807441d03199020302c0005603181185031000070f5180440034500e401089801602c0000784007001907040300d408198492000d00a1055404e01c507810600c659072100c401c03c1054041e8424005c081c00701e10700300d5060516110260f0520300b0309452100404607622845c0780c0003010241c603035020b0a450348a851140004905011050003184255404224842c0320b20001d800c44840d60000e2042005280c0108290103140040c00c08a03a81 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 912357715 1250 912356465 912356483
    0x1e100903063e04051008090d0f1202070219030b09150c070f020a120302033103080c07180f110f090f060d050709080105010f0503070b090a151e080601020604 69
    0x10000e620b40e020b004660000d903011085036020440170b81c0201c1214843c00940069500b02c0074002d000382d0300400d01d00207400c00140c0003000031040038001c3c1d0040c942140028141202144146141861000340d600b08452980c5d11506015002e68100000c007001c3c11004610415450407140d06040e0b40988070300641104d1106c1d90110541d166a0326030f002400c42004c2840d0105160300707002e503907680b001c01003007540e6208a502882806030b0050319040301140c80500e20a10b07156860702107268100c81c0354900b0901510f40000750f000008101c044507601e12550102e22646125504412540c28080c125400c50b0100031507032921101504450450000b21442c900707020740d14000c2407a40c014442030031841071a080c2448203403904460548100d81d05500280256030b01c4001c1112007602d10f00c0303005d0b010340c400c850a001c1c01d0b1142014000c0101d02616003c1e0140d600d238200850b1a131902c4115010681220411207a030b605503410389100074880c100070800b0308040380000c0d940e040041014200c081 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 912358965 1250 912357715 912357821
    0xc0c02091509010b180f03030a0f0311040807090c081e0a0b1c060510050330040f031208060603041104110309070501090905070207051e10090306 64
    0x148400c081c01c40c0c0c640641940760b2581c440d030404102c0c3d070249480740d44c402c4103a0003d00aa1601084a00c0512070190245040c08a004000d82c4c0074059020034009054584001304c90701b42c100e001500051048800410805203041d11910071501080881d808016141c0c0c208a80340c2200704220025131120301c0c0c081c20681c3c0e11255200203000d05030a4640c00003000d40207035648141d4034001c0e100180119410803098846100e5501805c030344e4403c0e141c054100341d07401180c103d60074442d0011001b100310340c00c2d031044500c2440d0210350b203d6000300c3e001d038003000790034002d21400600541c1401c2d00c5050800303040c1010b06c00107500e03002c005c2004241204540f8201b00c59111500136071100f07040302c0c0740147c69080000d0a01e48442141c0140d500041d00a040011492124000d4902500c0260040d004450500b410700ca48125004151485010310746a4034415840f1840e0907064105a6138840001504500d040c90039504a440440b0110515100f5408406003800c0a000c400e85981440f005800d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 912360215 1250 912358965 912358981
    0x70530191b03080304060b0306060d030807031d0a0506160305131106070b09010b1c021f0c0b0c030a110702011d0d05071403010c020312010605031305011503030207090c0c0209 77
    0x5482c0d0001441e0301c1c404401d02007009215046020070f6841181521425611182400303014040300c00c0240006411201080009019610903030044000c682000501c030355114950380741c003a088000b16200d9008008010b07028206184421204401386424803080c00c00c80381c4201d514141c4407001d0241c2034150307021240b03aa986003c4940c1c0f40c1d030141d1000e010749440e82e0310318020002d052065001d010325006130030450940c0c40f081c0703d02a600401e1343d4400c41790101c1c12a0029078591560052041220340d580116100d01001d52140200c0d40c3c019039a440d0404107541034620a08850081100074080340c001070784c0024103440a80115100314421803100000142031180c2008050841e0080d44c80100350715031141111010f085080e8000d01061070319120403039991040104040c940c1409900602c00c00b4414001981c0100740302a1000a404254440c42d08481144203030903007200e50000c0030002c058050002c200202104d080400c0700001156025102a80800e002031044043c000003038041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 912361465 1250 912360215 912360263
    0x1a060130020f0c0a140106050a122028060f0f030c02011805010203150604150305070210180309050102012003061c050d0e09010f0902030907053019 65
    0x102d0f000b10884050090b6405e259003450001c400300c40d41e035401c0510201d09810100c1843e8100c0350785115030b00c944000d907118508102a00401c031846041e03a202001210346c0c0341d941c03009000c41e00d4903030401800025070b20707032070a0340e92680710b6014450034100c50420186c00c840402c4c0d40341207030308011815480b0f803c4100c1c0144001c40202cbc0e9011103052080d01401720541c050342c400c40c103800c0c1d1074500c14034040820845000d540710722910b48891a0701c907a510340c440d03046036030840c0e66401229811150180c528069030140446140d840c00490440d03c24180c0c0a14058000c100c2070008000ca021407103003034822208000700c03046903018000003080d01521401c4002c0d8000c850101e00c80d6902140d841c216803100001d41902c800a400e6150802207460b00c034a81c941240d50500341400020310382841c207800b13500010011945c81c010340500040d0f5480742ca06000d80d08540d80811341c00d02c4030300180b41046c011340729209070403a80280d1411158148050420341c855810510840d00303e06030744001400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 912362715 1250 912361465 912361477
    0x516031701080312061c08180d060207112e11030a021509010b030a0209071e0801050132070f200f0324060d1a060130020f 54
    0xd4202414000941e044010000e46050a00d155032808941c444c40200b001007012180e40c0b60418110694000000303130684d0040ca8104103124880c03210620b2100003a01c0714400580c20380d00300da00011003c081100941030035541200171110f48203900c2005450358072401201c20607985403103a222101c03040c2c5000340050304448158400b12030340c46030702440003525200703200c103070b50012507034080442c0d0b030076806018009440d100603004001d414002c4d0200845d280d000f500307507070502100c1740c401007090701c0240022601050f80d0b02c4a1255500d010001014410199900308941701480003071641d01001010580320803000e4080107840744950b040c058079841c01a14001c010300c0081c030b0303000003101c60810f070403803048021900c40600c50040c90a00d900c440c120011054411a088a41034a484151480c0c82d0400e070081c100c1080b8202030b959400c0b528044842c2d801403000658200b001641c1d0001c0206008414000c0007a02c50040d00b11103c0d00c8031076440d2100400782c011480c000e80c041c3c0305040da10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 912363965 1250 912362715 912362747
    0x40b010b0c150a0e1908030c090d0609060903180f0e07020c03030c0106150c11010f030b040608010f060b040e130f1e051b062703010c1d01030903051603 67
    0xd1400c1c00c0d00342d0700082015040f05030752802500726649008a411041c100b10036041b086c11071440d41d8402019032554403099140b5400a00080003002080c070510500c0000c0c2d1040200050301111030070080c0804031078400d0b500051450550500001080c00c090000300c1e401190102501d0303c490105074140405080302580602c00403503d80a400350540000c400c450000d4000320302c181c0400001c80c2e18181007840500f007404c426a9414655114400c212060100f529001a41c580750344000b4055440750742c000d0003269114101145078030034030700c40d4070f0040504528491500d490402070840a010007065440d01200e007804103018446d50f8201a0755866020000c3d0b41c00c442d01500c1c00c650014090420b550f64865205220001c1d62a082d051048400c02080b0034184110300903c50b000640411215070020301d040ca21613940d480074001c0c84207020407912003150407109503901c00c1c2c81403c030440c101e04040c20040300c04080790300107080b5500c0d815102e060100b0a411400e0584070356003403510883c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 912365215 1250 912363965 912364003
    0x260304030209040c0f1a180127080105060a03020d081c020a09031101020a0b34050418050403080a092405060126071808010f2003040b010b0c 62
    0x100700f1000744c0700c0609440c0c0c00c107400c01040741c450b0b281d5580c82d42025103d20b11900100070b0f5015003808140344080100051510200441c901700b20f1707070440d215910300d81909400020052041076000e01440350701400541d43c0b586800c1c40d50300001c185451180e005408000700003101e0045011140c00c03071181c1340e41c80206540d00e03210840d0041c140343c41448140d521950003101c02d00d0755880812046400e98020080740d200783c80d050340c0b8140703106191600016401e20807107400d620000000c2900f8011240d521640e49031442c010490030f454082030490303480fa43c5400c0c1040006504400c1141d00480041e1000402c89560b01d001c0040f03140d00421184920400f01901c20754803010341210380b00d801c082c0d80741e8000e00c8005c80c48519081103182d0084e0166620310000704450b00c115400c2d500510110203070088185e8a00084e400c444440d01030001c91500c5240989554075450010000d080c070040800745035141c19241d002000106000b41240748d040003a006e0031809003048000d0400d00350405070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 912366465 1250 912365215 912365221
    0xa050709150c02010e190608130501180516030302060c070204110d0f0e01020406020a080c160e010305060f010501050d0e0c03010c0306031112030304030c0516090c02011401260304030209 82
    0x15009071402c0c00120f00084d140b1110200900b00762200c0c0041441d040d0b0510221414100c0681780d054000340420307213461304032280f000800c0090241e01228860716030080b00e0f21065060840c00d103411221b926520140640c3c041001907030005000745d00001109406484603a5440064060190050003214401c4046a01c0f401c4c101a9407000095a07503079202048507003036951000d801e0740100c0c0704500142c0c001014850220300340d1001040c1002c202025a07400404015000d140707180d242d0056421803402c0001070041100c10822160491015450302445601d00380000b0440c0c032604400300d005c16202d00001ca01c42208004a80240a00800a20140041c080010300610b050300c0305807030304c505081d0310000c1400d0042c400d105e40710036100610301d903030f450f42c400743c8900d2911007003151240f06078880000c1000a11036a480604a803440c042580454440000c2c255401c0071a1044c4030081c0c080108264580303035265200c1c040c075400201203c03c59003480303036043d40200c0d40042c0d0809640707420 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 912367715 1250 912366465 912366467
    0x1c23070f08190e010b04151503090c030b09060901050603011505010e0310050108280c03020909030d090818101b080909011e0801090809130e120904110306090a05070915 74
    0xb011030321075011b407000c1040c0140083d1080c1009038520407415001c507078501682045100341c001c044140e008150004415a4036a1641004501200d0014130740c1c010030300b40310a40d0020700072290455803c6009001d484000313085032801400d23920a44e03060029180a0b001c0517101071180068054005004118a42e0340d107090903140c8280e4800002603d40a07a10b003114040405008024981c005619101660444d42840f11031000a05028518802845520f50081080c021100c03441d1285500030b4440001d80c0c4030110b024004440c00784160320f85103186005907071043c00030b00a00c0003190507d51031540e078102051544203a05105400c2040a800459101482403c0c003c506220b00c3c10450403607940c0c4480c6080311314080000b003424108000c05000d034a050035441c5062607051100042c0c14000303040c1d00c0d00c0d201c120341060001140101c0d2807480c2d8540b520851a41890000b40700f46546003020000c6c003140b00003000101d565542d4000306a8144c4a8040d40f0081c0c04580728a5480400d6680 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 912368965 1250 912367715 912367721
    0xe010e010b0a1d010b090d0b010f03020414071205060409020d12171b0706020f220501020f060a1a3a030e010c02061c23070f08190e01 59
    0x4078241c09910036042c0021204090007080300c004080c0d44040205908100c1d0010b1980d100c80301c182d600692071240e00c2c010604c40c1000b04d00034080f0f2454000f80a18602c1808140d401d01e5011030789a005c400f041110464120881c91544041090300040381d6580300d0000e4004e028225001c1c5d0042c49000300306003003142c0310b965504400415103a46140e050f944000c0d0000a408440e808c41750410780c100c9440301c0012401801005100300c5026050540b0341c1e0403d50160060200c902400c00484144405000c09e00c0308140a05001c0c03001d060481e000e0741d00310740e81d0000034014403080d640c0e40e0190492002c502e9040c1c001081c0c002d100c1d001102c0c0000408c01480700101100c1c4005040b44c454400e0f281041c4e441c1c1184561580ba03140503c1480001075902c412554020392308500704001010b1202c0711080082400c201e0700c2400900810074080c00e0031151400114508101200000e20202ea03400480449103022949000416503031a1226194410403021100702d0160412a0a94103e00190 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 912370215 1250 912368965 912368981
    0x3110d0b040e01091709041e1a190506030408040503010e1b09070c02040509070b04092301030b0103170702041401090516052a150108070605030603070e0601030e010e01 74
    0x350144440c403680d41030b40d400c03140d40c07042c003c20129501160070350380300504010309074600f00280001403240074030100990308408940881400ca039202c0d01c00c0b000b00024003400041c2c1c0b43c1a296800116182940c2d43e140c0c00701400741034403400012000070304100c54241190040c00c0007800903c1030010804d0215507550940781c1c410300a8030024402d8456040410266105141c02c1d580c2021b100b10640070b00c8020304025101a819004025001c1002003080c1d00802c000d041c0c4050010320020540d0040580c038504c8988100b55014030710040003c56455103c0c141907a8004660010721240c1e8401c81000c0d11401100a400c10309090441302d40005920705c5c81d0403034250107000d21255035001926a10266402d5a0700040740c001d22a030414407004002c1d0140342140c0c145022407142c0358640091405032007031204402030388032200501034884c041c0044c2004183c241065810b600300a0002500c680a500030310001e107142800103010b42c0c1c460340141c0c9514020383e000300441c0c403900301894060a452 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 912371465 1250 912370215 912370219
    0x303060111161502100c0503190b1e1909050103120f020d1b0f0501150509090d08042d020a0b0a020a0f1704080c0901060c02060a0f03110d0b 62
    0x604a1404603101080400710a405002d02e520703041c1c1416111070210007240488070461003104001c40040c10035101d040c0d100d203c5521915101e1401044203800110581019849142840d008060301c1c0c507011946c954a40000c0c015884035142d1740701289a00a0100c0746041400c00241c000038001c14960010341a0780c000c002402028a142d81c0640342c80c01e01a4990707005038000d00c80c41d00280d108204107428140058112480d26a080d1280310185031900d9003650140d5490050040c10105c47c2c1c80c1800629080d2418111407916504454071446502c0415060264500004e41045940e121fa840d2460044848106c0510154030000e8004207001c801c900402c0400008600c0e40d0250003511841825640282201e000c10343d41e450f81c9540c40c513421036100700803100040395408154040d00c040e15409000b03003158600c0350104014944180c0c402070510071600700600140c1c480204030f034003041c11390030003020003820f1000460081000310032001100c2c2001c03034202159030b11504680200602 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 912372715 1250 912371465 912371477
    0xf0614070f0f0905240c030d0e0c031609051b0712080a150b0c0703120804060b19031b05060c0102070204060b0c0c09040305070602071a0a1b0c05030708040803030601 73
    0x142c240281c814000d01e0103100c0d4071030b00b0a00705044220704044504540b02c0301103000c50a021800090038a160091a0341040981d210409031104500c1000300b40303e0f10382d00701c006000120201c3e203e04204d28041c020100d0f0f154481b000182c44102c9064491802070b42c20709070903600c5a6a003131007850401002d4030100091030800204900302034601a0310307501c40803200404d0f070a510b0200e030242070360300c00b59000240b0b01071000e000011601070001142201c0b5552907550300761605d4039044c130440d040c6000842c42880c41c02c01142e0307900448a400015240d00141d000b03c403008901e01817408002a600c041c5d400203000814214004040d0041e207141c03882034809118498540c40c4030107250280512516241d404000311481615101400c150000c2c02400d165203413507400d0b00c6003800d0340d2000300240c458a40140800c50030f45251040c00d40e02558500c0c00300072200c828480c9803101180001c00508110204000b07100740402841160400d13580000e0941d0380c0da43d11441c8a4603900102c41090100d04 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 912373965 1250 912372715 912372737
    0x80705161104050703270201020c040609150801060305031207111006090b150d0507120e0a0b01081c0e0a0503160906060512011e0305100e0123040f0614070f 69
    0x2000b8006c841d100c0f15124002514400c0e089542d88604441d51401e90441c410383c0e04900d138a841b02c0c4190740150003078800218070030540e4500384030610a140e0060f00f0701c0c1c0c94103a00300b0100764084152190b00311720640511143d1214001100c60155402d4040254000e410104a0340c10301d40d40304d0000c0741c000880c14000d80c0d1622003001242080007900b081800700c10001c60094608580c400c0c0e0380251a03042c1043e021400c5400b034011140303840007000182d400003000505024444034030500401c1c0707202c000e01003203c8880e0106202c00c4c14048080c180502d0500040080c2e4841c110300c8040c0c040901110100c4030702c0c400e80030100d8440e1062904040c503180c03000ca00700303101d201200c401e10840c0104031f110740d107003046600c0382404c44894049800e24104c1e020000030814000c01e8001d1081e1741000c1220081042e481d400c41da24041c1d0500c1001004800d0085090070b40b42250340240c010f45c0741400d0061a05065000c1c00b1104080b201070480041001021600039030161503984956540b5030000c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 912375215 1250 912373965 912373967
    0x604060510030b06060d1805010209091b071403090d050a11120a171e0307080c040521120301170c09010b090405040c0e13020414010b0306010807051611040507 70
    0x409400050005100c078000204e06003090030081442e100c11640000b408a0042184041c40c00d031a00111566500010220700074a006c07030429400842e000e800140e01034114900200d103208180004200d0080c443ea00c4600c003101f842520f02c1d5060240c81036030b1225240c40d1150300c9000c561421070344843e00c08207804807420100001d54003425030350001e0078000015101d500207800c1801c00c0000d2480300300100700c0c804441040054038a1620440301c0c0e201e050814001c0e01424004104140f000d01c144000c000702d03628100700c5019480d0450080e031b03100503080702c110308000c3c0c1103c0700441c4441c000000103204211041407403541c4074800556a51320014010070030070314003c0c41038002e0040144010640c03460281e01480d0868811051100040e950710a03200c0d000c4000c550703a0001c4d0404400650960405000700d519100e1300039104a003541c10545041d04500000d8405410030401c1000a05100c4c020000c850111281800407001c81c0550f2900300318050300407440c00d0250b400c18020030111 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 912376465 1250 912375215 912375241
    0x6090e15090402120703081c1409100b01180311131514210d03180807120c061103010510020c030a0206030a020f030109020315060a02060601050306180906040605 71
    0x58034006040014980351070302000740440c41c1001810302d038000e0b07400c00000100d21000820f141554090700130005000340c840d24040310301e82460491503d59440400001500108030306c20745440d1005c0000d032800482c2c0040780d04030b101451110b14909481e83c080140285040005d8102c202150b018102080e4419410b003500d1204507810150100c500b01030103540003e0a8004513442e000d0020602c00c1c00020030f1588503c6200421019900648100c81001d94903014100c0c4a4441020308120002c041d41c03906401e1003100005017220032140c0b1903411652048a0744547c15070090018059a90024a440c0c42d6030310a2044a2140c010200001582800130071038144060005001d480460301c50307024088264802010a07001a90070048071a81d80c0c42c000c055806007130b140000503203030f14142c80700c180b40c1040320405034410641485015141036000400c00c0d40320200780780c8113459843c1c210100b0301c409140c031402c4074191866000c00540c20300004050f885680141c6e07080c1300945442c0044800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 912377715 1250 912376465 912376501
    0x30507080d0516021014030a051f06023f030916050904020d03030e010608010e07090203010f18231b041505090604030b0f0106111b101806090e 63
    0x10504145001c3c01c054a404070303195203500e03d18104102010041700c04080c1030b910440d58440d44036520030a111100b90b4042000118a85105500c03850508040380a1b6958000090311f029601d0390050030078030700440360503154a0000d680d65603c85c035811089070b40f515070800c58500f59540314142c485841c0309440010001110310181c9085050740740c0e502489520010400f095090544030b08070325084200c01d1013040000c118010001410396000402e250824240d40e0000c1141030042c0010722600708800f10140495151840c104e00c0c44095850680c09086402100c1901182c1d034141844144507140189110f041011a01c4e115400035104030491405280a5030348516001c262611b5914010401449040001003509040990f00e41d208014110b0484200000d0400700004200c2d00345c0182244013503082c0b28001c0d03c070040085000318183c400a0701c02a10401c00400c0b01083e4a00608001e10144802141003000b20b441d450040e101c650f844c4110484101080005072064020f00c4440c00c0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 912378965 1250 912377715 912377737
    0xf06010627030c031103150109090212030a05030609071404090218010306030302030409090c030f29040f03050f3106032c070f0e061315051306050a030507080d05 71
    0x141182543c0745c44a004100326101d0b501803180b0141c1110354940c9030015030080c08400d8000c00c0e030f02003e1043c0030300030b03c9040d8820000e03030003404458030322030700314080c0c80e44400b042c2e841c3d40f5280d4590400b15609514031542201900700000c0c0814500c0064000b8005c8070742c4001c04481003440f940044084078918480075005030028001804401d1094000461143c05440700034241d0740c607034417007100704e01a5031000c0740c1e00d81c29140c0080c0900d02e1a502d8001090f10f00100318044d02c0c0c540c458050700400160010708011000403955124007500068919035200c41c600725490f5a0264200c0b0007000071720801070001c00400b0340c0018034901c68020000030b80c0752000182c006400307010340e00d01e50413210a10004030b401000703000718800301c5001c5908001e00d04600100d00e035090200030311802418440e950801e180c200001d190702100720841203804c684055484201c1c00001480b900d0080080340c100542c1702180c0c90002081c81030000c0d00c0e00039111a0001d0300d005803c002c00540e240c0c03181c5000d01d1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 912380215 1250 912378965 912378983
    0x90f38041218090b0310060e01091103010b1606020d05130b060607080415030921090b0405031e01020c1f0507030b011d0d0b1e0105010306120803090f0601062703 71
    0x1c40450000c0e086040d000402400312540403042d614984190391058001102238000d241c0100104d40141c0141e01207a5452280f0910b1541008100100c0b4800c400c5100d050000310304440c5d00300001541280c107103080820007000503081a44051000070800e00c1e0544004140307030081141d03850220102c07a02180d0150209103458a00b810001001c4050070000302072660368a001c1c00441c8848614200c2484ca0040354401c10070400c0e8040c2010440c0d800000000c20207110510003601e00049140180d00c001c445c0c82e055421140a03540680f2a401700b0015a004140035040461050030040800380b000200c1030042d40d07142401141116031944400b030000d614096003500c0030040d98042400c14202605000b00a40c2c03544401404c407030191600c001e00039008a2a0120000308494070340504424070b82800540d24040201c01c0700c3c0c5410310043d0001c0000004a000e20300c040100341180d411100c1500c00640e5140300191590b0b03010301c50307551101e000402081e1075442240c07075201504d920841070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 912381465 1250 912380215 912380219
    0x12020615010c05032209060b07020d020607060e070902040504320403020f0d0503060f0a050609361e04021507081e0d0b04090f38041218 60
    0x44418440e0039405807144d0004116144612080501164101051144a010a52500c80c94a0072142644d00624941c0e1090200000503a10b0325454014a601200c441d512200c1509215004100d070324a005c05910031031800054085181d0054421200100d404100c1240d0345200c0f00519401803c81e01d09000744501c58034241140f107040d00703030806c0c000c1c412141810403036180a803514120002e441c010030808810042d01d071800c4680158690030965480c00c2c3e1910b03010205000c1c0c0550002d0620600d540100c0c084c8410300014014003031040983c07914800070071444030540145040d10190b040030000d0544107a901c0359080c0d914002c5501804020395140b8a0328003180642100701c0403a040d0b5000c01c060b00b002c1e00348070040058200c034a50051b0382c3d0980b001241c4110740300130004078007550038003ca1038041001d42d03800c1c0c2207443d0050080307100c17451340808030303c0711000c0c2030044c5c0800d100c00700c05100100b1001030540d00c598400e850701c0d940d82260200607240d610b050507844065a40c81b03501 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 912382715 1250 912381465 912381467
    0xb0406030206070b04140304091d0312010b030a0212040b040224030a0f020c011e0501090e03180d020d030504031704030b071805060a03020706110a02100c14161202061501 75
    0x80380c5c0d07215004038004014550880384260440e880f0354041d200194880c2d52904403910005007880004112200451070103140148461610a0500c41d0460b18038000c00068040380c001d4040750350240f10048180210301c1c0602d4100700487c0c080d0b078268059440500505000d52440c1c0c41d0002010b01d401d015415a0340d4030b14230740302921042d8010034000e5000d10000307a125009002c2c2044c48005162000d03103001c0d48810342c1b82210300c164813004203282040c08488041c01f000c001c85222100c000c0307140c5015010000866290000d01c04001e4022100d9810300c0140740d8804058403d6038429003502c5072070300d1700d0400c52041c1c0c0280e000181044185901050905010762030090703440050080c0907280d01d980e0781c00100240c0040d130003440880c1e0002078960400031076118081d0038480c12800e903818128410300c002e41d590302c5802c4442819640b82c40a50507940646800700c0c1700441401010360b00c040300a2104a0b0382c42002086880c4a4215a16010140045009445140c0b040000c400181c0c075880 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 912383965 1250 912382715 912382733
    0xd0501120512180d0807020f010f091206150609090c0504140f04090b090307051e1507030e061905070906140a050403020907020d1b030c031409220b040603020607 71
    0x1500282c181c0c0f104840c8901c0e44440554040050140e4461070315007020f8010310440d119035510450410041c8290240303c40e0300440ad0606645a40030317440140402c40c50010b0090045081c0d00d2001a001400010070b5544480540d09481c800c05003031003001c0428409542034080e6000d5070010350741c0c0040801081c1410a00c80c1c8800e6001040840c0700c1d1281e8448010f09030080d69500010f80000031310000340f10041001007284200381190401c0c9445441d107007a1100308480e26041d4400c07280c00880c4459100790444000d040889050314041d0400f12095103400e039500608101580c140750000303100c24064500c2030308844140e15111038074660700c2e0403081170f607100c200d0040c10700c0000d102c0400580c560096580c41204641c000f0b000f40c01e035400001d0070f409001c0040007940ca0082c052080001c1e44803081f6401c0c0d42e03040c1001c0c28408400108520301f8080ca66901e42c10510310000c00300d11400c030032811459070301e41000800c5810031420030f100c01c0d54100d01010750030650400c005400070303100e00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 912385215 1250 912383965 912383977
    0x120305033403020a17060d061508010c02030409060e15150f18093706031a07030b040e07031203090206070606050a0909032c03120d0501120512 63
    0x142080020901c1c0a6690809821650501c1e0010b41d000c640b004d842500102c441103420101c0c0b003403203001d02c0c05d0000a281a40302c1c40300244000c2d100c1d01048c858407041c4509201900f0803000920101c00e12102c025035070740151040d40350b21400c1040024512001c1d03401c60b40640f00113032104042105071014442c102c0c840c40d612040300e25081002c81c4036070321003201400c000c0003001c0d005a4200f005108118044038060425520781080c0d02d1307041c076800310b0f810b0306103140340b00306d0901340710a24480d0303110300200035071741c005409810b07400095152400d070400c82c2449001942c80420100d1015402c1c40215403541c410081c0940c0403080600c042020300b880004401240e01e40458481c000c0d40c0424029003010f034044070400c4d201c94041c483e6103003030980600604018081000810b50341d480091404c503250354081114503009040100c088001039105020040107001c8070780d070144910392040c40c0d910101400c50102c0c079040c004690402d602c40c40628aa4000009100891101844820580c40b44c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 912386465 1250 912385215 912385261
    0xc0d0309150c05100209061c230601021e0a14251703030f061003061a07020f0d08040b0a1e0e090714030a020d09082212030503 56
    0x4100c000402110342102420307029010750354028610030a01d012403038014150740c0b0300c4007540144030860b401d4482c1401e0720b62000040c1c0000350460400c4850100405240500e8030451040002c120ba056a60b190098050700003030307084a80b603401200385094070685107814484240c1100700c90701d0200e00e491200411240621042d91702500ca034200a80001140b40e10168018914400400070840c00b1885d031803605209501842c51880c01d182e880381c240800806582c4522140b0098800c91031190b4804c60281910640c192013880200c894030110b0313088940100d108051207080e01d22582442a0034032546030341b165407282024103224000c0e03003a0300681c4464040140042a409200c0d2107918910803d01d481d44440d0309416841041c82141140201400203020b801c00c0d0a103a40c402640840307600c0302d0130010040c0c6941c510407118002d441c6084d0040c04006010641c842c14a00d00c403425035061803c900060100d5548143d41e0003120112400907001c528184009880041d03120041a0784203a4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 912387715 1250 912386465 912386477
    0x303260c03060607080c0d020715020312071b0c0b040f05010903080a110a3002010b2803021806010e0d0c0303031802030a03030b210601090b060f0a0f17090c0d03 71
    0x454a5514502041d0203401f00c01a80181410407400800107004400c0791084d201640c54a0894042d18481c807901814a40c04c00c0112a100200480c440b0306e21103805500643c1c000d200d560b101da070070f1140d4110307000341600c0740447ea00014140d0300441402080380ea0019085003000c00c0c100e015504854034500b0302e509402000c0240e0001405003511488098040e0854103107616004401d07441c03142e131328495109580c901401c80c01c060340c49040b0200100200107107000c420080781a04140010031ba84000e4003d1a442c01c1001201400b90925201d04000e07603902501003032074030420000450005024120001c004001e20201b44a6003100007014421147d60000624079070202c1d191012004099000a03034500c0700c845036240000c444100a40034581c01d400c510790010800c3c2e02d400341845541e2480c0e80c1e880c200c020580340c00c0182c1e4041c800010007580c69000d091000b800e8401601c6084002940121f903412072a1000e003400c9000d0a8000c0003401c89a59105c140000c1014011003907042c010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 912388965 1250 912387715 912387727
    0x302270430050a0f090501020a02040509030c0706091e05010c0f02040b13021201140307090b0a050607030512010905100b0912010e1f02040e06101202040303260c0306060708 76
    0x201000076403071408a20381c0c480d40d64110444006040581c0ca001050030020480820050360f81d00045036050160104c0700000c454503070302203017869031194030240d442d81d001b0303c030000400c1c9070804520000c45100c07100d140603070381e86c40d43e11460550303150051502160600c0c031f541000c0780c04d090918614074406040080c460111400044004010074058030b449034001480c500412000d00740d0b1030041413200c1d0701c020305104410000c0d4482c0000c0c020415440c0e44d8040b0b941c103a965620076980104000f42c000f035600c0c6c440d409c00a146a0007a00c4c080c0d448943d00b00005881100c174490180f181280c201d484400505118400d604d60340403440c80e950022281d40001803410082c410700951f2084d035002800050703100c80c030401c04154680c03040441144184001c000000244d40b800c2d45c82001250300d0940251603800503114410602d80c2204450301c08074012003015000480c101c1c0446540e40c40d850301601500c0e07614045038045620315042402840030803542d080c00c1000e084513904c10f818003802d140d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 912390215 1250 912388965 912389033
    0x5070503031b0f011b1101110d02120705070c031103031317121309110705030403050c15190f0e040212011d040b0c1c1503022704 57
    0x504010411005400004000504864204415225507410390001e00c00c503504000005005419032040501b0f10079000c001101211080d800320302140c07004680161070b0480842284002d4000c0c618004244081c0404140c0c83e90052095603046a0301c500300c61002c80c2559201d1205204a44d4100d41501c021b1003003039042922058100060494070f00003c00c081150308003645000320b86040e288200b5010441c03d1004820300070000e051310b04068022800f0f0b04400281c50b12441003100140a50001040100420002084c0a0405041168061000f0741d00180b10181803280c0c4620300408260900d560b41864020303e030b00701d4500f801c1c0c00e12195900f80c00303000c07400340d90102846201081c0100b0041c4540d10041c400c207050050424203600c09490070340e0311f00c200780d24082c207051100140030418800d02040c0d149041e1081000002c18400c01507070b00307048400d1140c86c2c003040780300d105c100c040a4901031102036180b10501001020502a48480d207074000c1910902c8100004400500682201031f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 912391465 1250 912390215 912390217
    0xd0c080a0f0201020d030207110d0f05060f0a060e010e04060b06041e0e15030304030f1529090720150702070306051311040c09080f030909100803160507050303 70
    0x34020601c405001c440340c4002418402040c460b08103040c414040c0e5000714050710110500a441a5610407120f13859082c903d0001c09800c0c8002c0c814403c07601000010f484005080e40207062890060001c19101c401c45022141d0074010001824809000500890016040683d4441d00070b4103d5107000c0c2c4919585e441407407020b80f01c1000000c0707680e0400030600050f811592040103001d201c02f01122188c0081d03203901c074600c4050184500c401a0606000c070340d09422017840c140841c10080c91b50b0401058240320b02500c580911001800314000d03071801c0c580a018491003140e40c41994200c0e60791641d082c1940340040e8a81c00d4880c0e00d0684854081c0422010300494182d0001c1203c54514601917083c0d96008200380880780440105000088103140151002eaa048a021078903024104040f24660401d0344094038070f02ca241403902c204000800200a032000c00e0359101c4840d9246540c0c40d441261501c075000880e44100507000e80f0b48426440211002d10032070a0300c51242e2344800280c65 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 912392715 1250 912391465 912391483
    0xb0c090a03051606020f1908031023010e03010b01020618030c010f15080705150f090a0605031f05031c02071d060a0914071b1a0726060d0c08 62
    0x10404420418404c43d40c0401c082400b14035400001e18056031203034100c10340c500d018007004100b0724001c40410314138034091034031002500301202240d0640008000c2c03000c0804084c4078180c01300d080641c54414608060184000035403041e0010085034445141110041506400e000094003041c049509088000e000d24451006011800716182030021a5502040e4699204c16020b90203801c041145d5203980a03400300c8a944001202e0301d4480040d00c03445541b14a140c21540300342140c602080c05904a40078500412065a07003100241038224070104101d49405066410f07400701904161401444a000340c6000d2148107580207070b0340d1043c00c2b045494207610160036650000c010400c80b0304180c8400c0006000308a418000b00c0241440c001c1c100a010f4001c204108a0400c0d41c0244040c010044409030391003040765002100a1406c294556429101c01c4001034004021804a10030f86500d00201c0300c1d1071001e10216102c001c10440e102010103c22220302850301d500086104048c045418 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 912393965 1250 912392715 912392743
    0x15220203090106080c060c120f0405120a06060b280201020909130b0c2104140f160f03030807051c05070806010210051006180b16060b06070b0c090a0305 67
    0x9000b13081c441076504006046400a00495042c40620084c50000400c1894401c61901007541d9044900b21f01e80070780302e103070031040d0803100d41000301401da8000181c110001d13005020803c0306036241c0b80100303503d1040440f12080f405d040910f1008054800e16054040b02160000500e0007250f0004258a107008032105d0202d01610511075061004500406902104000d8014074001342000380c4030720f134401990011400d466500004081000c4140008401c244400c00c0300d0f00c00d80301c2240b0340d980750300d980c00d90304440c1d44482c1c2c0014110010750f000b0059076030507100c26045594032042100d00b60020f0b10003d4403481c101d2400d00d4080d0f00c41c42058000c500680c0c500e1217502d0b00d42c00291501c3c0b07001a40c00b503014581010440030b1201030645109907032052502d004040648001c1c81411101e6400102d4040030000f40305181c155001e030354201c15803068078107000241100c01000100e01802101410f000326031000910035050240007050b404900420405401d512a2200d03403600c0388a24141c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 912395215 1250 912393965 912393971
    0xb030c011b0b0915280b01200706020708070815100b04060c140d1b020d06020d05010302190f061115181b060703201207030e0405152202030901 63
    0x340b0242200324200d6401013445e528440c1680c800c0510600e1074220a0000d40c8540c0d03201c00b0400c042c2c0c407842d110401c201525001c40b15880d060852103480d1300c0389101d0304004d0321074030070300185002000c541c0b082252060400b40c13120080e0b0040c0501140342c010141d05140848940101c3d100070244017410103071031150f440d0094201507141c150114a0b100c2d28160041d804449001d1906600020042c0b00c0ca51150406525469620101d00c1c0c000b100c000080c851800401c0588d980141503020034100e07070084030520083c8003495680007100c407031801500680c21b488072042c010f02d4041e454500c42d90301d81d903089030100a2030a6010016403000d6814422840701c20b14400c2d140c01c010000351800c0c140040f00070f41000f41c41000079000d40318800d00202840041c1400d03100120808540050359100307807041d81d4501445400408140d40a84170407000b048c9120031890740340c200f40c071603203104080300b0418508440078001080750482c50401c03070b600940201c1d880034150070300c10300145014611260002c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 912396465 1250 912395215 912395233
    0x60302030a051f05010e130f050403020c09090d030207081903090308060411040311040608060c190806030a0f0206040906060c0605130b1911040e07020d02010b030c011b0b09 76
    0x40203546002c3d000d21880902241141d603007000312403074001244c0707003420300090701c402000200e102105006581c0070030a1600400d0124402c1507001544142c2c8a03909903560810b1803810064844401d8520850f00c1d8400c0300650780450081d4002c10710240914213183c182407280c0048002c052854a03040006501e82d40008105600105001e40020040324148035010100c0c209114501840c4005420f565000c680f0501a859541c85000688050005c0d54414900401100d8036540240d0301005032540c0c000c00041240e216030381150040e040180540504c544030703258079507a04042942680d10290412000039804010f202e408010102c44d05c4c1c014460403241011070485500511034064440301007882c000060780404220342c0300c402e44012031b42070640e058454004200383c02d0007030990340c4002000700b0b10342d42c810031140c410f09481e03080b6000d95100b00c0c002c901341c444020525405500c0300b070f281449903016100700150303039103003034880204400c09848602120304150b0300c50300306c0d410410039 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 912397715 1250 912396465 912396481
    0x2010b0405180a03030203130209090f06090d0801030308040c5009040f060204030b040203100b01020c012102070c05030607180b0702011b080901030b0d08070813030c06030203 77
    0x54241c2c00074414680d0801018110005519120140c800401301680040001c1e60100c00c6126420b00039006020211a413a040c0c00642c0c3d00c0c1070803100340909100b0500040d408000c000707842c481032201c60381c490b0156461aa419141d1000c081c000302d514000700c01010a2504074806021071a203805211040000c0c164041580507243c5803000d0010500480071400d854075001d80c03c80e20a9009584030991540e03181017024282d03400c08002403400b40002170010034800ca82c42520300075070086094680031000100d0b503030100d0321311907201400741c1c0113800311042c0340d8000c180c1c6040349a0911000c06202030a580900220b03409048100c40e2104c1200060003141010403440340e120707007e4180074500b10700742e07449074264140700e119007208071000240c14001c6921402d00054400d400010356038100d0018a00202d054100042d61030000c1d151094558880c94590080c11266400c003220602e050400d8560324800c0c0c2c00440c800d4102c60a100c0e0001c0040d51003d0f102004016540c0c00503181c1c107103031070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 912398965 1250 912397715 912397721
    0x50604060c090e010305032514030d05090d0801050f0d0b160f0f050412030302070206130e06010e0f0913080c070608070c4206170102030403050a0e03120a02010b04 72
    0x200405014443e001400010000000c84120f40c01e000c01c414540c0091240d00580c00e5002c1c1402044d6941003010b240000034000302400b1800598103007844240e4900072559590307111501c0000001e8130100042003281458054141010380c0648034214441031619081d07030903041650f1b00c10005d06492140030f80c85074010114214104103240c00d00143c014040020690302403401800414402d80d8800740030940a40c1c101c0f00b20a0b0302801c040c1d02c8441c8410104408803051182d0203a003440e000002e8001c0d841042c04034029140100b00240f040200400c0c07004010000740543d604a03040c00107100410f8954015181d850842802031000070306281c00200b44170806030180050110f00d2001400040c1c10f55448070610080c0c5202820a803c100d0070884010140c4000404144500341c190030180c032140c1008003030741d000310f51030144e802c4050800303800c070f07c000c54018002079820b00045800070301c241c50342d00c100c410080403078000c40c020034040d5070b15911103107241e00035030342d00d1514a0003418240 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 912400215 1250 912398965 912398969
    0x405060604090f030f1809330311270a0b011b030513170c0a08070b0f0c0a05030f040611151501020a061d060c03060a0303050304030309050604060c09 66
    0x600d00344a888190781e10301024034000f403401024170841138400e4000ca0b100d1903c0d00e00d080480d80d6880300441e80c036580d0f54014194807043c88071910285c1901075000c4ca10581202c01003c885840200080c50b54403180c140c40d108084a661104d0003488080801c50002424242c40803400c102d501142000f00d40c80302161007607941c540c10310aa074056180d001903800049090303a901400c016a8900c5441c0ea070014803821074008240341d1032001c1e0394981900d40085d107054002016600300d42c0c00f507110405580d507601d1a1098211343c840c100140c00401e4100d00141010040e0301045030784403001076071001d084d070308407009881d01070102203002c0000d540e1000d1601414a00d6001825218042140c0d000c080e1900800c441c0c41c9030740014110b10140d00c2013000303054150300b2402c1084901040c0880301101d01442c1c5104071039104660204040ca0185402c0381c0c003c80c4020010f40c10b241c6960380548003034000074002c2d020305580304c03100c0c4046041408054480c81c801d8270f000401e846c1d81c0902034400034440d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 912401465 1250 912400215 912400219
    0x11102c04230f1e180c15040602010606020c09060d15020703030f1b080a0e070803070c0e010b341b0302090a180204050907170304080111070203060402090c0c07030b04050606 76
    0x21541e45000b45003a503000f01d801c000b440c00aa2800c00401c20118a0548201c6055820036038612583c462260b1840c00f900940d48242c0c020702c1880c0d82e80c40c0480c0d4546500b00301580c0042d00071702080c2c00746042d15904c08014440c0c0580d0155a0f9403483c0ea8081740c0107180154003003600c0342001c0a00c0400c6210311100160303c081440c801d69000c200003860390030018541c1015940c1e89100c4e042c4240104040c0c40240480030490340d84408503d0b01030ba0807201c0d1f104841003441c2c040000706c0c480c0c0030701050310000c1101d43c8102c0e42e0340380427001342c140c5a01190f00060321035101c0c0140101090052201e11144801034081c0e803103252443c418404207010051201e440c0e145041154020900301c4801c9520b43d07901200c000c9080d440b078018840c100203c0340c0c0044500c10b0a0340c0030001070b4001001500032201500d008021404406081d10b1440c450294000d600d50404800540186051004036030070600c1c6190103800d01c002150729504e010b440740c01c151030046d100e100b0001088001c110b00f543c06081 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 912402715 1250 912401465 912401491
    0x705011803050703120216061b0807051c060e01060c020315010f0b09041b091d0415020d06050a06020a060506040603050c0d03030e03030411102c04230f 67
    0x1e490041a80c0103100c0d0042c20045d4501440d1450240c940641c0c1387e05800842c0da00d8a10154a0710074024208500306c61200710b80850b49030301c000d02668103680302d81000d80b151450112060b1211094081d02c000d171502d20740e500c4001142540f1008586400b0700100c0d21984ad000000e8010580781410000e071010f00008204018020a0225140f0300211111011826100c050b04030000d800341040d680d04881c1c1100308140f0040340d0398804156400c0b54400174000115100007034842038200011076018010108001001c6a5419252700400c001c100070302c80040d04a40b500000380500203503502000044e070040d500070050100c0c6200b01a00318a0480d420032003d491566440d40b40d030300290710241300350704440742181418000e8100301c10342c08a50054958034035081c90200b510b11801c1d510540514081e00c20081c00500503440e030401009485a0820038180100300c106080d500aa13509400c10b032170388424030b82c40c4880c0c480b460600011402d106482c3c6401641000820f400608204030303a01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 912403965 1250 912402715 912402761
    0x1104050414060f060f0d0203040303020912010911061b0d0906030606031803050702061e2503120e03210901292403160206181203060a031205070501 65
    0x144408080903160070954580f038a032017100c86690304a0041010000e405030000040004241d0325a00400d9112000c8403001c800149200740c0e1403c032403107035000030b001d106a0481c4829514121001c2c0c6645600007a90b0520480f030304600f18100b005891064020582000c400d03c2029014000da2010348070606d01002071002020b0700c07000b649104003001c1e01b40305d0700182001c00e41d11454115011295051101204400618014007455029401d01e02c0c520722000407c2801c81010f074181030301c2d40d8141d96108005141d001400d40140482d0440d8000792004001c02d01a0720702c200407026450382d2040000c445482c0428041d400d6440c7c441d1800745481500003080203110500800c141148010f884540300c030544000c88480b005401005180c0c0c0300c01c04000c008020201a4403440408015070958515844680030f070303803d62049960786442a0090548505801030902c065a8041c6c2c0040c502c0004565035210088072464000045e00003035800519203003408000d010b44005604a22018a0101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 912405215 1250 912403965 912403969
    0x4110a032916120f0e1903121815200408160f15121803020d181202030307020a06081005031b060903010f02030c0d0b06210403090801110405041406 65
    0x55981018088240e0f07111400e980111310303640400307030400c4440e00b01c4074900401c0182c2c0702d18603500c5500710700044076200b00410a14040c060551265000125003148038182c2da101034003000132030401d00303803103940b00003400b00400e200400100303804440900c20794a82c1002505802d0a0720170a080c0103400e80c8402c2001040c48002c1143d0803a000c607200c1444906040c0c800300c070039240803242a1941c50804007850242c0c501182d019020510035000c494440d842d90f402544d01c01c0400c002da0b041c158020740c040000c1405000f031000810302c01000c0d03c1c502645070b40018164080d43d00050005400c420030031503250b40600340ca802070941200181a54100341d001c1c041c440c4a8059414010340020420000d1910250000c140d840071110341551249008048545030750000d0f00c1e00442a4240325413007859013028030441d07800306202d103074101d40708030803c5c42c2e1902c0c900c001e0401c404116a41c007000560820070300c01d414145a000b900035589034582001c001c155410034000403568030144d42405266 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 912406465 1250 912405215 912405227
    0xb070b10050f2e0306150e0f060c0109020402030f0907080a050d1b0f06020d06290a0504030611030411120718020705011805010e07030b04110a032916 66
    0xc0e0071511500b022902061849403400c800c40c0040350030f0302480f41e0181d00e94168000320b080da44090f04054444000318012110212442c40c41d0740c00070030306600905541044070040000446140c00070611000d29808038080b03a0040741d2844038590880d06101c01364030103111080080014000400c0c0c41e00c080c1c0c0340c942d1542100e00010050040700710340d250240070980e01c0d001600781c01c40884960030602d428094003951151032081c100600e4400b0105642d000440c84540605002d0100034642d00302d082c40d074030320354410781c0031174180039050100000041c90740c000d100c0281302d80c8451548a080c107103084510030400c0314800d4440daa0342c003070003c911100002d00504807005002000300100040380f4450080c40741c0e81c005411942400c031040b1804c40c0c00c1c2c803c000c8071403050000300100d0403202c81654468405e4000141035942840200340851170081c60100c82400c02843c1d20700e01607032a034940944004801c1034036045808a0000810b10a4407002a5840001c94003500651507000d0340003010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 912407715 1250 912406465 912406489
    0x8120307050d021b0109050a0606120b0406050703091e020a090218041d01291503150102030d0504050c01110304050607083f07030606090501121103010b070b1005 71
    0x1001e501180c4c0103000072070019505162039141e402080280300505000e071701c880c64401c06882042c1000000183d40b243c0c0c02503002007035000f43c0c580010392038a5442c107015140140c03a1000b019150002200800e03c40460305c4400702c505e20b891340252403144140001213009501601c1d01c2c41c0f041c060686e03c040603142c0c105001404450005080130a08a10244440700c07024a030507541c648800800b071181860000c0d8002d40920390714118001c6203200f00400714160b04a190a40c00e82400071480c0c1e014244840070340000140141c074180000070151004450084070103035441e0784080d80e444a5560403d0780721150541d90f0f809903113441d0034007000c24010320603200010007400d07001480118100d030f120346051500c0700c0038446100c2c5000405103801322020000c00c40c0d104990540c042003800d030083c45248102c072a41e0f182e21840c0c130720344401035551a0410750707070f403502d16204c4a00302e1038109408000c60190a9180343d4546550050405452100c0f0003482d815103000407010910603981c0d070240c071145d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 912408965 1250 912407715 912407737
    0xc050a030f14240d0c030f140624010311030129070c0512070f170f0d110c060f180607081206010e090f0a020a0e03160812030705 57
    0x182045601907030030042c800600c00c80e00407034210051200b0920001c044030203e91407074180ea4030344003980c010004800f0403a54010141101081c04100103a800b0380c05154150040c10b11402c1c01d00c0c040c4500f42013039401c0304d030515102000360051540102d0021500165030080c0707820466410000c024000510040c0105a03510000c604001584200144442d5500301040403098507900180380c01140300c403040c0a850700c1510349008a1004040c000398203422104080180554103140c8031541ca14102c2c0d5a080146c4c0340240c5680842c0b04e5010014900b14625555400440130f424810803170410811461a07841401c0070840303d0402241982950b01c04130040a0300324007050381500041ca148a01c40340203140100100d00f040d0b5180c00c4407001c1d0f103d403d0a881c0c004200b201d007810007640901c211441003e4103501d10200318130100c181c1c06041c4842c02c5041c2141020800c0b00040d2804515030000c420b001900c2009200082c0c0600145891a03044413800b4103604000d8406041e500170008a28 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 912410071 1106 912408965 912408971
    0xf01060801060f230103020f12070c02030d14031f051207090f0204031208060a210215031003170f0f03090c0111030d05130206040f180c050a03 63
    0x3d036003090388400e80b461303c10741001580250003515a01d410000e09003c0703090003141c91010030740101e115844087c1c086859104051404150b000c2150800180d00d00010803601807800390307508240c055002103c4944406101d0701070000c140e0106520240d03113a00680c01660200b0312105a5003107034024801840c035a82c001c01644541c0c8401810b070140201d040028911a081e0682c0200700117103102d07440b27a41ea100000ea50740c140380d00111940c0b10007034020114a1b003504005401904400d40c00e0a62401604c0110909400c2c0300c0030307010024031144410700c0c4040c2400c8031002003ca10340d980e10303800300c10001e07020368004450880c0144620707607094071030398001e07140c100304465a4001140340c4071032000f20384d010344401307417066007406040452000141d8807003001c1c001410400400700c0c00245010405066000d136203868031000d0346814415407080d03a00108981d60300210381404 = true := by decide +kernel

theorem cover : BRFrame.Cov 912230215 912410071 := by
  have h0 := BRFrame.cov_init 912230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 912230215 ≤ n) (h2 : n < 912410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
