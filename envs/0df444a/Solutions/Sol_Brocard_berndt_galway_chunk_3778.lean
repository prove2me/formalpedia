-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3778
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:38:37.855606+00:00
-- url     : https://prove2.me/submissions/163c1629-94d1-4658-995c-24a914191594

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 679316546 ≤ n < 679496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 679317796 1250 679316546 679316593
    0x170f01060807171903031b08060604030b0603122205010c050a14030702061315080c07021c1a1614040920161e02091303090f0305061602 60
    0x1441c0303c041d081d9400007041c0000710b041514410302203a00710061800078010f0801c480d500d00900c1044480800d5948280c803c3c1e41b180c035000d4a03507450581982c40d0b00714201d2000341300c15454460401d0307175420611180003404662481c0c2c2d01c54110740d041600f402c03044040c580c01007810402c40000c481c2c041840003a180300c0e4242c0100380a80e0844221a0803401d61203903807000b075001480020b054495148030031511085038901401e41c040d8400c0881c0c02c4030351500507151050200401c0c0400c80140c5420a00c0e0142d04003800000c08404c4e4841e5a000312240f20b00b0701c2840d03003804440c10000701c4000140318204800301f0380f401c214120700c0c0b07414a00b040c0c0100d0041e212002e139905002d20044070030450701462000510a10360321106041e00070804080300070340c00c0358560400c0c107840803840c2c0c00c107014600c01036004004030496503c806800322191140c0c901542002a1617a0000e1075800d2034800602450040005e01940e00e08440b241d125042c0003221101154081022802203c80101c10080e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 679319046 1250 679317796 679317809
    0x28090e011d0a05060a0506071a0105010302041d070e0a15031b021504050c0a0b0406021213210206181903110909030403061d150702070605070206040b04170f01060807 73
    0x3c0c4a0f25a5404140041070300e07004250052000110041405100700f5001e900316045144201140c0c4c0300c0c40118240d0050b4440d40b124400100c41c1c44001d480c4540384070343d0086036450021010a10540003e06500ca43d6200b440c03044204007a5550a41d4140601e20a4090001034132010f8001d0b010001e565068410225060500301c402040810005019681d15481c0040040350b8081c0c8070f54404042c0e500510503400584a44040b00c03940c2d041110946080c03900c1180b00c421402c0c50070015812414107800d4030f8684e5420700b8030a40050f510003010302030414558460143e51954282809082c031585801600004607c400c00c0001070804060360803c41d0301910030072502d40301c1f031990b940707503008641000f0460360425510955010610110341d604124280444103140007040800d40e410006550640c0142c010001c03e000440c00354000b060003620103820585801c3d43c8910386a103641160300812406600c240002c00042c404020101c580d54494008000c1c0c6442c203101b0035510450f41c818038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 679320296 1250 679319046 679319051
    0x50106051b070b0304030e030609061306020a02010216061e02070b0402010e13060608040c0605030915060307051c060b030f2104030506090c0a091e0228090e011d0a 72
    0x4581c0040c030881005244201c04107840303050502c1c02412041c81007510901030312030000018400301000581c00d00590f00010500c0c0c801c1c0c259284c003006944520700c41d1040d59020002c5941490b00400d4841d06103001c0c4000040500c0d01c3c0e11039001e000c004044104681e40103006c540c000c04e0390310048680259090914980070075008010900c018005684114824601075001a1080d00025884c1c0316920540300c0b4040c00e511400c082d2214041a01d1050981d800b4150160008407204480c2c3e0b001a80141181ca0781c13a6644009585c00c800411451903895400368001c080040e503015018a101d400c42c06840104003c807403d503501d02e203069a0543c508401e268440c1008410710032940a0358000e403d55280e4509640b1246d56440351480b018002c9280030700011340c80202d841401141c029801011903040c2d4010035030006500100042020000c2008504c50940454860240c1118240e00d64100582c60040a0410810142c3c07120610303c1494110b510903c0d50a540c956019511300d500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 679321546 1250 679320296 679320337
    0x307020a17071802040806070c260f0c160906050102030703030902040f0e03070b0705041214030c0303250507030522090608150a061d0403030e03280305010605 70
    0x4a02e03028881e0701c40c860650032503807445803002d4141c000b0401e40e4500000c44106454454003110103814504000c0d000300c03490722501e48902a446c003000000c0040c40c0c0e10034103025000c140c2940590180200b48850f0703018992100c15818442296401010341c1c210401403d490080080c5d12132003410001000c041d9101200e070708541c1c5550003902d84091840003048480d1500c80000d0342c903444110150f1301820b0700400100507520910445041e00c2803030581c050541c05a54402035824207010b286049400180301e03110f55540d00308040d51048480300fa600c1d0700e07200b411280005680c1c40c04001c10402104110038004250018121043c00307045607003070300c1d100e001303030301420340c16025038003d480c0d03040c104600014255000507082e0a04803260340c0e07041041d03e8814000c5c2c101c80440c030641d0414104134004003241e50b040204554400d01900340492084885400103086901c40038104100090b225030144c1c03030b0b45000c0340c5c85c610b1032110308040200d541010f5020b001c0340a50038400f4004074140d40c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 679322796 1250 679321546 679321589
    0x5090d170708040b220627110402070f1a0f010803132606070f1d031203090312090607092315041d0f0601050313120c02210607020307020a 61
    0x500c801c0c4107000c0c00d070814003d856840c1800160412160154010484089600b07c0d64169442d4100c4c0541c820940841c1c180701c0c1c020301000e500300c003e0964400007c9850000401d00700480a0145980c403000f0310240c0c50910303041c214040041e041008140e00520881d0892469540e80c0300039503181968121211040500e859200e001c40b510207800e41c00350109000b22140c0001b0700c1c501c40f81c02c0d038031040d08501000281d09411002e000f805940343d402011184400303040d44005640041001040d43d280c04855580349054140645d80d29a03241e00030ba04110640d6800b0224070058410400d440300c03102107140308202100d0106204130700c20150b040b94800d8480e0468120b5004100600a40900310b21040c404100c0c0542110410301c180c3c140c0b800180c0540c0b2603400c5a01c115a80d03424404921b1460700e44c05803042c414082041405007500c0104050398600f40600400e26460030300007550110005050b060141c00341c40c450541d4014802180181c0d80d010500d07080e90703041290392512804d0500d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 679324046 1250 679322796 679322821
    0x219110d150903031d030903060115030e0a030804050616020a11040f060b13050a0b04090b0607020913110a120321020a090e0c03010f0302060306031005090d170708040b 74
    0x941c0700d40d07414540054002015010b4220382000800d440003039544d00e080c0d20a0589070700c280c1303003616415000302005115018407080b8642d00c62600345000182c04002d21041e5140c20f802c04400d4000c15404820001004030400481d41d1040003405e1028002d41d00704000b95036a00c048030000c3c980785580d990319009440d25402002c54000e803940603c03a9030340da100790f0b0025503c501e01d00f210040320031101045500708a000340044445a040031850301e4506140d05004000000700a580141c0030030032b030130260341c801000768055034074200c0030ba6201d01d662604488003c03244600d580500707032508081140d180c11a03400112207405041c203429500035101500c5800d4a009400345405101040020001c5c1c2d000607003409440d0321100000c5e00b0744441c00109540e0100740304441c18034881c0d036000d10040c102140a15007103000501100e4201c0c002c0104002950b004541c1050142d002c1072003800315030b42c0910707000c3c035441d40c4922804940c00d1881e0002d01680e002003002d080303d040440071612000303615 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 679325296 1250 679324046 679324073
    0xb1608090d0b01060905010e0402030106080613060e040c23030705040b060705160806100e0604020c0a12030f060b03160c1e0308011d0618130614070219110d 69
    0x20440c40b0700c6603102c80d000360103c5268004c150002c0c280510b0900c042c1400e1003200c0c103031080c9031a40740c0d042d070b541c01c1040341482e10204440f100507214030700040d6a2829880d0720f401140700b0080c0c1c0d0032950a1411401c006005016140845c02040e80041010b40b404154201522400d460100b40d1211034030100d4900d2040c00f100800520030b20b8541c003400130307240720041c064500a07400c0d9141503c0f10a030204034101c4a01502846906480105107545459402481000c0c1c0c501d05075214180240c031012000341340d1400304000301c1d8480810407400e40440c41080041c1c008000f640d8110304081201410034400b10802c43c090182c81c400d10b4090000740016140c5407228149a20b40c40c404910b40109200420701c1120031841003516940700104540150501c1001c0c0940003200c0200c0c0c05c0b009501d0328074040c250f00c419580a40941c07000c01e03503c0c0240341c030095060400c2e2041d0f0a004000070310300b0b05d65001154408801c001040006001c1140f5904800c3c000c0b103001c0255411070800c0032011210 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 679326546 1250 679325296 679325303
    0x5030609061f1b0209090109140f0d0c0204090b0a0c1b03051605070b0304120e0109030f0215040503030f0403020a0608071e02030d140604050c1c0f0b180906010b1608090d 75
    0xb03117410848003e00542100a000c1c0c0304510000441c0440501199244001241c0c0401a080145030f0309801d40302d009140c42c01400100b020804402e0340e220141100307410385a9020098441c074509401c1500060181e09403c985605800c0c0e0039043d03200200b07280141c2080725501010140c03640203201d001c2210001402c000050f03190360b41410b00d440304505070100d1010002c6200c030701410140d03600800607031080b2504100c008081e030041c2d03420018070845280b01020191818400442c0580f0104082d01013040781c002c03255500c90079030041041c20301080e0b0140c03040225440030401117940c41400f000a000000c050340c00740200344d031016030550243c14106000c0c6441c0c1b44600002c00c00b0505414001c0d902a0350410654582000150b51481000c91096800d810600110340c2c984443d0300c10441c4144074072001036658000000500034103800818040702c5101c01c010b02c4075680046c041140100b5200f1140c502c0e0000d101c224034190b4a05141c041c00d480e00105c0c080e1515255000d02d144100c0d0b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 679327796 1250 679326546 679326559
    0xa0f05030604092406080a170318010608160b04061b08040306051509090c06031f03080403061e0501080a06090f062405040209030a02040b120303040305030609061f1b02 74
    0x12120301a03604d04030b650382d4444015003003a0300000d4190300811003c80e515045050300d48034003c00d00c0700140303d0348050002c0e2041c000008001e0044c40c8203201d000c01030030070b0328042c040c2c0900482002041c1726064001c400012420403003002542e401007615201c1d510b000c01440c0c80140e040c10240c400340a69031020b0501402c00d000c100c0c869900b196808184002200c001840c0e031204042c5039503d030515904141c01607020800b14546203000141d800c0c3d60864240d9940b0502c1d100d03610b5940a800c40e61049425546500016501401c003000010300c014a071303503081129624000e055503587d401d80c1d801600d102c0d83c03181c81005111440241c40c009940205041c00414109404610b04a110b8150343c0c803000340044010999160038000c4a44401c1c000f0010416620769408000040c02c0c503080d01d55000403180e04680141e1302c21701c007540c41a030180e1640380d160b10b8200c1c05e00018440003018544a0300c0304d040e07118085010011001040c001c0703498803a900404180e400c84929400c4500030350f0100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 679329046 1250 679327796 679327823
    0x5040e010b090133020706090605070c0e090f0f0a060c0c0b0f0c04091e060b07151d06041a010f030b0708070210020d23010302030706030209040f06061806050a0f0503060409 76
    0x145c001a006007191102d94400d00d00719610701c0210b40f0b40c010400001d090010500d82088403480c0700c40e600341c0004820090b00d08c1d08a80c2c10610385003811602d1020640d0700801003a0061040f14400c0707001610b0740c3d01704804458002d40c0c2e24034490700001d00b14040c2d0010503001ca40030700010000e40c0c000e0400001c080041c412030305201111202c0012403003210f5401c00c074000c074020403100107a607081c0d9488500b0001450001c001034016010107002c0c91002002d03a16120f0403410100591400f03a80540c21428a41c0524050030802040503000580c54261482c002c100054051202039031201c2145052035442d22a000c0072401d1000c0b8918031054180080380050060300e15500c4918003000b0f02044030b22a81d826074155841c0102484040d5040c3c103c000f040240300e01070340007402484402440041c02aa01c0c04d00d41e81100d81c190040740c0001c01c0783e841c90014010100d60200a00756600f04142000b234002401050080d000b280344040001c013102180b8640c0344d941040c00c0d0154019848003100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 679330296 1250 679329046 679329149
    0x130b0702011d06040c0f080307060e0c1504170106060507110103060527060405090307030518180105010e010c020604150e060c15010b07050706030207110a0b0405040e010b0901 77
    0x50b5000d40301075840f40e031a0040050380d511211b80070012107000c54041d41c1005400c0d1130724402091030504540c1e140c000c0c1c800f100310075078a8074a02c80166040b000300940f12810038008107403400200510b8010743c1e240071424001941c00c04152070245a0000c0703e10b001c03c00040c0100c000e0074265100603000301c01d40c5015001d40d05803485050b4005403142e0414010b540d00010042640c0080c1e030a64070b140c000300001c9001c60322a100520540701c03598074615481d0b9260000c282e4103c4043c004e200703000052801030003203603480440180510f000346811103010080e60002003140c440c0b0700c22000f40340e0030a205081400e005584500919600400164646a65101441d10342c030480f41d002e012480da2800105004082c1001e8440f00354108005105490624034150000e60113002e05a500003010320034050382e5520182c099014205880016032074a1070071003844151800d41010b1441641000d1510384140c8440503014112628420401000c025003501904011080e2100302c40c071800715110500321 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 679331546 1250 679330296 679330303
    0x708090a03080a02300a090e041505071d0405070918061518090203180f0d1b02030a020409020f0306010905070f080103050c040903021212150405130b0702011d 70
    0x110f040940a40e0070a61101220b01e50140c4010b0804865010000b174800d142c80086000d041030340c94505108841355181d40c2c3c0c5442ca40822101160030803010640d24050907a1400703070682280560514580000c5100b0042c900c0026040304e05018958941c002850710b032003061100000c0c2401e01c030701c270b0070040c009103d0390240030a4014a0242d00309241e02020309441003141d1003d5030080351942d0200b6040c00300b508040d6101900041144107017580c2c911500105102009480c0c205500415522011543c041d008414111200f074400ba850510800940c40c0424081440d641c1210000741280e03132403000650340300e00808456050310881d0008101c4911680c8100d0080f02aa00c400c031444401c481c0481d8411824040280241c0201c0300300c02c0e03e030800da004407034154406d0056a082c0c52014184030704540000d1901c9018101003014011500c0003000480510311042e00e0030700c414944054035008000c1c01c000004c12030302244000503c0a4400e50045142c118401007001c1420550540650b4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 679332796 1250 679331546 679331557
    0xa02040c03180c03050f0705130207031404150e03030a090302120a0f08030106020f0d050d0921050a080901110418020d060b030106121a0f0a0e0903030915090703080708090a0308 78
    0x5c8901ca01c51702c0daa0400d200062600481301c00078410014000b1000298010790010740048003840304529212034196116000740002e41904410000e1b245400040104006010301f061070113078104201d841d18407070b0300804010980780c05480805a00c1c20000d02c1c1880d06044000242c010b03004403089400b000540e00040d4102d405d10781c2103a0300300c0c0c500345000e521090180202000700c0d00c20800c001e04514550004601d1178000c031040b0a101500b84c00d0348134517010651a080015200003070100d00b5641002e046500040d451000f0080044048020702282c481e5001b0740400d09000c1c3d8840d029040550110340c0008240201844000e981d010080304541003805030034042480d400c1c1202e8260341610840e40940d002c840109980c0c1018000d00800518000ca05a00152804004074004a50310a014041c200060045a0380c2c50040c000701d045c0001c1000050140c02c82d4014010031140026804040d20703044104140d6450903458199014440c0c0c090158201600f49400402d0010542c040c04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 679334046 1250 679332796 679332803
    0x207091b0206010f0e0415020d0504060b03070807030c0b030c130609090f0e0a080d0e1c0905010f12020f04080610090f020c03190e19030302070b03090a02040c03180c03 74
    0xd4950b40c0344c84000c0c0c0c000300180a440c0110984400003004186200168442c0c074900407001860003119030120019a041260161103441d110b014405c940c3c01d003084982c00416503c005083c02c1e0742140c5d510004043c0c00c1c072540c50f44210100124280f031144508030b031010a030340e009039050107940c4c0c031000e00f04070520712511400da441d0008240d041c0000340500d8101650b42c001800c00c060507951120495006040d680035010350751000c040900808000c041312664080014203504210410020010a0a030b0040c904000980890541c8183c02402140c5030b044841c4000d6210321038a01c0c0040c00d80910781c040f01a5100c0c0e001480084000560b00809450034200b0501440c0d808240b981d09a11511020002c907074410071407815000d005000215440700d492034454a42c0004800080456007081102542000068810010150100181d500800d5a11030355030861500c1e00d100c03130311020b00c080c1c0a40207945540c580c01c80c2612a03407061001031071201400f5209a6582054176800e5000c1c0802c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 679335296 1250 679334046 679334053
    0xc2802061b040605070605090c06040b1309140708130606090f05010f080a020d02040207050304030b07110a170304140601082d03090d080d0f27050316030207091b02 72
    0x3198590300d440c1200c0c25104a44c6500f45403c01a0360b0b550300a020040c0f24400780e01a040c4c6880c01c6a43c0c3c14001e00050501040080d10380100a0508100e03030311a40c81086501c3c506181e004e54100e070310501690250841c20981c0490f9606401030070340040c40e800051080d0310b0680081030008990303000007603d1100e01c10410460ba00c1d0101201c800301a8026030300c1701d500070504d450052800313034401100da038400350000d801c08029a03542440d43d005900304503040004281008242c1d0742c02503608890b0344485009000d0405aa2680d0b030505c0d40012040700810000400076043c410000c03c04510451201c5c1210004d43e5111512a1543c142003807a030410381300160700364440b0803d002d0044088030000055460801107008200a00c3c4401c4c0c0c0403682a0401d010503450050203102d508e00c00f000404002c02c03401c5441c20b4480042c031501d510700c04814104040d4502041000040e20b1115055910602030b0343c02c40e08060740f40400d9541b0080800e4200035094213008040000c201ca4942e26808a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 679336546 1250 679335296 679335331
    0x15030d030c170402090c1b031201030201180e010614091206091002040f151b030801051206040b010608130b09030c07060906120b0414040b04020907170c280206 70
    0x202d02030791405480107540320380d001c40401c1e1100007600007046101c800c0008081c842621030401407c0d50003c814090700d48150384010025560071070850300514020700080364485003010700305120310300180548010082001e2404103005500b404070762010303000421036003604d10401d8541c0c1c0e80f14003c0300c2d0b004440c001c01c205003600100034000e5070705440320100307403100c800c0c10004802004100701021750100901010060000802c651441081d14000d648080315903052000740100031014000c14440c82d44018100004075803040303d56030544069141950a0b84c6942c815003910240c445d00c0500206070510a02c2a1403000100404e021594081914111381d0340d00401ea540c18094402c0c00d01007009000c1c00707485032480364000c0c060824024070000d188905008010b4807540c1c00c40d0308440071140c4005020942c500740e128107034400b030a4a400d82c50110301e01c001141844020384054200100450040c210a41c4003100d00e085400001e244003481c400380d0740080d60b030441a540c0c01e0040310032034032 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 679337796 1250 679336546 679336577
    0x4020304050a1e030504140102070b13090b1e01140904020a0c0b101211041416090b030903070303050a1b0c0605130201051209070906060903050f06010f030b15030d030c 74
    0x26035800681c2c0603182c5d14100362800318840e250a80c020b0310a030450180c2400444d010700c0707800291014400083d5010302c4031b820200b0500846027200403042c411400c0c3e44a40030018000000581c00020038600f061107210241045440c0c0c0c0100300c2c00903407007800415403a4501d6407010400320321602031012122140c55440c003d800c0c0d5900d034001d0020025102e0001c1000c00e0301d41c0481d00001e03902501c00036032060410b2002100034002d491a1074880702c0c00d99084c4149600141c0280642461540185581044107105969229040d002818551243e00003040300e01c03180c1c0000c80032103141e1100703d07069000b6100103100d0103c0340400c46920b0b2602c408110307048403400001c41000d6060316014540803200250b0f40001034001c1a900c9244175813100854001101c1c001c1c14014a015101c00e181141189040c5050512046108089910460040100b00766280c052821240c2024811900381c40b5410300042081c61560115018031034070311151205680b6a211700343c151840c5d50350440075000c120 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 679339046 1250 679337796 679337843
    0x315081e100e2d010f1a090108030a030c02030f0c030405130501030c030209040f0c0612140f04020f1906260402280e010b04030512030702120906070204020304050a 72
    0x40400035480100c0c0c0e140c40e60201d01c0400d04042e500f846814901020300c8115007500e00440000803090703116540c0d01131800302294030b5a003102d401c40c1e800110f50b04000035070360749000742c4000104158951060110b003d0092086407074181c07a80410361341d1065006c0c49550390754054031880c1d02074000d0414444039004944111412303a5070181d142001e95140d80c08001080c8409002a201c440e10095070340d00240c5109090b40c01040c06894107400c44150f1164441202c007522403181881c81c00108204013100c1000440354081e50403118440f424a581e0b0102c0e0303101d03001c088100484000848007054540e00b02c544080620340c401c000341b00c10b004042e041c1d5103185090354000e4211151440300301083c0303010008100748444a401160206907584246d820001c02a40042004000000c041c014044203111850b901251186c3d01883c50402201c001d580d135070b02c2c15507003542120101d00c0391030a0390307501c08a8501c150010000c3d0346070b0a00d03007001c82d1900340300304040340e07001c4001800c4d026140ea0403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 679340296 1250 679339046 679339061
    0x609060f1305032404081c0b01110a0203060105240c01051504090b1b0d0f1506030509030706020307020c0d140c15040b09040b040923070b0a0315081e10 67
    0x142d41450208555001c13035150032030180c030480d19403106010340c3c9049909400340c181150f10900c000300303034000c00c20000342c0107a02020b1024099040881c40e0005a02c000450904440081e942d842d0040215510118900c0400360020310300003001542580300c0005412136800346034803210400ca110071403c2080100c804c0740c070b4028200301c00500007a14161a88520891480c440c01607140341c001301031340307550890b8001c198100000f540c2d03e035005d0103e84040d44040280c01d083c00e0800080c20000e52030390b6a8000d008008200580000004503403a01c00c1c0301c00188944090100340d4018500d00d05800c003100d6a2075564100e11a24241005519098000003e941703400086c0718645420b15180c801c207544070301200d40d089a00c66031242c141d515540b18480146008001c041d0710001e40030303140701d043ea82030a4025074550164200303000040c0401c00b1a000c120440c00e002951070854407017a02a024594000d07040c41c011401011403054407421200311404400090f41c001c124030200c010f044400b40d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 679341546 1250 679340296 679340323
    0x501050709080f011b11070305060c0a090503070e0c07030c242901030c110a03051e070b0f04060e060103150b0303030c1801091e050a0803190e0609060f130503 70
    0x100e90b88030591714000d00741548440307000c03c29a00d80381c1e12602c94601d030940981d1582000080080c285e540c5035441002e10010f00001c40141c80c1842c50705074461146c0c20060402e012098000842c1ca003054019540c006c0316640c04045050030300080c244c8040c50807440160314503818101100c507031080d000c3d000c1c4008541d0a143d807441079591070340300460051821503120010320448602d100c888510410801e01494030960b1210b5440340078010340c68810207050030806245105005910014204800c05940004d210040d44520740e00c0c0d0901001078418010341071001e001e444004014070803100002c040940c1520018803001c2400f00926070f80e4402101c40092105092120084400300341c0d503c51072050052404920b02c1d40c41c1c00e0001c46444002d6a00d000170400b0700c50410060030b00011540040030008091420b15401945409034190300070069820003141c01591001580e6010542d00140000381c24240c542c614000c02102d42d0381f100580d0300e040c18680000081901d000a000b1403100344 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 679342796 1250 679341546 679341581
    0x30c090c0224060103090507090209010e01080c0301030b0a090209040b0a050106140f030907051203040501030c0c02091801110d0902040b0306090a0809040617011b1d1c0501050709080f01 82
    0x10102c2c0c0030601c810b01034412810152183e03400701c00728600700541d1015003503203200180d0b11044180050140d200c2e030000c21341401424030410148032000d000352411a0b4000c05001c0b000c0d9a5402d510008200c6414029444028001440b06200007084c0b0b240c82032032815800c0110383d8907100b09940d01c400e69080606000e03801c00c2026981d6440e94051600401c51000701c6001e6034a600010340564a4500102c200754004a0100700369a4940503484060f1014200550100c0442d00481d0390510000c01140144a83c0350b4001221402584082c2d8000440c403c1d40380c071560046641800742200303050a134803807400c225209149140129546c1d01030001c01000345142c0c2541e5441c48181d82108440e586e01507a9030400062061468500d802d1060f01200001003c1a043c000024450b402400b2035041113480c010350841c103880140c0c3c540e0b0312902103407551011105003d110003001090000100294202400c2c8007a040c0c21400c084151101941541d0885981c2c0000034200d4504032070ba09000314 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 679344046 1250 679342796 679342843
    0xf041e08030315040207260309150606041e1503060306110a02150a0e03030c0c01050a1104050f061614070608070903060e0f1501210503030604180606030c090c02 71
    0xc4c00e603004182407480b4071143c500700424882480d0342da085140100d20b0717644e00003040140c440300c107000c0c1805005400b02380c02c0403824003001082d5030b401240074119640c00c4480520b000283d605c0c104000601004045c00d9540091660040c05070499110403030303242d0b0420a002c00303005c8501c02615500d1207258010550b018101d13561966481024049101842d6204502c00c03031040c0900c0114454400d0140669841c100700c2a41421114014040c0348043d15108443c155420103d0454044800c200c030000c880945600005045105941c0d00d4511440404203c60400c54112030040010300e42e001a1809581d880d4001c0e122131404840c01800180c00460601c0010a280d000c003090310300b12000c43d2079640d80760030114900000d0700c401c03012200f0030600400201c924040c01c4004c3c0c88070645901c44015096035050f036a40009056103208584962a4803044401c00b0f00e4494000d4101c0702c148001e40d5241403140031000503008401c606800c158044c40054000a0885503039915041d0102502 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 679345296 1250 679344046 679344049
    0x50f1e06061c170f03060a05031f27060606270312031d06040501050c040302010c0605130f080c0105060f0d061d031315030e060106080c0f041e08030315 67
    0x18040c01c602103843c1c084500426071070344807a401411100030301c4d269450781e034141201007090118041d4001c40c130a03400850300c001c2c00780c0000c041884ca80040340300410116601003c41c0203035640443e8003903500402c0030300e1038240002a00708100b11080e90b141c94160008000c2800c08060404054a40e111410b00b02000040d4540b11400041640c40c500020205858240107803500c04103042507000c1c0d40f00c9401e10080c0a801e03c202070304000e62802a5103030030715503400a410041000e1018103403554070000180b45002c0308000e01c003917a500140c220034441c038038070307040190307030850741c03440c03819618200000302e00d0308014440d00c1d104e08008044071007052869030340b54064000300c801494440001c2c1050354000504001510702040c202081201083c20304420005200000c00070000300360411400c0c280d802008036840b03041d180035181000290340e030385502c0e060a01c12903d02140704100000c0004170308441c40d41000e0740704105c5c1c02d8401c000350354900041d541d01055505141416144001e502e45 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 679346546 1250 679345296 679345339
    0x907020d05071e0f030509040f021c05060d1415101212020c060c03042c0f07021501030317090d02030414010c0f0f02090a200a0507050f1e0606 63
    0x800c40b20f0190441e440d150742e82ca0505803400c1c800328040f4601246000c4103150174090342c2d481e080040c00842c10103003040d00d02482d55081101e403210540d039800c04100103891f40030041c4c183d20340103901c581c50500303030140b115521110070710034001340300080c40802e824241d1079540104882c2030403002c80b0018403617100c000c0445110100842940306104000307110f9180c0b031025040b0700c0f040c0400755840b10315051501d560303440c1c2a052840e01a0052503088040e800402105403c191054000e00d42990f8180042c1e1078903810101140c200100440000105940304440b0178070706c0e0490070340c9c00300d5445800c48c01c4c0e51104081c1d428000758105210500003000503c440c1e07246050b0526181c0c24002054507410030041c4150400c2e5581c802c03000e038510039410070100305a041050902e0400409110520824040401005600000e02d001405090552003201516007275600901552140001c0c55481c0790f8a106038410380b00c0881c40c00c0c4640c0ca58200202e46240310f0030001e4225490020780e941340464 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 679347796 1250 679346546 679346573
    0x60e060403032a0606080d080c03010b090a081b0a050f0102120309030d06120201022a040b04090203100b01091508130c03050706030207030e0901060f030c110115050907020d0507 78
    0x103000d41c103c1c01c40380241951682c0d00a9801078000055050a2002460406003c41c00700000d2080e50703024024008980d10850f070444251043c09929041c0b02d60008404008940c045000c502c20707001c1c055014440c1410480b02c0030000c581089900c0d035510280540200c40100c12f82c0580c000118560007120000029940032409500f076902d8051920b105c0011546150042d0506004051240017196010041003020483c1c000102d60242a110403502480880d05003a034011500d41c441c009680e2140d0300500216030707008007900c020420340145040201a85084580001e105240000c1e42080c07102e4980c20300d06181c0d40742c2800344d450401104a040300c40c0c100721580102c0060010114600303001d01d601811403076a02680e214441c1c14020110010314a09074450341200300108042e540203400c0c3c40141615050214951078100d00544255000d0580e03a00154201081034a140d04540c02e004140c6400702e55112440e190100200c0e554030410300324001042d020483c44011851102000d0f1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 679349046 1250 679347796 679347827
    0x10c0f0e040b04061a03150a030c17010609060e0f0705211f0e011802090109090c120c09030611070b0103170d0212070219020609060c0f010204120c060e06040303 71
    0x5480c030b5803005c1c000c083c11540d0295082c0800080140618417420101403604000308444141d8054210b84684281e6a020301c202100d085260034459070304d103800e400c40801450020070030481075030380702481c50407441c0072100580d840c1da0420008100b81d00803000e40d05900521140200011003aa484401004014251001c49400c500411150414020410b4081c2c000300041400030351601e01030350540d000300001076203014014041403410f6607101c0481000c80e410150046074811740d412b0103980c02c140541c11062003a041902c8010010b800c80340510850340305540401c010540ca40d07070309500c1d006200c0020082080d080c010000f0402801941c1c0d1600700f80c0c1070300c1d0b2a2800e030010400881c1d1240700100b600281c2c11040007071203a0180034000303141c100b6101c075242c1140507500240c6a445106400c6102c1c00002c1981e0f0b0840504001a24040080100865a1755104d0348110b00723180a00e5004ca5900800d9400428000e100d401280c00901c80680b006041c039003950b905862020400a48a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 679350296 1250 679349046 679349051
    0x1a0d050a02040e011d0607170604020d0603030201050105011b080a0f1202040311090f070207051003150e0421120c030209041508071703090f030a0206040b0309010c0f0e040b04 77
    0x40c0140e40d0303600c10640e012241400005030040e118401200640018401c00555000007081011090300410f180c0e18012031083c60080c2d40e9240170024000b80503019007810f2244ca028808400c050301540308605a841c240c98440703641500341c0b40310180020300c000c0100f10340424450741e00d0460154240907040c08941c1041d481c82c1800040c0303a4200c0e0425070040d2084401d0fa85448010300b08040f0307490b008002200ca014007840c0c40c42004e580c0352590302c40d071801070303000c4140c400c0030510982c4880d40011380c1c0d44d540b1100c01d40d19504041c40307a03800c0d40d003658038014a9165200714588900700f40c40c50303045500c0d00d8171190100f60f8600b004050741252001456003c1015403465515407050003100c040c500d03c40c004660511810500d0079546030814200000e202d0400583c180e03001043d00c140311400c07900c0e1451400d001001c07906000e107840000350008000b042c0802c1c80c1961030042c52181c04990004c00041007041e004440601c07071801c440d40802e005144c242d12034241500035004116019201 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 679351546 1250 679350296 679350313
    0x9011505190b030901060306052d060307080703030e030606032a06040306230901020306010c0f1403040807032a0909050f0607030207060e0c10050a0e032a03011a0d05 73
    0x9282d0141e20031030b000c3d01c0a9546d442c003802000442c1c4107568000711a04111000c84490b032110460000c0e000d00e2606041240800060b02582e00308103030000750800300300791070850785e81e494040d02d48050340621500c81d010700742c00104035050000d4440c914541e9011001c1c1000e840d01040b50b41d08401034801500f0030820000440841c2c0345000f841c0e8680d201030a64036041031400c40380010301d50090f1829009900400a00903d6079028954a09268005074400400da80c035181010170460b4046015856000118001a4107100410094100d80c007034403801201110112416001c15000026040f20125040c0144018070407984940c0c4428410022540e00d0394a10a0451805100320b41d4040000d4000404000b004414025031140c1c10069004019401d089400108590744143d504400c0007070110f0510b9607507100d910550078000c0050107540c0030039100306030079180c24401c280710000d0090031712070895241014071513074000c400300d1258021744601c140204903ca6641c0031064401d886407450 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 679352796 1250 679351546 679351559
    0x40f0c140a080c1c020a0f0e0901050310020a1e03051008010c1b0317100617010305033f01060305012103030c110114090606030303040510050a1b020d03050901150519 73
    0xd00c120725154985040550741f12000411900b0f01016003030160045000401c51a01d0010390030310820000e400258a03084901b4046a10140320a0b1505030000306442c1c01c803006401d94031241c041c510383c0d03000135003864452920b942a1144c030364200d00000d60030341500072070381017840200d40050311914029100c204030700c03442450208241c9e070604a418551604020841d044212600700c5402c085078402c640d032450321a80d4980c0150116209441c804ca140703803542892100c150020314a40720340e05005051107102c202c020101c2401444042450300d0008a10020740707000001c40d038848200007041803100c0703036402c8024083c0356401c08107200e82e0f465666041c090a00070b03100c0340007031240380706694a80703407480303904e000e0001e00464001d41081041c071000c00e002203100005507944c3d000200c2e00b9201c03070244100901d020b101c041003440140000f0420f980c1d012030000d8001c0b1082e9818019a20740c1d0312424200c4088151012404111280800060030302d035410b2030410b00c4801c4404030b0f8595034132 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 679354046 1250 679352796 679352801
    0x40f060903031d07321002060a0b060313020f0a0b0a2106031502030c070b01030f03020601080705060409110903060414100c17060f040f0c140a080c1c 66
    0x8504501083e03d4508a000081c40d090349a160000035500500c80940b4049005040341c0c44004000310007003045850030380003400744034654040300e8040d0100c00e8404031500001e40300c000a0b43c059100d07a051105070b15040c50300b40c1c00da9000340d100341d0300484060019030800010f44042e04009402403000b9900168000040c03014003100b0318103843d100c1c440510114240400d1600c074804c207004510f40001030000c01e245444451070070070301c45001030340c0c2d40711004010390074001c0310700c014032003503580001004200d4010700c088030a9201e40c00b282c0d5540d0300c0710000e5440c1d8819015042e041700701031000300034506650b0070852105580720003540c905254540400e042c0002101d0944840c044580f1051429200f04040321003803446101c104661521208001c10101d040914000b0f519205000304280355901203103403400640041041040b48090080400a0480e100491340440c4180201104840b801c904480c031410039699800e4081e0345240e105d581d50b400c02e103c1c074444100d842583c0c0c1c0b43c41c003562 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 679355296 1250 679354046 679354061
    0xc0601050f0612151c02030c03061e040305040b030408041403060603060a09140a0c03140114010521010519060b0405060d02220909060b01110703030f0c21030506031b0108040f06 78
    0x400780c03603640800d076005152400508c403c0c010300941c0004d007080b50096445929081c070000310000c012903501c03507081c01c0324140160f420108a800c0c001061108200c0035030002c1045031210a4220051038001c02015220301049039000d802d6000100010840b840c0d41e40100100c1d44200390020f40e50000b10079807890244405400c54496100e52010303c00d21020a1104031029100300091003208481000d120000c0018812203001d0b110030041c25100e81141510354804240400c020040c501d08907080108001481001441c1141b50070008106054802c044409544010707218519086020803010001d41c4103c941e900304400d081c00a5140d01164100d100c020540108082041c102504044040751030348141d6a0520503590003080d0001404100c260031030342c150510001c00f820300b420995500040306001441c0c0046010b880c403020400d0100415800c12683d0100100d50b0f644050543d40e43c0da64a0501c441c1c0c0920b4003650b0b10350312441f025503010303211f44030100034500365a03100740c152140f6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 679356546 1250 679355296 679355329
    0x6103060209120303010303171b030a0c03060605070206040e040c0b03040506061c24060f08071a0a080c1c0905030304170f0d02160212030c0601050f061215 68
    0xa2444510320b80312040220403080040658919455650f0240051b800390440a9101d0150350004e045050031010803200b50042c00341c9196203140c9550720301c00410a5402100c086442c2c4030010580510900548881950181850f45002c1c00c0440e50001c0303820003003080328154a459008219044680b01031801588100028007140c24040104070706d461b0320b1000c1507400042042000c004c0703400f0006070b59228215141e114500551150b09030b015104581081d12100d000910000c1c071030400107000300488241d0007046100c400e18180c0714110748034480710035000804110100718400030f40343c028407001d44100d0758070b22070040f240c00540c240c80c111403095990740c10101c208404d002c00b40c80d41c0400219041c400f1858152800d100d80028011b1311036070441c2e10f501040140700c0c4d11808803d003550300e4008024240c0c000120b100300d079590340300321004002030240e040002141d0030b2a42002300032540081485043c00c6165681c032441442c000c11800c0f041e001315501701346a4540e000804c098105 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 679357796 1250 679356546 679356551
    0xd0906060b0d050a09020a050111010e0714041b05040302010f0207120f1a010317070c0b0f220510080a0f1104141207050f030f0f610306 60
    0x319100302c1e00450703500818901050381008120401640c40c003845d403054603003d0801c0381c4240503198150b801000c0840c480c11003445020004144482007039644130707481d28100c9041c404044200107006100b405441614003141060000f8001580261102c1025555501c1240e00305903076160a42042d4100c0784042e03079600720390203124007441403602c94051a6401c44058896552456a13942c60911086079003c2e00310b140419080200485001440006d00c051215262290844454010702d5032014403c440701e81d10703810741e414000d11100b0000f41101c0b0010710010300b08001c540180c5950500411003250140e586506a2805095102c2d60034411507180c181901c5a00f48036601d14590400c441d04d6200b540380c0342a5400003d0300044460a5900070b803405092081e44001180c603103413914071200f185000303d840520690000089200c1000e032440e07107540c1c0c007005030400304c40004403140d10f0070040392810017820b20b00c44010034040001821440c02c00c025000f10b4501003007000158200300c030402e8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 679359046 1250 679357796 679357807
    0x20d0b070f120b010918090b04080c0705120703021e040f0f20030a0c0c0803040605090c0d2604050a090207061d0d080c0912010504120915050d0906060b 67
    0x39070241030711441c00b045007801c104442800001905403081c5228070b5003a142d5658030140d11041c10b4003d85009940b1202c1450581440e01d80811310b0b80000d502180d0901c07410500103000e1a050b0b0151000440000141c11030600316001c0c0480b071094000038464528010843c5481b07900d840c49095210802c0b031400248184003018140c0c01c1d03860003d820b249081c648001c0314402c084000449810501407038000071310045146050300c500e8080c013005410b488000c02044240503054110324414400b001c2a902d0162043d010071540c0030760340710003511142da450814044480b00d030210b0340582007201442820913650300d0001c1c0c520303071851b00074020b200d402045040800c4400d00400b44500d0075056294040c00c0c240391019503034070b00d0600e0141008003000110744008408400c90b100c0d250090840c80110300c4082e01c0a018180582d41104c1d1031640064134080e4a21841c0c108040d0b03803140f61066084001900c0032141500a80341145800b5a0341100740e0008145119210081c100406c1c655102e5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 679360296 1250 679359046 679359077
    0x807020406090b03030f09180c0408061b16020a08030c0a0c0801110f0f04051c02030d1403061005090306091e0d021c050720040c1713020d0b07 63
    0x9840641c01000c2d041d060948401c090754011042d00d4202c0c403103c40302a1208070307410008100d24003d40f00340d2081c0c50f4030410710400c1c440c02c1c001002070f05d00c094102c91294a92414594809550154400568009002c1c042c00e0141080c0028215070005001c900d9154440e0030172411039100030b1a4a07102c0d03001c1c3c050740302001a114661001807100400801ca840c03182604540103100f00b010001e4403100c0001c80309110030300c1900741c80c00781901070403080a01450304400b0007280082c00c402d0780b00c2d1090120b103103d454495584c05216121a02e5a6402d64480100740f004d8801d40609100a200303041c4900c000c262801c101503071161644400070140380c5000f4140d94081001c05130040d1458000400c01070007260000707221031032030f0035005504006d8088d00800312824052200d00030501c0b94500891a2402c5140c408402200300440742048900d01c03900003503580507038040c851000f075040c41c000100d4248088107c04800d84c005030500404031140d40d5000c0040034111440400720b8000c2d000200f50303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 679361546 1250 679360296 679360301
    0x3060f070e0f030709020a050c01060902250f021c080f0406170f010e10080115080c0409021e03122107090605090f0310060b030f060a03020a060c02030102070c0308070204 75
    0x1c0c80181c03100c2201807030751004240c4030140c0b8068110a07a40008081d6486d0780b00f401123074070800040000700007950f110040c882c01395021800d00d51070301e505007408003101ca40602244441031f5010a5103032480803a07a00340a10000300a1202c042c40103640540400b1440500082c41610544d0459560306ca041050191848590554800c46c4070080400c200c140c2981009141c1502c50700118800c00381e032024202c21068400e50052125075003024402944203001404000946107148181c17a20f15030040144011990720b45400380d482080700c1c1d07071003819080152003169550405002d80700003101c0003044042e140e0100d9000b0b600d001e05031102c02944640559425044240e51170245022440c01500030514020030030018402c8800300120f01a940d82000307801941070000c0c00500c1400c1c2d03620600c0001d038104542c008540c1004000007203262520b48521070030350340d0081010420a00f8042c0c2106d104c03400840c1280c1542d070820261010600703005034500154810300225584400310b1051100b03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 679362796 1250 679361546 679361567
    0x13060b03010b0423131e0203010b0a08010903030615090e0901090209090601030b01060e13050702160807050103050a0b03030307050a030204120c06030b0d17070602120c07021801060e04050a020903060f07 89
    0x1c0c4211080722000046e03120f14110b01001c500000610182c0c41e2800006c1c014400c0d10001ca81c4074101c1c040000c0d40340410b400c4561898084d0b01c1c1000010394981e600b00507040c042c440fa42c00940000b005003d81c0d218045d11039003146014000080c20403172540170441c0c0a1056031141d40720742c80740e03004104100c100714105000d0b040e031b4a0002c10b4042a58046108a82d41815102c0240e0f1200000344286108005441c03c1c1c1c1800800200d0701e0765500750f8982c40740f0860040d640041d084c200007a182d1040c0e8003070714403003420240042d031460f40c42182c1141c890700240d6074841015020007000600f60003100583d800079008100040d00c0c10700d1b00c0005400c5420840b20359000d440c0c2c0501040c00305140c108800030a8451070340341035403881c091820b00c3c0288a0070085d41a0111020180210411184003600405201ba12070807030b0b404208051102d0504248103040004540345034041c820b0410381c2006404c555600005400e24121600090600c1c2341120750030300300c1407800304000066510804104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 679364046 1250 679362796 679362811
    0x1308030403050712110f040b0301050a0e071a030109020a050c01020705010f0f0509120a1812031b0818011e0201051b090f100203090925030513060b03010b0423 70
    0x1200135071a80c0d4071041100f00408803441100c0c0a210401c050312940c01c26004014010020001c1e49440e0383c43e40018903064140070411f108000e000318050800448405040440550542c15686020f07450342c013940c0902c08030810000103214405850401340050403902d48554004204001040654002c4885c40c1a60b416260706110a210050f003002c24481480c2c0c400c01c00035907441d11340d12000d884245501510100c801012400002c04441d0140e01300740f840e10030358803041c0c50a50200600c250034030b025809841208100031108032040c2d07a0882d80c0d2144010b0611000c14001c110000780c0c002170b00c12095000d40d454078104480424100c1c4641119126441c69a0400a01c000414815022149021300600b140c00d8080d041900030820384440c0b82005101800915001540314003c00c50351451056101d148100050340390701900540d84541100000d541d071402c482e4613002d0280500f03429064165503268a81c004580390360042d80c0080c2c40030424844120103940418120500040029 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 679365296 1250 679364046 679364069
    0x1020c0a030606151d010c11060c0c040b2b051914010b040c0c02060d02040b0f04060210090b040813030c091a04230c0909010303030923120a0513080304030507 70
    0x5902c41c808044107821402e00e490021f80d0381524206401250100b10213600880c0803400b080517603400200107004190540301400040391000c01e0041c1c00301e0301010035010034400c1411412540b0024210880503010f542103a6220001d043c44030701410002c41d0684107149889590280344509000e0b0b40324800065504120482c60254024000410400d00030b00c00c5d0703000150740c0140306240d015100900041c05001d039580c5000003010301541e0003440382c500075014440340800c111103148210340340e06402c0400400f06130340f940d4845101da4060000642e0316400000702201042c0e00e80c8e03007030000e0071224000040b0724900403412044441036120040c440ca04100501c004c6011484020b40d690341485400c02c410340f258005640d2501a00c84992340000345c24000009040e45900710404107801400c0028041c0d400c05c030145074030066010b0503005580460715901c0039048400042c01020700b680f4080303003400c004038820455282c03550301080300c42d803001c030f828000c2c041d00303012160050064103000e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 679366546 1250 679365296 679365317
    0x40311030d140a03020f131a1201032405010e010f1a090405130f05100b06031302060a09030203071707080601080d030c1e231806030601020c0a03060615 67
    0x10420000390b0905a4400008203c0821140c081d4050b201040d0b18000096100c2640b180e09240c041114031409400e008110580804001100115800528064440010f03603003981c036440328291000c1084111442c5002c0000d80140389446000d02030048100070750340c20751521042584003461030300f008010201303d584100d4023030b690104407503c0943c150350126003a42c6001e904280c8407a5140d024018a241c82900800c001d030208a000c01016000820410343c50070006100315800104c80181110714001000009454404068902080d103441c100304136070b03184d9020901b0840250f000c2c40b03448842012460030a002800002d01900c3c8650060180d5894034015642e50f007078403503408081c0f5030307102d1030419403038864590055074110301a4000228000030b90001c042d5052002c0c0e84410242c504a100d44900301c140c2100c021044014065420194910400000fa030024145606511851082030381e961102c0340c1607c021401580000b44082c1380400e01e09640101050341420041d10240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 679367796 1250 679366546 679366573
    0xf0d050d0f0e01080f0c070b09031909030201020c01030b130e030715020915030402062a250e0a06090e0f07060f090b0304060e031602120303060f12010f1104031103 72
    0x204d66100320040e00c140c0b8030380c031426032100c4948150000035100340c0c845400c00040c001c001009100c15500111280b40d00d0780307018070032207060035503000083c0144c0028200e80300030361003604000c1d45201c0007001d034000d03140b09010080072101d80c50280003980d00003207200c0c0d0038800340f96a600703840c0307408180540c45d0403c030b60009454608108a0401000700c04404541903449900c03d442102606d02070b9008e0070801d0b0311405952840070280782c4903c0c4507103200742d0301d106844081111301051401c1d100d00c6050800600b00c0c050b940050004480d0341d0f498070b0000c2d41c040640030b41e0b00903603042000f4201d4142242403907410021250040801c0c081d16103500951560301001150449040303c0c42503442c1d0300c552400c04064000d0b80802885440081a20b0050a44c502070030441c0c1031084a403419002018900039880380001c4559642c044804408540c00c1d0034000c4440103048220300000440c403100420b100e00300d032500c541000100c20046020300400052803002d048071842100108444600c010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 679369046 1250 679367796 679367807
    0x100f0e070e090a0209070908061303020d030209010311040f05011d030a06020c031e0418052716030b0a06080303040f120c020d20060a14090f0d050d0f0e01 68
    0x8144099180000002038141d07000744043d581007503001702000c444e8140341c1c00085c2080b08a000d0b41c13055010341c0002c82c86a84240760740e004040c1e8140c02609009c0c13009402940250481c20440c6c2c18543c03914608d803021501800100080e081c015100c50f0041e090000040021107144183d0784207440100758132445590000c0c04020450f44200056600c0b0f0071102202e0450003000e410300a162198111446a1031000f00548107490840c41d00140ca4001e11400a094800c242ca05074110100b00d68400e6101c43c41c035603152119400c990031265850601e41c035443e21796555600036288032950000703110303880c0b115001d20802040d080008604500380390700c49001419000d000101792140100c1d103074030301d54043c442180d0241c0c3c00500401a5440c60708055452254828844494141040542c085850320400b03841da00740d204da8810088107a55680305000303600c007002032036102c112101e80d00501e035161880c51800920400151104024103440603144942452852040c06802c5226424603640312 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 679370296 1250 679369046 679369049
    0xe12090d06020d020307020f06060109120236190204061b02150a0201090501060501090303201203070f120506240712020d090b16060b0f03030a02100f0e07 68
    0x1164160050402481d100c8020b11510b980307188168004000c1000d00c54012a102140c0910081a1a403c0c2d07600c80c0115203518170ba00416000c140710044003005030a01e1a5101100d80e8014461100d181d814a030745903107400301c024803449511109040048445190304400c400c4041558158182820000013900040d00311485003058420500030303a00759902c45824460014001c03c8603680c80c940c2c0700c4020b0113020455400d50f8950b08100300020207500ca03002c858100ea4069680d200c1c24081d844000305801c64040d0101c0280c807803003e000309540c2490000398060300d819181c003101000407000282c902184ea229661700d540c6064100f25250b00c2e52030f0711a220b20024a05101600d21100f015851801030080240143c5441d00b81d6620803034001038148042c41e503503100d0800140d5a040a20158400d000440c007007840c2c0c1da20b480e80040e41d01d0b00724444014000300b00c040d81c201c2c4000400d285800140d000401640040685402001c9911840720080b0140c0c2c418030034030403c2c0c04060f680c1e0b0410f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 679371546 1250 679370296 679370299
    0x19030806010513170120042d24180f0605071401060b13090504030c02060304060b120717010207020607020f03150108012a0e1c0804080601090e1209 65
    0x41100302a600715040c03c0240034000003c00b01821001030040c000c00280c1e1081014690760740c19043e6400604050b102140c00003194040c500b055060000203c8000b14100040c81400443c04150f4003004a41c4250f1034810941035152280580380050a59464030f41032082d4480c440d2003030040b00a42c00482c4291403107030404540c0c0d103041c2e24040b03031440e822504c0d02c4595441e00b800401d030305103208020031080d040c0e41c1001c09025203c9a5031022600c0965004010034907010b100401420b18101455105026400000340500c0c10000f0807400f04243c8062851500041001d10034080c1100c400060701080c00e00031418050240c1c0411054464100b02a01c00d010031404441c42e6503041000000019004402c050301d1b50352030440c036001c0c0001d4690b142241d484452000c4201d0180303060455901c0c400d40e10680c14860000c03c5c40a04e903c603845880002c90311002c104003042e2060002c2004101e1600140322a40c90400c0020444800d910203244640003c0305160f803c0e109c01c029544071800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 679372796 1250 679371546 679371557
    0x31e0f060114130e0138030411040204032001030606091a071b090204050901050f09040b0405030c011e14010f03120509130902010f14040b070f0b090d021903080601 72
    0xc3e1030410302c88400154400d944603844080040788118510600d445004245085244d00c3d00c01041c01a0201d0014499110030500178400140411542e0801d494149005400145405c0d107c0e06e07034444203882c0000d01d075442031b1500100700301c55a040c03203035070000c040a140c020707001c40c2000304003c000c9420001440100f0f9006c40d6280a0202d00c0d0080300c0000400c910556060b81c0c0c690161010b5040780c421203124410440001545e4140014002d8617031a0040c4016450f075982d07a502e82e001407001d4019503462106014016009400b440344516000000e000700c48825202c51005090340c1c88485010820040c0c100100304020a110340c00e4244c03503015141004500001d0012911405408245075002c81e24940940d145041030380007000d11030007a600c515003044443d1068540b003074160304004100c982048100141280800984012449504e00550300d000da80c4854866074800d0f51070003000d4100e5900b03103d80603010002c4001901030011171031060201070314050043e4030000d0a070b506112 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 679374046 1250 679372796 679372807
    0x1f0806061804061b0f140f03160e03390f01050a0e030604060603330e01060914091b010503070c031229011403040f0c0308031e0f060114 60
    0x61607003014840012248420145075042c0c0700c01403402101102d5072000c900c01100d1034010351100b1040307480c1f404501980c0c5245403500002d9080700d0190b11307403040c20090100c409806030707641442940300400f80860350b4209881203840510480066003015500249503106810316034481383c02220705501c09003409900d4000c03042043e146440c1c44100380e40c1c1130180000f08000c1049550200c400e9074021004200743c500c0c1d0442610a041d00e41408160140c0c00c45004030000070f042e000564905030706c01c00400c000d5580d044800036101f2444074880007000072000c000303030315400704500f9400046040d028012a50040006002c83c03101800c03039010096400000814940203400c64003d2540c049401c00540d50301040103d041e1800030084541d40499841d81111584241404d024031200702d1452440e5482c1d41c0d58850540b140e501d4200c5000541030400004608043c000d1880f50100e0080f00e400820031008480009400802d0440241d2140c020f01c40d2690740011504003070b6000486443d40c42 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 679375296 1250 679374046 679374053
    0xf080f1507050f130b030703050f060d0204050c09090a0c0f140418090503130e0603070602030d20130f0e04050d0305040501021603031b03020c030f0a030902091f0806061804 76
    0x44c481e42e84618541040910300103040704a600003503100b14441d039002c02490f00d810704030014500c4180c2d4515440301c149041d4002614180c0e001e940c100d030000c011185020f060340003003841900115581510035607a08507440e855070b0400c8594440b030b2030525100340d000c604180c3c8100b041c000c030301414403180300114500340451500c1e8003c46000d604181180d4603641820144002d00342c09000703c1b400380c2110341c00319140b030400003000e0007541c20a802440c101912180d0b801c008204801c810b6141241e800b03d110b09030703a0190000d11015040304800c0c6842424031100500c0c0044581c0001d0441c5180d40c10000810404100481818400d00d0085100d49650400c58068081d0f407600001c982201032400302050b8050f84046901da88044003000c6820751400700342c01328050311640d03400a030004c100c08181d820f0300100500340d05100f403c000582c0d0b109034000c1040380034110340000c00885240203c141e080e5020031a1002000400b009011600d0540003045812900c1424200c08481110209040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 679376546 1250 679375296 679375327
    0x15010f082104030f233f030403090e06031903030e0c04020d0b040f0c050405100215040b07020105091f090212010908030105011b0b0f0c0d060f080f150705 68
    0x11a0401d6210132058581c2c20f01080d84000a40c0d0440201400b40c450180c15201045210004682107a428003420011116900d5415450700041424004003444e104084400e03000d5070040303009984d0220ba15040c00342c0c0b0a060384002d81110321950005000507104881000b202c40b080358580344c0428403e07030511400b071400002300300c00c5138094000b0452425000169000e40142c0c14100c03424800b054601200d40100c0c0d042201f0300f00010400c010a1240342458107140c06042004d204a401000c0d10160790455078030706450440342140508140980c4580c24082c06030042c07070a0000d0030402ca8042c4442802c1000400340303248030340e102c0b0414015076031400042e414502c40c0c0d100a000b9000740f850100342562090052038049082d503003446054588803104c805c0f2160340310122100f2a15045801c9101910080c88015410010003020300c864405010701e1b4010007046140303100d884d0411145500342000100401241d6202008092011000400440d00070020742409951981c243d44100c14 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 679377796 1250 679376546 679376549
    0x309050604140f01050a0f0629160614041a060307062102041d130803151c120e04020a020c0d060b09091f18030311041715010f082104 59
    0x5441d481c00c410443c541159403c800c4400c0d0700c035001042100d45407100f03208640c6a980880300c02c9909c1c3c05050044605410040417240121500140d040045075120f030141c510300107040302c0b624800750a0004004011054030103014014000f20722510f000d0000c0f1340d03120711610480007007281415130050313080229030b6403495094003002e0940da04c40d241c9a000840e4000e503001b55500000c0d40c00040c0402c00c42d8145d80d01102e0b40b01c819030340b5540311aa4540070004e80d0700d224940c030007407481541c122000c1c000c0c02103102038443c0521000001451401404116041d04400d000b5401001035843c00b83e03010886c460703410b00c1114007600041d0241050701c01040700c600d0003078114454405206480c035002448180f03100705810100802c200100340d50007590b06010410806024000c03098001034000d4002034140200781d8003490030107075103039035103a54405200d400300e9050b0001e0f00300c2c402c2c5814140c0c500e40513081040f0b402410500d0102455a04c28010189080301d65801c80c4085000d038080d02280c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 679379046 1250 679377796 679377823
    0xc030e03070c15050301080a20130b031e03070303050903091005040f14090f4c050d08131505030a0b04060308090d05011e020a0f030905060414 63
    0x30745800c824a4021403100d082e0040414140290b90076102c0d9511070030440e410390f4880c00c05010510b0316a5500c1890780c0e11900d00040c40e5486012102e801c0e203400941040da500640750105001c00ca0300185810502841c01003a5448002c0c002000c891100008444100f40e0510b000101c55880d050320a0541c011030321200d5100d4800e2100c80b5040354403d01610039030780d6012031065203a80c1e403100300011503c0a558580c00880410000c1c41d0100044069079114403180800c541741d2140318518002e0500d691000c0c44421004004d403000301079052070340d201074541105a007008600700000a4182d07401c106005200100001d010b090142030120040000d10120071072040460768081e0203411600300b02c030ba0101052410404809916141c007440c030031641c2150784c85103400f82500503c205101c015030300341c8483d92074002580c0d83c140c651007100d25040003104010780712004d4110042403030945000c03d00415041c085890007191002c540e00d0381040d03102d1700d00e010625220300141d04007540c1c0d52110 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 679380296 1250 679379046 679379053
    0x1c2301051e0d030e100206090607030c020a12020d090f050a14121507081614030a0207080f040303081003082a150417040f14032a031b010e040c030e 65
    0x1c403c154200c80a411241812282038a4004120100701c0e62401c0803540380c2c90540c8018086941a4081d900810a560640c81981c03512441a02c0c6c000301c000340020090010b0303210200d48001c40d50b020114501404803108091b403103903c0e20002411468550140100030381c085c0038150304035522541c1031035a00580901740e88104c400744c0200510007404546a0010984444c00118100d0703a80d5140013017244a500d405125000c03e04aa01554000401c0341c080740d542005203102240052010f03050103507258038020b40d2a801e620f0024001080a402c40e52042c00c04882400058603640545103104d0b005600510705009294048200f184441d0a203003043c085d00100b40c0c081d0075001403162195000c0c90028000f08682402c48030f0a103e01c2c0300d24014040d80c0d4505105d176660807859400c010760014111484000381024103010583c1d00e10710003c18550721201042141000e00010702005a240e50041c4813030021000a030082d501210010b1086070f880311800c42680c001d51140b06a0305000046 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 679381546 1250 679380296 679380319
    0x40e0c13170d030e03030718050a08100b0604050d120302091003020a02010c0908250b030f0a0c09060e1c0507080d0e12250b1c2301051e 60
    0x1000c01da0708604040c00090151211032451240240100221581100001e6166690b084012641c04841d0b01040d4124841e20f440040c146d80c810358502d02500140d0044c203001c80005c0079110444103a140294012003051000b041303940c0e154980d0429040d00301b440154a1241c129085009100380d0714480ea0003501100c80d1081683c0c154060508018150020000c11080c00701c158bc11000030b02c103111050380600089500d101d6900289284500400504800705480310400381182c0c100710380d19070350303594124200400c22125000f0a00c0290084c02c1050700310342854401040c0d03e81c2d00350000d000d8079208402940141410b140d94000680000070340d60003d071a00c11091700c5000d503003403410000b100101e5104243c90640c088500c0b8441c41c500421b002440300380c510307400310a03070340340b043c011491442c000807a003003500020441c2c060070f0300d030a02c0304415594000d000c48820040540a41f0300c5903201c46c04e5600e51440f0031741516411102e0748586c0d0520401085603c400b1400f0941110f5000705 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 679382796 1250 679381546 679381559
    0x61e211104060c030305130809010e210c0a060c080f0a021615200303040b1905010b03040b15010c060b0301090818032b0c03141b010c03020f040e0c13 66
    0x810510f0f83c13003580d013030195071100f205501c20301000b4500501598010460041c407907000340c40c40050900082c2c11010f00066a008c0b010044400e01c1c1c80c03500d2038101d01034071541460981c0d00c2c0c3c4098103450410b01c040d070395507840d0480c1c140129181d5181d480000101404601c0c000c201c50b29904203400000b40c1c0c0c4070f0302ca145954891968110260201c2c81e19000c200d0b00403109035020b2400a0500c0c001c506642d210f450f003881444015041d540880c02c0d48043d0784010800340112806040d0031121030340d0b03e00786480c220200d801c1c01448860119400084040541e81c00903400e83c1e03042c3c1201000c108601203900180c010215180d00270400c41001400344401d003120b010814050f0011019604204e142520042c411601c500c4c140c400d180650040150140c0510401000a802843c103034000c0b80c2002103a065a0388000d5548540405040c11900050024050341c1280d82035490254140041148241e00c240079600503021314800a200142550300711400f5a9981d08507011041c0400b41c0e40c01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 679384046 1250 679382796 679382807
    0x3011a0403020433060e150c0a060e0d0806100e01050c0709090210020c010906050706020720031b060d050a0e33040f0209041119061e21110406 63
    0x4e2440c9101801c0008800d00d02c10352410314003110060745807240c0d02a001e0081114031211110030151094040c090141009001c00c00e40c1e100510442d000102824140740041c54011450000010065110308200107521101000c4140d070f0441d08210100c40034550040e1201e01031400310311801d01c00d000c0005040120350b0404841e9a000350303450440042041c0040361141c041d020f64902080403038800308030340d5214400a02d28540504801400c008456417503ca5482c4583e0303d1601c10030300c20140410615050102c1005203409d81c145012041c8a48040307001406007100c3c04010aa407080014841016508010134103000d078402c1d5055501440588921038052269402c09281200c01a600080c2004200390150340c001d0007031404292650f0821140840007070007154809114000611a07803903101e000002c071800b40b08803c05075420124010030a50540c030441c103d15a1403460950702d41c2c0c1010000030408c0c1d410390604140d00580d00590060f003520390084c6403510f4001800900c840c0d006 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 679385296 1250 679384046 679384091
    0x110a15060f0f1a03090f03030c040611070503060c07021305092407022d1b04150302090a15151e0c031d010210091a091203011a04030204 60
    0xc90301e00240c0e41c550ba5245100509402110250a2210180b418800c1540b02940c3c1c00f0410030125030420007904c0000d0f0a43c0c1050342c8085070340102040a000d805c1d08107103039039182c01d5030a00030000d080c0b829002035600c2001070412850181c00084030015500c075035098240326184040d05125a042028402c0e54900000703400c91091f80b0381e50050100740940f605071600400d000d500500220b00c00c04040c0d00d040d02115a5602c00f92544681080302c24000d11010038074846030380c406204d030341c2c03000c080c0802e4031203420b00f02341c458250310400e00050f6111072150307400c05944076001406022034004c034030188100b40c011840700e80c0b18110100420341c0c891401080009001034940a03006138200503196001a180b000700401e108070744000700100c1e50080402506814412101195042c001450031560074200c01e5403040d941038440400020b0079855603401500309030040c0380c1e4905560107005203000c1800b81807c101a4010201c0300010040705031030155400420422540c0d8603980840c0864821 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 679386546 1250 679385296 679385309
    0xe0f100e09090c011403040506041e0b0a09020307080304120f020d0c170c040c020a03030905070906060c0501110301030803010e060a1802180f010203070813030c0602250b0901110a1506 81
    0x1005c1c1c101c8038105244003500d00841c4d00400400da1030303c82c2e41d035203511107140c0c412044100a601e50341001007800080207500440c0710040c00a4012118010b01d03090000540044003940d10801c01005070011711030150600c1a000708683c0702854007031002820304041842c020344003c04e40840411034003030440342e41c1c0b00c0c40d0600003150a1301e0184828001a941c55011420140c1c2000c0f5200c004079000f0781000056034402c0f02901d1005850b0b680c010210f820f1600001c000030b500603200f0040150903c130f81080ca907480b00c8980d05544c034580d030790342151005018074104c0c148403002041c401d803100c6400300090500e910043d8401506002c5441c003e400074082e010354400e0b28030303084095042c14001c03d0103800c4107030b010b503150440f40d45035402c0c00d03801903250201c0940c1c2030b60004003240c0300036414809012964003500c0c9032607200f066804c010310030b4114a4084035041d2406c12a050351141200e045031000c0c00c108c000e02c00f80c500303010f0600c00301c0740020305100051100070421103015480582503811 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 679387796 1250 679386546 679386557
    0x360301290d030909092315220f080f0f1801030605150703210903080702010501240c02180118090c0e090f010c0306090c0e0f100e09090c01 61
    0x301010030210100000010700030600c414018002c004154002003402070240400400b2090400d50541640300310010700b0f412508a040324492200da103048054021810318504045c441014464007014640c0702001065101c110b465402003003000c3d01038468000c00ca184107521007080d00c0840c84e0319400041d0b2000d00f0301c880c40c14001d4a41c086d21500c02030b01c101611444914072035685040e01940301c9541030742840380400040b852891081070300e480c250280d4201103171200c0d00340380207040f42c90050305060942e414007005004005074014200c450301c1d112041190007410300001990045030f5240e001c0c2d0402d0550562000aa50200d0200d04a502e0240c1d0403070542149001042121844000204060b12070041040304191841070340c0d410400700c0b81030740d034500d8400da0143c0c00c40c2c0c98a0840404a0303211201005550f50503c260003940066080018042d18170740006407030800d100496038850301003501d00380c1c0d080f0700c214070040c203622000c0c00d0031a040c1414001196141543c4011600091 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 679389046 1250 679387796 679387871
    0xf0e091c0206071e02060408182e0c08090d061b180623030912070b0a060630200c0c01051213052a01110102360301 51
    0x9110075513142010401c0e80a40025141c0b996484000d5021500550703804030800c0740124540e488006c1d6820000030a0a181c0b204002152525a100700600031002807004a09010340846c02d0349040b103101e134000301c50405c010000f07450014005c01c4500103500d1819503c5109921041d04400c410b0000386046640c8000e15680f058112030044c286000e00c0d4000c040e040b910180c164a00b405950000701c0c0406803000300104c10300c03066864000040a6030082026024014281c00910a00c80031741407925141102d29101c0901140c41d081d00846504c1004080c00740c510111002d0b4050100341101052100416002a060011680200100652030700581c12202c40c1507003d6400c0b04d000102c040500708144c0c6d5903043d00c503d240000c040503102405281110603c26800c220f44a80503161b81021003001c1c20050001481c4800c100010f01280c0c1c07041181c0c0d00b084a2031443d01001c02c2000c070310b10b0110303c0a04200f80604103402c3c4440d4044d800c10004002481041c002c003000d010f01c80c110540d000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 679390296 1250 679389046 679389077
    0x15050108030412260f04090b010c020f0f0117011514041212030f0617010b010f1d0118060905130903050a0311070c17010b0303040f0e091c020607 64
    0x348181d104096200100c03500d00341c0061040703240c0781310b1180a04842002c0c2c0d00d180d024400c9641c40710102c43c9903000c0004e824807050f00c19204625204400303280250712903440c0d5002c50540c1d02101142031050001ca40c0419081c0e1080d80301c80100a2222600001540e41d40040e20740040c005004030049400001e050f04070003080c13000e680460b51400000c10003800d290300d031806e81484002030002015150081e0845000071401804010590200504071702c146000400303085407070301a40d00d810030000a51440d0301990184c2c240804019004010000603603031801a90b07815280464100da0240a140c0007916641061010080720380541d800c282a184508c2c7c003c080740c280d1031008010500c00c0c0042110644a42c1c0300310f41d004280b1010900d403507156100e0b1b003044000c6d580400c2c040d0b034840285098a103405e00951601d0302003a07004508050a101980b0010207880c0260591141032600041ea24242041186440c56450701c49003610180340307800035101e82c000c17a17a8001050b0107044d007100a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 679391546 1250 679390296 679390303
    0x3050c01110c0d03080403021603080a0806030109030815010905031903020601060c0305030a0b0103060512010e0d030b09010504050603030906130f060807120504141005040c120c03030c081615050108 87
    0x200340000303015114090181d5026174018a02400c142c007144254200780c01c05074124184074001d54000d00303040c0d07100c200394240203101c03c200800d49802139040c40301480000340c001c41c407a500040003d0164010511900c012240c9144035032280341d1502c107034120300c3e5403801a020794241041c040d038281e1740741c0d81e22103d058843c41c601d850020001102003000420400c050380c0300080203901450041141561200041c0b10b544c0c2e007170015a403a940d80e0303402001d0200c003007080088285072424140301b9005000002009610b05208413400342d600c502c00203ca82e0b406000711410741038020185070b00e0310407040c030000c41c644860044200e59007860b200454102d0203162518460003c1d69511101048000c0c1800003401014004480b102d541009002401c0c1d01030100801e04403508800040c180b4090404204460059010300d1003456420011408200d46e51a0401a01e0301810a210302101901c2c0c100034034440c10a10b01c14503c0c04400017030800002d10342c82c0c200e005000c8010b2020707980f105d030307182e07107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 679392796 1250 679391546 679391563
    0x1e030c02130e1b0a0b030c130e100b1606020f030a0606031406010f090305030f120117070e100905010306021b0106060e1909060807030215031501120f0603050c0111 72
    0x1070b90f110b07a486000020a800c42c10340d085001904a07110596910002c6916800a407140700e020715020603404403000c90340c84810010b00b641c0d0854985800c0030380d00402c2c4a50140a100f40c420700c0052200302c0d98400c1003841d64085ea11200440d41c0d10b4101c41c114045130010b03242d05440c80d09111002445030720a0240742c0b021000d900701e641c59520b407a4015224240d0407504802803100d904400400b00750203101802602c80c085900507074500141a450307010001c160480b0201080b801c1012280c0c131000a40d0b081520345c201c0703a0075056110040d2020603607002d42d1010148a0801002008001094014000c080030b100146039070704480001003030984d8014050040003441049865050746064141c100019050800c1081c49a03101d03003c08081e200203820202041d03010442c00c00440c2071a84034540c034a912000c01d24194100190760030041e43d0005d00087c1001148400c2030450049035109a6039010b41103000c005840d82c900c2c0103521503070603041c460b010424001c810001101d01248210 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 679394046 1250 679392796 679392821
    0x1503090507121505070e090a1a0102030708040e0c04080d05040905060f030c0f040e0319080c03041e0809280f12060513050a0f1716020d1e030c0213 65
    0x501d0b503c030594259004000c02003d82c07080000c140b40c245c609450b00d903151030148000507804900ba0440094000c00725100032400d50440d88100031000200c0d0590080c1d5043e1038034182c1114490700c5040000c45240a2070f00291039900a113840008010303042001407085844118080c0590340e603a03030402601c20500000150190450410340e41d031072500020440646a00420004001c44843c810f00e1941d04008014441d000140e020790b4140303038206a005502201c00c1e6131b060300d0361800c1d40e40c3c141038203800100d6203041488c21040400300710329001074446e248400386c081c00d2204040509101e084500b00e0107060411890031010500d0803007210f400d000da030103044840c5004001580c03000c0081c94010045402c0849505250000800c1403184c64a00c40c001c0085a0200840d81071940c01a44103021400034810f0400c400408892400024481290101e501c101321003510b04003140d4441105d00314460004405000d0740425800418890455009032101d0041060361343c0c18000b16450201400c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 679395296 1250 679394046 679394063
    0x20d0914040c02071208070204060902030c0a0815060304061b090609120c050a1508061813060e0303090d1b0c0e09010e0703080c160f1707150309050712 67
    0x6851400c0c40e4004403500341043c070495121030b6a9148881c0f061a0840c402c407141c50002450070207604d444c0c02950050924444118514141480301c4210781c80307404001c10030f010001c0c002070380c0900341c2c0c41c00c11031000c000703002550f5a1a051402d10014144d01c104001940001e41031010a9485042c6180c2955619100d842440e824080441415003c0c40b50845400d170707042130046411b44031920380400030b01c41c0ea089240301c0c51003c8005041e040c4018042c502030407090204207060700d0801c58140c0c21444000002c055000b0a04002010b05403c890341489880004184034050301d001604017080811030f900d4400041801c128580d003400071702d0300070301048400c0c0024031141840c030f440c2d250000c03140c000004010180d41951030501450380e2043c1c41c0c00c080070a0400c02c882e014020031040282c2d07540c048c0790340c906040100d55a108540900780e10008401c81400c2c1700201000600d01800d882c1d5807003c3c41d110703c0c0c1c0008000d0300c110503044400c0e0140c44000242c41210301050580550300a0703c0707 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 679396546 1250 679395296 679395329
    0x14060709030b1806150607150b09240112024003051c12060311150c0706110f060103050c10050c030702270708041707031418060409020406020d09 64
    0x141d108544021141320381c0b044e0201f004000080000c3c02e1000146401030000c03072044040c0c0100420684014102c610300141e207000c02e400d180d0038540458488009007049220540702d1041100280a488403a014192418058a6070180d0703c0b18500210100512400c0300240d0102803107064841510000740154010b0208204400c035240c3c0090a002003864010f40058540217100d0545815603c26a0000f4100306074484078181844810840c4c0c4043c640586003050000d8101d0380c0c0c030324500c204e81c01c00c40d41200003c194a401d11502c1c10101284040342d0055860b81031581d2544450030020f4882d42d0040c01009041e805441910070710240c400242d0b040038026024012240100801d00300036911390f400c41d04c042c03800207980d940946120350b145429480c052805a6251b0341e07400d90420f00715424840100003e9000c2c070085a034100000c10720307444003c5001603aa0320198141c1c0690301045c040f6003c241d0806c1a40a081115882d0b400c85420f500e80c6d01c000d40e40c06215020b00007000e0f403c10a0b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 679397796 1250 679396546 679396561
    0x9011517040f0b1503010c1e1d03030a0806031c0f0e24030915190e0115060c05011505060301050d150f0c020105010b13050d14060709030b1806 63
    0x1240c0358028026a00700c8544807150b502d100c1d04002c01c81d1414042e4031150808500390900748295805100c050804002c8030f41515610f01d104114009550100102c0c4000c0e094003d40244c410401c010003c0c0407a030300c0780040f0802900381c601c1290103a001c6e101d250504c2d50b264181071044c034100346190f20780d114000b200d001c00301c81d411603040126800c84442184881c3e0003036109801c40c101c0042c080c04d1a16414000020790404951b205228000c01d00c18050011410781e040800300b00319442900051000052000c15024010740c04618141c6140840001062508524104416403264000700005416400c411307403901d010707000e42a080701007880140b280e0305188420380300d503d010700c02c4e054815040d085914103030f45242e115140c0d41600c0d903950384105902406a02d0142446280b0107007003880018040314090404d22810307114003101e12400302441943d410094019140c6000e40307200381b810b031030081c0c10109248001c84200414400007524140c4039101103101c05002005081c079521642d6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 679399046 1250 679397796 679397837
    0x12030c080c121909150c020d0206010303050405041e050903040609080604050a0f08090901030503040f0602010b0306071404080706180603020309060402120f15090f0715030203070504031e02090115 86
    0x15409180d13440c011980440c081208070312074210074080c0071415038491a070003824443c0c9010000d0035944100018000a80c0010a840c152041580c000482400c4444190a010017480706a8159850002806048040400200161a12603e41400d00d598070364100b0707503800e0102c3d0f001d4500c0e040280307018001003502c01802d090b103008407100d40c1081c90141c0080e20305802a41704a0ba07aa00000d400c11a41ca804182c0d1002452140001c100044c6e01c070011984480c401000e00c0d00708041119070004810001050ba005080160101c0300810b440b2000941030394a1038078000d0800716810000280d40d8428001c49104100d8500a040151960390903c5491440c808900700e0324058010740c840f01540c10051040100b2510b5266810f42c10900b41082c101485c1c0c0204042c281c10200c0203222101008188070301e450101d01e40140d4950361132030110b0b01805250401041c0115020103400a03840020411454600031238440708140da03602d4407030000c1c0d10740304014000300d014901000710420094 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 679400296 1250 679399046 679399081
    0x5061c0b0610050c01050a05010305010e01060501080c0f0708040e070e120a060b120312040b0708060102030703080c0418091502090a030602030a11070b0a051302062512030c080c12 79
    0x900703155041c15610f03074802c1d007507074000ca0360380c0d202039075a000403c2400bc003402144058441c000081042d0ba041800007020100c0050100c044404001001e1405050181c00c0340c0102c1d80051080303444949034030080208413426100702c000124445100e09061500103104061040d10754000c000e2400140d5500b00a08100034020f0340c00352100b140454a0381041c401001d04210043c400b0346145018504101903c034054142401c00070100104421642c00004813140c83e501810840e54942d11b920821081e8800d9812840314204100500c484010041e000100700c140b0543d200300300c001e5004044401c0f4040c03000d1003640700c13000351001c00228146034019038219414002c0480ca900714045080c925900990f003c03115041c940d41000410605407140c00c1d000b02410310f4030900110725400140c0c1d54010544d50004000455910458220440e4150240716510090f8107078050440c0d0000740080c41c11085010119800c0c0c00000c4060800004507845079a004403080d1064035524041d10460040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 679401546 1250 679400296 679400329
    0x33190807020f010204092012040f062403050d0e01050307050703171f080f33090304080c011e0f021203090c0a080625020a021305061c0b06 61
    0x405030b01ca14080428001803020f03224030000412a040c0301c40b040d91803031038040105042814240811154420505c070303901d81098006400300f081035040e0602c81d00410f18065075000c03e13900400d101d1958418000c6490440f0700480030799007031100b19841030314407441811300c2c0b60008908200044410340160080e000640c020b1404540c0c00b200300f076047e130340f5007410307180807943e600c030070101024000560b48c10a0290103054086e00b9440003000036156507007100d40c0e002d101c8008030b8216000f100c40d0351b198441c40d015090800c000394144140007a80b80d44c0180181c401901032504400010350284049410307030524001001c1a2030fa40d024116607100c4000d4040045010320350104102040c00030285008904070f1002c0e00980052004114214440b0b0740300d0021904440104404545c540c03011410810000b00d0782a03e100703910008070300380314400d00c000758480e00541803805050701d03950029104441c15211415005407000b81d1030b80304070105400034071001c0d110780001d0990400100081c84c4061 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 679402796 1250 679401546 679401553
    0x90b0915030c0913060e0307060b100206011208162004090c0e04080c03030910062102040f0e012901020c0d0312060302041107030212030907051e3319080702 69
    0x6580d034034a400d480c1480c00c8400d86d64004a10751051280b6171103100d031407034021160003400c2d40304214041d4980f001481080c1c4407007195100841030111a4044070129030f200c2c440001035a440d4505013111b0078003e480d606403038441c4e101800882c01c1034400c1a0300c1c00d8000004482651a260013402c2c0c400000300110380c10340003400040107002d02000554040c00c01c280142c50110381e40200c0b0310483c4d4a540c0496a041c0c3c49440082d18120001b21541c0703060f0b016a40841c060b00e0030b00440d0084c06000f28819219803916100740d88403160605814281000f01450009006060004a80d12640e12030031640c04034410190300c00182c010307285900d541c4840b2802040306039607a0005400c541a00307d10b4010110006200010503a06000d41003040d100b01c0b90050840c10071040c80c0b560758800d0301aa5008001d16000214075800212002031084030080000070703207e09102c0000a04c1d5403040c031038070304207a035982d0343c416064500c030580f0325041044024400c03118000708120b810600180480c03041d400f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 679404046 1250 679402796 679402831
    0x6060903110a210501051b07030e240d291c0b042409030e13270309060201090506060120061f06030b130b1207090b0915030c09 56
    0x10400e4115a00c12501450980c014003c40c0c10400d003035450081450302020709048010712411021810b40380c2030340c0c0526000401120741c20103c0e4948002d03480c0070310110060141405801c4900c00100314120740940d0500c101d40f00703d262101000c1110010084403c007940d0921914203101c4c08170070607009107032080910704d9880c0c2c4880726840c009031015101c00384100c400309400c24006000c2002c4c40c06656007040080100d0320002c203041100188184076081c41c2e45404000d90094100101c180d54410491416a0307001d541000c8641104c0800c401048002000040f040e0041c130415064507000f1000c1c201d5a07954400466141d030018881d1040d4011428001c0710001e400c001c2584158803001c00c44e11099180c403600500e085080d8004070405040c80d0900c04207440e00301d20042d5101009201240e080154400200f44002403078801403140b08502002840104541162654100c1652200003540302c01d46080300c5206140c64040d0150702181c4806040d05000b101242d02c110b064603640c2081c2c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 679405296 1250 679404046 679404059
    0x21b06330f180a020703030e150705030a0605031c0e061e07021c050106091a0a141215041704051f02100207030e150423030c090109140105030106060903110a 69
    0xa100560740074451a138041501c00c101a0540300b03030311900d0043d4001f0110020355500803580e0b400001c289008206010003c00c4440c0c01c950403400103000018103541c0040c0070090440c42000b400315100d400114544803480c02400d15800700d40c920b0024494441c0c007100c00d0711003c0340c2d65206d01030807070b002140400010382d8035072082c3c9401c2c8424070a00c0041907491802d60944245d800c500d42010b605080d940c0300414540c2c540c00518112803045030070183c0c0707200440001d00e54129148403a0b02da4000d032505600949a0f640b0714901c998490b0b0b0080c55011004048031141d40502d015581d013000120702a000f690200315200300300c0411500c119500100e00044500690700145000c40108500c5584081c4500e0819141045e415200e201d0501b0f0919108011464448150015003407070380185900c1c0d85500e0030f100715900111b0252458959582d2103825400625030408100709400018001203898901800303643e0440b42c032580c50a40440c2141c48541d104490502103d0340800d103408002070341c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 679406546 1250 679405296 679405339
    0x204140609012714100602280c050a0b070c08070f05040504240c030608010504030e0d03091203121d061512120909070513060e0301021b06330f 63
    0xb2494185010701351403d100c84d117a804114203400000642d040510780d0034002605c0070004480d030140c1d030045526410541441426442d00d508180c1d00f00085000c003140541485000f01802c0b48683c0044030800d0703581c0510f5403981210700031806000d5105030100070710700d0686c00c10394005016440400900001c4401c1d64051a0a25041a6030740d44a0f5203c0c0001c0f501032044800404006009001034540780e035004014002d00b190b814802d00e0070031200c0b010b151181500801510302c03055040c1c26110b09060107804e0b44a00b9600000c21820410406001c900001c0c46081800d107580040c561900d840c2d141150810a8021150300150920125685400100f0020030311443e00c80d00d50780d0303900c150011301c10000402172020341402800c0010b6034503040c07014490000c41e43e0307074035001c40011644000640648200002d07091a25000080c0c00d821a0010941a01a481a609510403c1c444c10440c1d511103000c02c1e95000d081b120700003e90910300300f424413011040d5009181892024180d0301030840d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 679407796 1250 679406546 679406561
    0xc0908161818050c0102191a07110a03082d0a3308010c0914010804020619080906070306031709030a0803010609030308011a072a03030c02041406090127 67
    0x2801c0c4d00c00a010950381d40c040c80074205407011010000089003107902c4a00c0f809803890300039084002010001100786208144c0600b03c481840d0540e80118403905004001c80800d0700ca40315100401c02ca200300a01305c80881012455005000511603030300da91182c1c00a01000fa4450b9480b480324800944120031910022140d402003a050a80c140c1445d03034403800c42c0c02007e1100d0900800b00c00500032002d4210010003545800d1078850416074952020840a000719505035882a02d0450140c0e2065009401144100780e61000c580c0340343d5032460118103550540c80054400c0702048140c420b1200e41c1350040014000c0601100c440084c250f0f120b48042d4000d034006400118200014005c03d039100c8403482c010428048030741080038105100242c0c502c1038500090200c402c10b641440620140001c010601d0032040c45582c0140c0d49044c081c260340d03440d0200301d103d0762034079000300102c040c0804e0050190f074016000c17034261783c208002030200107804052440c000c0400303541c1d01c4101e102405040d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 679409046 1250 679407796 679407803
    0x607030e1e060a0503091506030a06090c0909060506041a06120c1b03220e0c0306040b1906080906070816051c06091401032f03100c0908161818 63
    0x5a03a440c002988501f4412042101001041c0300428041269000200070007095089a400203000d040e502e04080c1504507a817207002d00605003003000c0d00380a000c2c0d100d40c3c402c100586050112008808040020081900c2140c0e403000c2d003131000746e07841c0c44400701c083d030701c00c104610381442d01c0d001005019610700f002036a0039040d403001405203a10030400100c0c40400c000c0304561808036007003070000e032500c8800a15a04008d00c000c80003450940e6550030882e00c15102510203044142c203c1c0412040e03407024003940c400316640384085554090005400ca114048035a1800c1c51510740702c850001c6407580038400d4040140c10300c2800d41e080111002021001c19010707001401e245041c801c0010b450000c070392000c456141d0001040401c403940c200280440c454042c41c0d280446c851036100e40100364900c030a42521179488844980900380d84980104961519010011603440c542d950303648a205036581849914445d0800c2100d041c14800041d40280410109071080c0c098000700e21030082280c01d0303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 679410296 1250 679409046 679409057
    0x110304050601080d08090a140102070c08010203070314040b0c071a010608061201151518080304050a05090c0a051614071a090918070803120a06050607030e1e060a 71
    0x400a2100810402821200504042e40c00b8a01b205109803608035510000d45094034a881d11700070b070ba4007941121003050340030280c00009a04c4510803070007504100e0319007000c00c3c90f00c1010300304c400d144003000303220f2903100000701301596515038441503940045030110382c00b400c124104944035a036080850701034507180d654000d1514107041080000b106061081100ba4506500b40e1610342c500f04042d070035141001340a001a401074442120440b101c4010310b07000c1ca09401e004900c2000100080c001ca030300486600109545540030010a000b054484955100c3d0030011260368074041c5014001c42d000d4448031a0000c000c688034580341408003041e25078143c000180c184500402c14048429085007a1004c1d420103a50201280000340702078642541c0411003114400d50388030804c5844098a52801501c1d200c1500e031002c0410208207a54242496007402d00114413401d12100b956403080c1c040c1d6507803801d40140024010f4a40e183d5a11064484400000a816072542c0c40104403000c2c00e540c1d01c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 679411546 1250 679410296 679410299
    0x70f020307060e010c230304090b090a140f0a060504090303090311012009030322031412030105060d0b10050c070f12140f0a1a1302010801090906110304050601 70
    0x4050404540b500200305201484880f0712660740c1c0908205069507010788010048581071720300c40103024121054002c40c1c4000280451740034060780009030341d000141d501d10200d868030807400b81903074804421031020000e0311340042e289085000c0313001d0300102c801100080340c82d11003011400f542d0b5400c400390042601c550a280400d0360021282c074040108100804c8491003010090a40c2c6008240c104190b441c00301c0d060b10199420b10481d02035042c60b0848010704054440d001c149400207120996002d0f00d4181903668a0002242c41c52881040700d041c6480c5038280410011280c22030740d940c1480d40e40d614040c0c001c90b03c850044c4090500941c88098550310420246850720fa5a900810f240c83d52080c010808200704010315a000c9500113040764a0020180c841850401c450550a400c0d100d2008160140440700c402c21842c2c00c5070501c0d10803d40d0360600c0c9280854100b100017800100050010450642240e000d14550751007a40301082e0308080c0e812003800c9400a940603502078020000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 679412796 1250 679411546 679411549
    0x302010815060307050a050d0c020a03020f070e0f0403021903050d15030506010605070302030c0d0e01030606170c160b040c141e0105070309051306060e0d050709090c0b070f02 77
    0x4100e54814035655020000d11004030200b0054080030348004c007031003c04680c540c10207000c1d4086e10010145103104001903898100020741e00e0031031002c00d0340540100004603003110f00208034107058581910702030000f51144410741d034411000800640450091310014030360307200c04410302c101039402680c0e910380350071500850801320b908604200c05c02201d44181040005c0c408281c083c11180c140c04c00d2901e88d082c5040503402e5200313940741c80d1a28025415503990b51038014824445400081e0f07001c006107500e802064803448511100681900c407030348009411401040c004103480d448a5964106c5c0d07484503540c90150720801d44084550307231403515040c420200d400520080c014411075010400015800e424042002d0064045041100c0096101d051500848520008280142403001c0c601102055400141100e00454002900070400301002d441d02c80b950f001c8003070304a0040e200a900c0d0501c660028410b044007106d50204140300099070304980c801a02a841c0150f06084034000b4510 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 679414046 1250 679412796 679412807
    0xe06130516020f0706170c071e0b0a0204080a0b181b1912141504121e090e04060b1909150b040b16020603181b09040b180109060204030201 61
    0x943c8400c80d9400013a08001c000d80c0800446084002c0040c1c14065031182034442c00544a1203801a200702c0e000b400c0050320b450340301d59030300c500d80c051541d4460a0721351008007403e9116501c24a11641c0c4507903d180c000c610140710b03e54000482064540c1d010074000d0301d260502c40013050350301021080e8014038800f8140003603401c03200e02d1030710840401c56080c1503100005554081c40038041a2140c018178089940800c16213a80c3d40b40070500c0c1e00030380b61504d080700b8401c40d14103001c00050103090340c3d102e0040e600918a0305002c1c031a01e8103c000340c1005175041c0d601f03d009009540039a2103402c00c052030707110700c00c0c0704004903019402d60348050700703111212090303581c56070f14840303110181402009220110002c0c0c5090f1510000c03040d82d581d01441d021134145040000180d40203400106200900010004085075801d00c541a11185801d500e509a49040038012198102800c5000903000039007601c0081d07801503600c000e803021618140d103d1800c44a40160445150b0b80c00a0709005541c0c021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 679415296 1250 679414046 679414063
    0x61203020c03030415050703050c01090b040219140103020903010906060308041d070504090f02071502090a0614070b180f07060e06090a0603050a020715020d0b01110303010e0613051602 81
    0x340e00544c40c01d460400d103c041121a01448010004040b030600109481042210a000d1042d4024004401c9509224010b1941035800301d1113650251050001481d0a040c1d400c11a070140403035440096400c3d0041d00a540032011156055507a0307251070300081c40911918014600a83c020350301e450800d0103803192143c008140c80701c0c0138016010031065691200c105d42c160380c903842c0c000c2040710602e403922002c0e000d000700c0240401c4920080c00d54000080e400340901c1c003000c40e42501c1480d5103110556801c9200d1094000c141070812030540821000c3d03140700c2d080101e80140c0c0c3c100c200c1c094030450609600038400c40017900465001c000d125801150740441c20000c079201c44c600034410001800030540c03886907500707154441002482904883c0e0680e01500c0d040b40c90300302c19041451944c0001d5000c092050310b80b03413600196803040d52044680341608103549008514603401c12900c54000140145185c0e07103c1c0ca1440f040c802c0c0440f602850313029480201c0d18101700d5825100107030815451 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 679416546 1250 679415296 679415299
    0x20c03192025091b1d01082a0406050a0917100c0e0607050102070615030b1807120f0b0f06010507031407051609200a120b0301061203020c 61
    0x100c0035041000c180800e080d1000c40c4411014015040c20000749000e1400070f90001040a18080e01ca010006820010420b00d681c42d030345a20480d180800d0028401c400c0c0c1c6400c90010342e5000000b40008403d0380303511580108061502c0b807108000840e0b480756403064108000151011403d40d17041c60b000a840e2004e001c10300c420300c458040c403140403540d450b00961800401e0383c0360211003007024090444040d03803c601910840d40c83c0814185036010390301954044610304d1800c0005000c6c1c4510314040710a981e071013600207040b502c80041e15165844d000250a02034000c089000a00d0014020081c00040c82091140003145141c10001c56034000203201d4008034682c501004210307a071000131241c955516040c100d035502244d50802d01c3c28000e034840180184510074801601c400d0760b161210403100c04190a210b6003052241d070650940501031307002507904013444905c0e0902c0c0200c0b140401d1051000000401420080002c0c0c00d44045a21681403001405c84a00038994140b20180c8030410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 679417796 1250 679416546 679416587
    0x608030909041b0f1a19052109371713060c0b060a03050309010318080409140702030408030f0a020a0f060510050301050f1f1d0a06050d050d080a020c0319 68
    0x990400740c0307005a030b140c4294002c0281c006203d500307106504a043c80c1c4811041000302e0f13146020342e8810741d21042e81a598032402038040450005100c0ac520b012001c48881e40f08407401002031f540c0c00c1d2403540129000e610210b05000b800c401000515690340145225a40d001303041d500e42c1008521200003801480c0122441d0106001041c400001c4a141400038a00051a41d00c01e003074408000c04c1e1804014a0120005000113000040d600b041d5140103240d2100342244e21880710903070307070b0303210f04d20072124550000d002c0034804d0220308000d002824854019100078001c01c0e40c490019150742d603003c0f07803075907941e00511036803141030500c1601070b0805600170015410420f10301552442d00614850071590440949a51010090b0140b00100718240709000381c490b220040c4200140b04407411131300d04d45000c50008892400e012000d001940041c0548403101c9e01820803282940300030861800eaa800b00094526104100000d214413a003000c01a91581c00c1080c1c01880c8080c081c07040c240050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 679419046 1250 679417796 679417807
    0x60b040207171e07080705070f08210c0105071206060203070f11010203070f2009010302100807020316080403060507031e09151a0f0102010608030909041b0f1a 70
    0x40b800003042c5807025010301c4081c0c650703140082e040000c8200da41c50156a00d004241c403820841180040c0180c507101f4410b40303003aa030f00c8010212032607103503115041c0300d648000b10400508401800c01c2a400c60741100c1c1c43c1c03401580c09225030a482d42510800c00103000807004219528051148601a180600c0035510300303642600c600c064a605120080c280e0b5030440040d0030982c0c001c10488000c140d0002001100911504266441c0102c039843d00100c2c50000401e9a40c031b251240d0501e05076680240340008000ca0000100d400b51002084641948400c121460342503c8180c80c500b0054800c5400c1503070b607410b62038080192400640940281828240d007030b072580c2d0900c45e80d158006405d080000d80607100b4101400581c0c0c0302da04522074145004600500610301c1d050100d01c81c0000e49101d82c00800844c0120308840c2030b40328200194200b40700380410303490041d042e03035001409800c403480c0010780c110349600d04a10a51000d01e810000110802c214070442c0f0510a0603450002c005003800b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 679420296 1250 679419046 679419053
    0x111c06050f2e05030a0501050603060d032303090a03030b0f1012060504020d061409220f0501020a0207060912021503060d05060103060b040e0f070b030402030a0b090604060b040207 79
    0x55401c444058458025103140318100c1c112400602c21442c0882195507901d040300b4000750041c0e1096130010040c504210020440b41454400c03203015001c064003200022196490442d08001d120340d00c403440044002c00c0d10446000040a580100310034006412161744516000d02215880900c41d030081b030742107032070840c2542d601100349c10017117050078103028510640901e0780c0180002d411080d405840484c1e006980c6519a0042081e140c940f0b4200036840100010028014802c6a5590000c01c06e0030607214848102091000001d204d03503100d01219150741e03111800da0b044179414031f0059100f00c00402055602071505c0004104c07400100040070050340200703c111840801a03480030100202003203c07600c0b268003405e40c003504542624041e5849150090103048001820307440b0703500b02003202c0c1c44074002080e0f900142c41c401004000341417800803085030765000140305980c140910005070700842c1080d09060302c6080c4440103040c1c6c0c0d02c1c0514043c02120482e07030072a40110301c14000d00000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 679421546 1250 679420296 679420309
    0x50910060b04091e0c03060504050a18061508010f050f060108010b220504140907171b0d0203030a031407110c01121b0810050301050601141804111c0605 67
    0x10b440c000320020a00040540a403034494222620003135403149450203030546507515911810559500301d4080c8a5030700c50321801d02c140e030a441d4500d1502d0080710300710b100080840e80014428161040b040350b641da614500d250868000800182401c2c0c1c4032410407840c002000000d40d88401e007428500c2065051508911143c054411614044285c6000490000f07060315071000040c8001407003407000175292400c600f5142c00136940e00455114514020851601e18a092a000701e10070300181002000550304041c4c1f045001701e0035402052240040016803400d000911044845880c0416003501c9402400c0c10032200802c1002041004ad0050201e0100400ea1103070084003441c01104d404588100f03440105448030f00c21041c0c0c40080e9510b60117940107a08184225651584403c8540c2d40e03070306250036108200d80b802c2c0001e032010341ca448040c0611000c0c248403154190451151340344100030604980b00103400e0f48242a000c0358a04003214444070242c66540d40d241d040c0501442d18022804 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 679422796 1250 679421546 679421549
    0x507080d0c060203041b081605060a0e04050a0216081201060f0909051b18122413060204060e03101b0f0c060c180602070b040308210406050910060b04 66
    0x10030b070f8000010505020451400f6041840c0896641e5105640c440ca4640c0d0740d261036040502003030b071040c000145172519005030307080110319455036000200b401d0700700401000020f1895120680c01c4c0800f22805040d030540b00303031141c481c4c61055503032900c45042e0340c22690140d014804105042e0030310300700e6982c455640f104032211075601280036107941c80d8008a00d0400b2804100100d0041058280408007012040c40c900302901d10000807518500780c10344421821005110600205c8411240614480c42003580110924406400c80d0001d80d1a01c00740e0307106501c4400010b035a0b1002c8203151409104c0d412500d09110340810000c000020f541c4c4104503250141020700800f42d1340c3d0600c4501410840402e290f101000300312100540102810403c0d20031102c406030707010004040f80050001070030806407000318070500d02b45845d558824080381d228081e05003041041c0803803050242c0111080500491007000007040743d29013113075440c0c6030910408501019900f00f40040200f072019004850 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 679424046 1250 679422796 679422803
    0x806060109090b061905041a0903030f0a1101060602030403060b041e021602060309160e010806011206020408011814120301050910243b0a081002070507080d0c 70
    0x60f4180d40c2000083c03140c010107120500510b0742c1c14001308490b501100520a070790900d0240c00118407003080031450380c059031600f00e03010340c410094800c3c15001a00504400c2903c0d2400720f06600e00e40c1c03030181c2500d80d1079100d100582d0001c10240200721b81e0b4001e05155420540c0d081004d00c0b1401410300203003446001c0361062681c005951820501e6404c9c0042c05c42c3e402601c0c0343d40d681011501c10350b0325104d40b00704450951011501007207003424030782023904944000b40246030507400c0401118552055000444d08075900b0003000590600a0041100909513003051102c0b0407407a0403e40e942c14580d00e5954030f241c1100d001f00030025038610980741510410381d140700c855510008008456209500601c9000c00600142e14294215040c1e01120104ca50b854000303c040c01590002c0072500b0010401c040f195110b00400b201660100ca1324035100020124010b40c1d940e460400e0600c4006c0704d001c0700715034000501c1424003804000e04401881090010105000c444000501c01c0d0f5003140c004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 679425296 1250 679424046 679424051
    0x40504080a0f1214011406121b070f06020a1409060d050613021204030e0427031e110c0a03030203070f0f240509010b031e010f0606050a09080606010909 67
    0x405082d48210424240740c442220b0420607483d640c0101c0565040901c141686050304c10007a4400c1d060031015a20700004103807910b001a1248495144185040500112400e02c00e021201c00310b0200d55a001505000366030059032564001001401c1000c0f42081074481c2030100300580d140d27100c607400c07039007100b07042040060591201d400041002c0c0e845c00315058454000b00c0e0019000403034840c0075006034807031b440c2c60750341603800800e12040c1c840784621b02000040c801c00c0703031810551451500c40a1413203443d00c020b00d14100b0b41004005200013040100007401c0181c492212a01040303050000002161070512085ca0b40d41d00940d42e1140000c0240705020703814102c8100017a44080304407003940844200c82c42c0d110815032008007801c14481c90800d50a0070041801001d040c13084500303141010b000b402c21540025003810b000003090703100380d0040d075881d04048020b0780d803440703200f01400b450f42c4e4032959030140241c02466544183c008500f103070044010b101d03160b0f0b046002c03c1d04884420001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 679426546 1250 679425296 679425317
    0x601060f12020406020715030e07060c0302030903060a05010f1a0405061e0d1401050d0f060c091214060705030114010c061b08010302040e0102040311130b03030c0d0e040504080a 78
    0x1201c101002908a40c90395001080105420b6004698801524801020104241042e100407410b64a40c0310791400b281c1c20031007061001c180f0401ca450312441c06070044900d42071100001c00e250070310850341000c0007962440103105088564049000a00800550799001140c04210240720301c42c274442c003845400300003015041050b007200c01000110403402840d495040c0f01c6131000103420202c5c24089a00703d11000803d9034a0f05101c06c00c0c81310b0300504404048003499031043c0c02441507074850000e100e1001030008640102c140b105a4103031040102500c0010400e8141d494584042c1585007807002c2800188441084012006140c05007483c004814466600b0084000e1541e040074210703000c0c116880164040e080104281268400e4908020f00e9250011090803030080d804014900b44a401d100005072038484030035000c2c1007105400255144900700000d02e140e111640c0740c400ea8000c40c1d0009071442c1c10078080300030100107440034895890a42d64040c09442104030340002c0c007690020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 679427796 1250 679426546 679426577
    0x1211090f030c03070b0d1805060a05061903060605121c0c0305071703070e040b030d03020306040e0106031a0106140a0c320609030a051b010b1e040b010c05060106 71
    0x2840c2e2880801905a5012903120500d059860b40110440f0351a41c0c14800380b403c030f206503412030f441c26680000c064091601c40344083e4001c0e00780074050f2a17020b5020104a100702d02e4980c1444015403040310000b404074605400e0100c58034004d0444402900220b80040100700043c522220462180c5491012081c1601e015625802000e00c090560010068424490711480c4000c1d03010324420303200e4980c5607a001d4100300a5070300c40c2c3c03050ba4040c0c000d41d560107400c03400b039006076800000041c004900000c01d2200b186c00c60750030f5070050300c2c5400c0204012102c03081100d0094050a50780c40c0900c81c8a02c440d0344001c7c40d10481840c90100300c6405c551070140a91803400c09a80340c2c1490480700741c2c542d601d0038051152140b80040806004040104030007100c000102c3d01903601d162201c9051200d09010b40342d40000300d5081c9000d954a4503928a026aa00c6105a8418500c01d01c28070440d400c00f41404201c4240300320690600034200301078404294000740460449400e49847c441c048401c15 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 679429046 1250 679427796 679427803
    0x60702120a0c0f03050f16091503050f0601030b0a020c0a020607020409061e111206040b0109030c03081926070201320708250504241211090f03 63
    0x11000b40c00329020b6030010414007000c0700c01400f00e901a40172112162180b038046525800044415103200d15001c200b00714280d0b1179040180c01b81c040c12200ca01540d6692a11400c0544c540700344046a00b0a41c018020461904102e07600500c0720340d011400c100348102d10079501c250703101e0080d2203a280440c421045581c0d41d041408010b511410030700140c120881a40310880b15104030344007182c2402480c000d030308a04401e86907190a01c201e64207403501d50400f0301c00146201311405040015160002c40410384100d164801180b09142d800e40c0c4244c0740410003444524034603c00c0410900c801114800e9407409102524000b400742e08070fa5a4840e100e0903130060400c10303003141d80c40a04034440300f901d5200c0c0c451400300304c65200720000700d940c3d0900d044524040c22100c1743c2581c807410142c0c407202042200302d00b21860640c1001407400f9110a07191401c4c0c0003510a00c00700380d2441441101a940c42440c80320300c2402100f06119682c40e0180e03565850254622850180e411011050002d68041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 679430296 1250 679429046 679429063
    0x7181808070507050102010c032d020708030c070203010b120d1d2205070f0504030b04080412110f0108060f2412040b070203030610050306040e010e1b090606070212 72
    0x31000940d81d045034a482034903582c0510640707026501c3d05420b043e809005e800381185204450201340f160b01200002e49440c49003441c2900c960980c21700001340083c0c2c400e0700841c010742c2c013101603d403150690700c101400d513000c000d82d15000e0048034102e0701140f0000a01d40b04d1081ca035080c03500341d07450b1818a001c0a099090217050f4492106c4411155034a01c22003051040310060100b031004c0e540c2c030070041d10340384008929a0000f5108100c104042401c40d08041d4105200c1d00d02d051400342ea0721100c0e00c894045180a4540700c03004606110285010002425009000e0814480038901480050310703044854602c82e004402221a00c48148180c1c180c01c080200114005500e0301c0d07031280d045c0301c000701c201c50071144600010003080840c1d0000090f01e106d20401803580c0c1c0018045c445c221ba40c1e40028140359002911506522006203080c042c0340e0038010303400c0080c4204c01d120b008108801c9083d00d2024007800d0003c007841043d45820088842c00364041d24030720039440c0007106151502d0b590 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 679431546 1250 679430296 679430303
    0x30f0305070c021e0a0801050105091810060e0702010c0207050f040f0b1c1509020f040c1e0513050604052809050c0a03050a0209010807030c0203090612011502071818 73
    0x880710380901307283c140844142c455401c0d258010300750303205c0d5405401c8a80a000b00750f405402c14002603200c0d103003d2400c00d5013035180f1080c0c8807240701c80500081a1603c80d0414001e4103205000c10003113a909224212a5013103510080c0040761422012070f060600d184c1c2030501603501c40d550481036003079039006a5804180a040f612140c5102c006081411190000466400205500383c814000d002d00881000d01e03001040d11a4203842d000c00c120051284891000602003550300c040e07200b512a20442a0844454803003c2d550141c0e400e5025010645804c078511520091000b0701c51038807aa056078415402008944118580900c0c0d040d160b100075501c034080c0342c0e06000800c04650a4000070303140d0340000b070f1001d2000b610358a194809174000d080318640041c0328280042c0026103c3e41124040d100c5600540e881c240000c40410030a602040041c0207c41076500100a9100c0c400154180b00c1c0003480501450307824003c80801440301002981c00381e980b035548814110007884400074a141e032 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 679432796 1250 679431546 679431559
    0xa08060123030a0603061b050d020306041b0c03030506030f030904090c120809040b0901060c020d020406230a0b040608040308060105270f040e1009150e1c0507030f0305070c02 77
    0x241103d51101501c0c41380030469103030303040001c2c291a0805d1003d03566006102500d440381080e610041c404000d410040c10340b41c0c81601d6003000042030900040c449a40c81a6a88840c921441c504000d404d551380540014007075800a80c05210301e403400b100742d41c43d0080481c3c012541f21054104000b07062950f4000008403111703054003274104840d500084c41c4c5104280e40c1404202c07400c0c000c11040180034030500e0f0101d098825858014030380b9041c0414603910003000058895148c040a01c5c41d0300d980080c0700802d600440a8804d9468076151050040c12420080c03413800e03013041c2005042c1d940140004041c003006c500442c886038060f50544101503540c0310410340d03d11082203203100b07291135004d4450007100c030030360100c809003054000d111501c00000700819202241600d008002d19018800f914503400700290007450050b94040c03400030040d1140144160500030740c155070070200710411070040c84001c000c58800a43c1110711540c44070014140014550744105042d200c806800400a61041 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 679434046 1250 679432796 679432801
    0x40b030705090f041202060f060f0121090203060901060312120e060a1a01020d09060f09050604120b0c0a1209030c05070b0a090503030c0c060a120e0717030a0806012303 74
    0xf41c2c550303001c600c560300072002c1ca640d100f9142da060343c89040541f2102c0540600c04001441410301d40301c44c440c0031380e06241c0440c004101c1c1d90a980e8210800041c2000691145500411761070708100e010780000505008210440c590340e140010f02c210061034505214074440c2c0311000c002690b00135000c3c0074000043e640a468001002d6001340b40d06400b2040364002051403407400c0d44002036009032135a43c0d88420084a09249060f200d2109111901041000e042c2003c1610b44464014000030002c017400f00ca0b1007001ca180c00c21007000c000340b200c2942c0f2421b001c40b207001c0358000119680300c1d151400008196059040485400c907081d40d000e00584120500081d01914410041440038000d07542d0311581a1103104043c0c40e0b11441031011030a9101070031012080c03074800010000b401586c1030024026043c00840c03010358940100d40800c0d604500c01c20801c0400707412519120309400c01c0914584000500058442c1074043c100c035040082c01a4450600782801e4009071310511400446526807 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 679435296 1250 679434046 679434061
    0x305060a0504060c0e0a0501050d0e0106180533011209050a0302160303210b030708030a0210051614090a030b06100807200c0d050d03050f01080c040b03070509 70
    0x20300c4255011070f826403400500d2890944074200d503007500305000b0042c009640c5000c004451507008204c0d10b02d0031603610075814200304001d1244000520900d0303102203101c2c039144032080c00c45a008004409011a0b0300319640d6000c0c0c900c00154804d4640350041c1c000d40c801d580100c0b264000381c0d020616a0b4a810321200502500144140100e4425400c903140b413580e404030300040030913a10008000c01c0c03141060b490f40076108000101102ca44e00000960b60f00d0031350001e03142c502260b100358a103410014030f5131003040d814040c20030741c80c0091505100506042001804806144c88044104003608110b00c51800700c07201203510f4070100810040711a41c41c1d0410501040040d10141d2091031a41d1800e99100e004103c424800c043ca601c1d0201c031580a802c10280c0c8009010300da504034003400d5403104c410350395030b4a00440e50740107800418205004040181c02c81d0009054046041022801000390440004e03c03200c5000e01642d02146050394800420316000301034021307a92000641041041a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 679436546 1250 679435296 679435301
    0x1014011b1a190b0a1a0318030a23030115030f0b36090307030c21030606120608030a0c02180a1b030b03060402060327010516030b090a11040305060a 65
    0x850682c41003000070180810030450307048003521803414100c42050007280070145800103958000e0006210f0343d55034203508441070851f4420003850b00842d2442c131078005046501c909203003600c814584a2403540d414000b010400c02d906020600070191500080c1c0e20889840c0c00230942c440c400340012151501c0842034080303400c540c50740808980c81c128103802c1e00f140c400030014002d00606000e0342c40c010a90f10308403006001c1c40c4065400412100740d404c0c8444080d02c00740244002660000740c0349003020b100500d0004480c204990389402d02c4024403c240d004801c407848503941e802d00d0500c2400610100740030038416900081030061900030047c880020342c000360741071a110b8030303114002048402c05500310303078004100980603403000c0001401400c0103402160000f4031010664080d01100310965032504100d51a00ba060b512407040c4400200031155400c411041d80c2800e001c5101010045003001d00000c12022049450701089000301c0058000c450296400105884031440c1c9084180c01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 679437796 1250 679436546 679436581
    0xa0207150e0c3c01050c1501150509031e07030614070e011d06030a0b03060405010e16061d01030209090403020a0c05061602011101061203081014011b1a 67
    0x1c2d6140c0304500c91540e030f502e007240a003880450011034442d5200050560b400062150403410700200f084200c04c0740c2c0c0108400c01e01c485403a03894411660500040008212600401c0010700c007051000c2c10741e59502160030030460100c10400c003041110154014a0111240c0c000380c0203524094041c100040140c000610441c4241c030340c0140c05140d8001114100010034902d03e242c0c030745444002ca0b502d0144011908400201808140a8440d4000a00702a8141c904480c0c50b0b54489506407c490700740000c1500c13207143d0805440e80e1707180c80f1000d00014448603c1d0780c80c10103042c04021242c0e000381e05486031000094600340c146d00c2c26140c0a0760701c120b4080141c40700403001a000031a172800000319200c4083c03807111012818001d0b401551040f0303540c13034141042c4d5204d0b00040b800013468581031320750354000e90f50012142407421040a44031310719004011182804c4928650f40e0b41c01404684031100ca00d03401c078200048505085058254006540b00040c04c2d030030600469210740c850712903 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 679439046 1250 679437796 679437799
    0x1802070b010806191112010936060e030c010e0f060a060b04150c0203010e03070303180b06060a030908040e061810120602040911120108150a0207150e0c 67
    0x2250742c07109106540d9041c211040e6280f9800000f0011816480b90807020204650980807414030849a24400c1848000d800900c03909554a504003400d1400554032510030144e40c04071140728001595010a040d290300c009172817140c40f02d80040d038440c002c20480c2c9080304000000c100030880e98072565143c41003210103910521480010905604451003850215100242c4403480e20b4a00440082c0c5903480c00784100a000c0004003207000350714280a03d440c00840e007409560380ba0501e113400307021224140300d49a1007001d03042e081400690840180f0750480e00440c1d40541f900d080c44000c0300a001d104034000c01c094401f040008a4002009650740a0346040307880c80d540c00d59505e1503145024084a0140b4105d104460410212035006200c110700d41c0124009850310f81c80c0c014000070342d030268411201564002480009240560400d60b0260a01c10042d00c0c039410b03092540200b044024150031001075002401108000c20140268076642c01800240500ca1002c2c98403a1208403800005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 679440296 1250 679439046 679439063
    0x41503020409030f02060f090715020f0d08070f05030f0705070524040b013503041a0a110303070e0402090604051c060e0102250204140a060311060a021b0406180207 72
    0x601d000c850010b07224230407c0d069006180072841c000f00e0340400070025007403000354040c02c586542a820180070394000b0400c01c2e01c49103118100418002c1c1f0b09a00000010100308003841441103d513171030000e594014040c0e2401d0382d21448942801410580048401d01e500505c51006100d017404410741c09100f240918105030040ea41c41c070000300300d061410381c600600482c9421002c5652860711900e80380d00701400860b800d058231904003142c103072090300d00b032090350310040b4107000006e0f4020010032400320207034059400c0d42041d48010300048030714048a44a1500440c20b40e00c6900c62405807002803000034417070180344554004411021012940c00d40ba6181000d42c00742074000c050003254000181c0c107420050618580120074408951000206c1e4000d4031600e41c8000c485d40003c0382d90185180001c000350307051552410710241001904041e01a481c04d21100050ba42c01184900c40d8809864014060130030300d100180080c03015030402074162518100c50141e06a41da03001e412032033321030a1072 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 679441546 1250 679440296 679440301
    0x501050603040210030e1f060515090a0603020a210e060606030601020a0b0901063308100b0c0106050402032e150f020102040b0304140c0d0809041503020409030f0206 73
    0x1403020912040b10080d4020b0110741903100034034860b074000846c100e10102030b511001015010b0791031b1035a0074800ea00e412900c488050005260075403242000e411070a21083c50240705001003181c4a41500c02c040501d03038082031601006014600007131a003000e44c42e82c1083c2c038a02c09501c0006002004448080e40301d00e100103122420554116401404160010803001130186c0d14442031203030003070404000c0e54031850005030150001c003000503e4806110402183c0d204280481c0b0004040e0280f03c007003204810a00c0040e802c100c244106a6a1541c044d941c1d4400140000b801f40003268401030301710740300104010307401c001c40b140e40010020840491003500b5006a500e0003004190040f42d0541e140324005940c0940510859254040710340000b40c00c0a6907a11404c0d12a0011a8281d8400d04200c0d0382c0c1c220784105128070892000c08607598910300c0607549031a100e40c080d20481c107000cbc1ea40c0d0310a5210743c48000715210020342d4000c3c800e22509a003490010001c070070040000c005441100c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 679442796 1250 679441546 679441549
    0xb03090102041d011809050c060c2506121401121407080304050f0a0b031611070b0a11060907060e040605040501090f061d1303031e15050a060203160c0e0415050105 72
    0x240c1c6007400c2e003010048c0440c0303a41b00704010880d031090315041e140e0f2142007000c0b46111780074014110450f0082002070101460190050010000c61000a104500d402c08100410341c48015642c107507103180101100d201020302c0c001e40c109038a00e151441c90710541c41c000407440c1000008005440f0107072080081944140c00348001081c1c1805001200001440061035260302c064503200051401d10f40035031081d00080c205810281c940d040000005070003d904020682c00c130344802882317041c40005018510b86407200300e40320a02801004100402c0400310a01035980350000c01c060100100100b040e560b4611805008010650054800300c0c101900000c041c4034182614040c0c8113020311100d080d5032200c13185c50111802103011002e150355030380b040d07041e040d4a80e51250b8070342d800720000401c4060300c9110101c02819600441c07041c041d80d0030070b000055000c802d03180c540503e0381039410381c40341c40d2418403c0c03048541c200080c00c05c4120304000038014108030f803800284e0f003050f0030007140e6291b60 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 679444046 1250 679442796 679442801
    0x201210b1c020d0803070c02060d0f11180f060c0d11011113030b04081c1409070b07031805060c150106020102040308040b0a020709110711030a0c0b03090102041d0118 73
    0xd602a602291000514000c250f104c0002c551010302c81c40c107400340310b0703050740051029004000c50300e1b0b0480d0348024034a501c2c40188100041c48988048003400c0c551103904001c001201d940e0304e41d0150002840d4146d182c0c50358400c1d100f01d102c03c4002d0307a02c1c140c80c14000a04006003886150300355070804034000d254401c00011030b4810504c100344c818810f4110b03140e030024440d01070070449600030100406030080004180d0301c10910301c1c2c600d001c5010700c8800d50703000c00980003910607045a04140000c016000040c012141c241ba8181010308802c0c00c134a410840010696020641000f00010310034007417400031a08a552540d1840507042e00e03603c3d50b070102c1c204e01441c0401002800100420310080743c68001501c41c03405a88100c1e015103440e0406442984d0101405605000b0085049010030200d10074a4030b00890a400401007000151120041400180700e1045c2804000010a04041080d01110007811007623916002d120b095640c034002c03601d424455400c10400203404202007802c01e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 679445296 1250 679444046 679444099
    0x102030a0b1c03020c1504120c090b100509040902060d06080a0c080309060a030b120111040906060c02030d0309020a080a080a0e010201090f0809220e0106050306090d03090201210b 79
    0x182c1c014004a05c0c0001400541540c020751070740c5491040c1f00028060704080d640c40b441c03a21914041040078a090900400c0c5c0342c048003032074820751801092000395607000b0b0a907856007504840c042801310050020804500c01c4101548034982800c0700070429100000e11040b21511520030400741d03503503482c004e581301d01400b0003a0b83d00031400c2040c1c0031001d00c00e4010ba003405074002c050084101c20840034a0860300f000d9842001410f020508200190841c032400b00200075a040141c40d040d400d030f001075290f501664284082c103603249031400540d11254904d03030282c0007000854850000c00e08004055410404016000031159a41310340725501c1070007006441c0740d210300030707c0c082e01c00c4d43d0390b11000f60444100c55400c1a514440c20980340242c6000a51800c0d8200d00002d14440e101411400d40b065500301a00942c050f000340500300000180c0c060a0365001d03d000544083c0a2004031084040c0701d0074008020b400d40c8030b58880c00f81e00c4d84115a80e107000c41e062800e0b50302d076130240c6c604080070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 679446546 1250 679445296 679445303
    0x50c030d020f060402092d06190503030304140717010b0307090915090305090604180c030623030c040e01240b2205060a08040b1b180d050102030a0b1c 66
    0x1038041380044c1020080136800c0281c0c0c03c0305000d1740c1c203000d20080410700400700d0300d0225004c44091001c641030281d046d56001850400c526002c40c18400403940e00c0c440604020042e03580030760600319100c420702c880d9014001d4068054211030200c0c7d13003a406041400401c520900541100049845241c030030110005c5d44692903a0710444c1c0000b2810050108650136018401e04001004a5907140c100400c080c00301c19004218030a03045e00b06000700c410b019603820500d40341440034807201c0d103c0b85651004d401003440084036008000046814894403400035600a42031000140c030346003040d0031070360b4445050f03030b074981c88400c5c42c0415170802681c610031071040083c20880c1400b06c8100c03081e00162a4500c0054030701c1145e990005c2030f0303507501c40b24558001901d10018041081411010503402901662441070b40c0a00400c181140e88034846141c445600710508140c59a00d800026448041e0407000864680c074156894001a04000c40180c0c40366000300248488120441c0800f04450380 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 679447796 1250 679446546 679446553
    0x260306010f030b040b03070f03060608012d09020301020f030604050906071413050604030c0618080c01080402450f0103020d03051306030618020a022d0a050c030d020f 73
    0x1101c100c182e004221007441c0d02d03000342e00d40340300d002107480401021005200500c2505081840c5082c40c40440b0b0480c0c211a010381d0400e0465206080e81e80142d010000318040d1411038240701d54001c1000382810131000390107500214080040c11a0f1030040c0d880340c041030b034081c01a0755a40710410303195002110040c004c900c050084400c5500c060020b80b054481e00f641c1003041d80d45520005a4680107640120381030701d01070b0300602a20740c1c442d00f010750070401041d501c1503071810903041684880040b01e0640c10844188000b07815540c81c80e0040c0403240c110790241c0702111600391981c6031a000f9101420300c8030300104000c4481082d6040c1203200c0c072a104444600ca07400c603400c101403c804044150104181803100242c1204400c072068002c100f55140040d1070307032524140c1412a58000d150500303240c8144140703501150086105003000485401014010406000000981401205050181c45005441c408000b0001100c0410410480c1201d05c40d9811000490340d6181203075100c01640c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 679449046 1250 679447796 679447817
    0x10323100c0f110a0b0a0b0306010902090f0907080a02030403270e0106210510033f0c060e03040b0a11060c030105030a0f0312090f0201110105010f06080c070206030426030601 77
    0x481e03002e445c9400c461000d001040075101c0400091070f050b02a00007032162030b8000f6001d4040c1c40e044450000b80342c815114000301d03140040000c1d08000000781555003050700007000908240c41080380d800042840d0343c07600103030640d1400300b110b003c0a901500504076801c100100d00715006030b94442c454004501e118020301601060700b03000c0c00c005821144003052990740400040c20440e052000c621241044402ca0594003d601d0444540000d1000002c10061404215032b03074880d0352414070795040a0040384072000b20291a19520031640084603404010694002c956885801d09138078a4800d4219017294071444269451791000384290350380365200c8600b48000910503031010300440e002c0e0400981c0d840d50002020140d1322008030403111040b00056a904544e00b0490241c08000d4642c020046507060a407854120056402500140856140000d602640c1e820440320074640c05400e09443c1d003030601d040700c9210503d905202c148000440613001d15a80502030724800c000c142d481d0020300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 679450296 1250 679449046 679449053
    0x9030c0213111b0c150c0c0904080304060203060f061b0c0a0501022e0603060603030f02012903070b0a050301080601091b030f1404050606040c0206010e010323100c0f110a 75
    0x24540300f02907401409203601403082a5284600344403580c03001c00b001c55640381121900c3e418000300c0250780744201d0b4001c0902c8082200c0c0790079282d01a03030005005035030780c417130000084180340344201940c1d00200000d107100454607121840c002010186040300d80c0941c00404005016940380a42401070303120054100020400404000640715400c002441110a681c04001a0b501a42040d540c6a8403000c04000301036000c00d800740c80c0c80180c4000c1062001d52078004480100d030302803102040c1c0369141e0100c280e81d41409082e008010306103103541c1d00c1400c108054035503042446428414000c1400001d038101c1039000d1941c0c50002c005040040401c4d460b020380042031045000c0c00c000c1e170345480400c0414582c00c0c0031809103010b00010641807608500700803e640300d1496807401c43d008400108107180b410207049066982c810800e1400305912040c140303103000030f540000c019108036400c6c2900140c00d03902211001080350f07910303000200014410781d11103006c084003e98540c03040744c0300d0012 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 679451546 1250 679450296 679450327
    0x120807152018180a1e05130201080c0306090a0b150c01050907060c080409020307050705102403170a050c06010f0303020601050108041a091905010b13050403082809030c021311 77
    0x842c6407030b601009604645007000c5c02103a0301103a0364440f4103c80c0b1032640035580c11240840c0e02012407240c0314558900100410342e9010007030040c00a0540361001d0b00364580e59000d0500003407128030011511017060f00c6401c0c1c0a05025100c55003a8000c0300307000325055224440c400b981079004028a890b00d03103005003410081d40014100801c00c102408501d0010380b00b4840b0f107030010780807070b0080343c099060b238181000041380d0710201c0b0f03900d0b40341c06040001444001a4555138011044095191f00c105581910030b441008490201802508008078184028031480001c0e24040d90883c0c10700da0301c03800191050001035401030804948218240940000c1c01041a0301003c6041520301030b14103502902030303a030410401203445944800f40c4c14201d0034000826040c0511002040c003550130a520003600804002e440e50b441078044641c9840c01400b804247c14035100c01c4a41001111054240200303078555801d012482041005014500c401e031500030013107501501204140740c503140111000c0c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 679452796 1250 679451546 679451561
    0x100e010e06030a050a06151403040c0b0f190c021318080f040e16350a020301090e07240909020f13120807152018180a 52
    0x1000350031410298540c44841c0614000d05000740c1c08609810450703032400a1b40d107680c01c81c0d42c14041d420814804164044a103400c000058084c0b46e61b20307222070620305e04c482d00c0c54001c660114000104008410710000c0140003000e01c501303940d000f401e010402181c000c048903801950040107030401c010740300d5007680300344080d14102d055070040f550382d5a0b80b003030540c1003007048800d66200841c04000d18240c1d4000c0d40c1c2d02848040760081055240390020b4461521108200701200ca001c858481d4104030060100718200b00000400207440c0070130350000030b0b510034010300a0340c034100310107500100310006420043c2c3da625410040f41c5041600c106126045a03007640041114103800041c0e00e444502c001c02049052818269545040031540c80c49604683d10195081501c4506c17040031070101d0307040e290302c25482460344041a0288410300301510101c003603a00242c0d0160350003035207040c0d03600080c214401f511840e9079410842d902049409403c200b4110080010340c03000a40b03440c0f05520104 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 679454046 1250 679452796 679452799
    0x906030c03080c0a140606120604080d052a0405041107240213030b1012080d0c0302071b0611010b0d02040e010e0f060f010e01120311010b1504090614100e 68
    0x45404e009510b40c2600214a80003d0140d90400024000c1d60b081440d07202d6102e150700d6005160a0415079204c1c82c9500c03030404080c00b80740d51034000c1a4100001540524800036400018407100029040c0542c107900c0f0348190761143c0d18004036030380e015441d001500d0040d40c024801c10055240c40b0601d004102080c000c40854690030401060f07041f0000c0d0301d007000741d40035080701141407420035680da10260090304808600000b01c14400e0000f05107008850070b808000d4400315026401c0803094002c0c0c0514040240080518100042c104c807450500e801240c001c0c1d95607440d8900f0084286088030000007819411141c40d03201b07038026050a802180c801100c032000050020241d0003914101080010085440c0e005442480860800c3c81032103400341002c484c21341142d51408070441741070040103000605200c5c28969001003048298040f0240000180c8400014103c0d100d080c030f1070768070138002d09107440d10f40b03000814a0121340b10000c5084038042c2412001091600041d11241c54a82c1c405 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 679455296 1250 679454046 679454053
    0x1107020d0305090607050a020a06022a18010902120a0b0d0809061603081905060a052e050405150a20010b040f0209040b0d050d030e16140108010906030c03080c 70
    0x43c0741d2a040e0003010f03001d01520103050640c051b4810088084c1d6540d00c4681190320020f0241070043c290422441c4011400f0103000344094184003003a040f07a5180b0f8982990070b409000000c10100a40080400c1956114240d03907990b03985482030203c0d160307085119000744004807a800010031440040c4040c8400401b1982005075000d2280d51b0040f84200450001e40b01c072052101b9920760520081c09004d03038030018045850b004011440e50302682c40340da84508004e010001c44503c00c410015441403001d00852000310055101420a601910a9601584007029404812040c84007540d0958045a23140060000450383c1c3d80d0000c40c8500e0425015540d03444240362aa0b92889440000300043d440075071504585401c10003103503460044070380241e0342031a1040000f0b03004900950f14410314100002c044545140081c50032000300b40d081e0202c0c0c880340b40031400d0501c40d82105c00e0050240d039040002c2e0703241c0d0f8803901920030b0381c44014a9850801028800160510050941100808101c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 679456546 1250 679455296 679455307
    0xf06030c03060b040f0503060a0506030a200a08010518070f0909030504120309031106130902340605010f0b07030c020f0402070f0c050103021204021011060711010c031107020d0305 79
    0x200c14469111703900c10301c078a4091541c1000a82010303c5003a03440079420340b040000e8030f4100d020944503582e03407070003c083e464190484c180b203444242001001040c0605401540e0340c80f4074009000b02019a0260346103690200c0b001c86249000854506440040359111103032481c010119010b001115012401c3c44424407000c102da0302001041d000e1940079a1f100d0001d9803071810407984403002c10301c000703004200030000e002517140c405111004584400b440140d5401c070030411031a400001c103501005440011a01048940f4501d043c64241c41c09000d0400c0140d03078507240c2034000051071207230103210201400310202081c0680040c864a07400a01f01c440b58a070041c00042c03c90b8000700c4100c40f00161903110206000540010001412084c01c08614005401d005081410002400240700d440d007500c0c046a0244244021001d001d04c500481e012070600b0000600042420320000140e503103441007054240340300340505080724400c3c68515142c01c0c0710b07809004141010740011790900904000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 679457796 1250 679456546 679456559
    0x30a050a021e060d05100b07120c030e120a021906091703190305090c120a080705010207060e06160207060e060d0e0708010608160e01050607030309050a06050103020414010f06030c0306 81
    0x1003138008155180084c5526103104046c4210b07006800643d00c41e130050200b00c3c00a844841c1a00800260781000340802a5038076040301d2900c00c1c48075440d0410026022251501c40016003220303446c0c42129400c64003401082c0101c6080f42600c41d000000365002020007081a04543d20601c0114401c00d880c40d08540f94060032003448103000c0000000d039900d040142c6a04240b201c410704a108a038010040c01e090000280e440c10034003001b4040705000504142000806d504071449640d100f2014000c40c02c002e411952180800c82e0042c070589c1000020400c3c580c0301003641000e540e1039841d0780300480b40c4103060000c1500f01821521545030750307401034040b2140802c1600010502c7e6070022401c903007000455410708070300744403944140040320014482c4079000791046041d5030041d9141c5132228100d050440190450748405840d600500c0c540100f0302507107411142c162070080d1407e0060007048034051401071400d00c0354a44024441c1000d00809101e0782210880702250b103030116040d91100d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 679459046 1250 679457796 679457809
    0x60806041a1519200d0509040b03030d0e010b190506030703181b08100203061c1a040605100608070f0f170f0a050c0c0a080d1e1406030a050a021e 64
    0x3c0ea000403403035580c4110581c0e51001c01c11444044258060104030b812094081c10b140503070703e121407095450765150031003031b06c0c02c10640d0019002004240001c2a0001d07185000b40f503aa0340e1b0303501482038103040342c4074405c01d05605000c44101401d000c2c0307140e60340301c07085000f0603008100c0b60750514140313181000706800040410b42d41200307405043c4a940380540c15880c000d00b010800785d40b03074014010010b607980c0e09640c0074068041d151020000a02d00d20f8011201000e00c034804c2d01115039041808213100c180d900c5144100001081c2d0f10110b40c55070020b40f0b440ca81110f8800004038501f4800000c1d61181c2c4030803800c0d418030305000141d017034869a880c1c09060308607840c1d030b2440704032404c02c01a50020700903981c115080c4403001d46015040c132040c0c0d403524002c00010304290350020b00070790179207010790041c5180303c1507416904109245203600800750032080741c058072303072009640860703030901c1c010440c5d00603507511600914036a5826800d0024104500780803030401a92080b042c0c0c4c0c152981c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 679460296 1250 679459046 679459087
    0x3050403020d02150705070509060418020f0103090c090606030f023a060305030702030c0405010609091a0a0b0901020120041a070f08040305070602031e03090109050313060806041a15 80
    0x1000601f00890912051100e01e90000f0f020a10803400c0c50308000d441c4801204c3c4804958041d5003403c0c1045039040103801a01942c10300a008071030010700058400480d5102d40c0540d1301d0f0f44d409000440001540c2c01c10f90181d80100071144d02d101c10940d000c40b500031852140d40040c0c9045085664001c0000811680c150b40140c4940c2c100050729411840c0c141b1004500c03100480d01040b00c0c0d41810001841030a06001c0c0c07400c001d5403800a040000075200c04003000350002271940c1d542c01c1e191003900308190050039000c0e01540c00c000031b000c00c0d058143d50b036401655585050500381450030124420b40c1b0345101020300004410000480880c0a001170007841c2809010910380d00c07451858018501061075010b40b04541040c00842e4070f1401104040c241c0d000600c5155480e0b46171103074882d004203400d0300020900e2000252828122001e211210120350710342c1c40300c0c02c4030340d1001c1c00d0000344e50a01d50007481d02c1c0b244649404040c90401c1c03403150000a08240e16007041e070203041d85103281140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 679461546 1250 679460296 679460303
    0x9010f050118060e070f11032a0105151e010309050114010f0815061e10030e0d02030301080c0402031e0f040c1e0302041805010204141c03050403020d021507 69
    0x4010b003044909403a4040c82c0020501c000e20200c132458080c2c002007401c410924954100080541c0010461400b0402d0f50130900540190800c4050034010b0311030000d80c07009031041d165081c6000641102c0c03440404001c1c40b48040c142111018038006d41c0e5401000d40840d0905243c1e0742c0c241840460300c01d02c10125080c080e81072000c8154106102c50100e542d5550000c0259804410004610401161055000001569101c039218102c002268400d02c48404841c0c2042c0c031041c03a0b800d07560713140e00b1010501c001e01d402d0350202102080c04036164802402175001d02d5004011580603401c06034021540400710003d50307507281070703030700c55400c0010420703590071413424002810b02c018400c03c0464600204030a4542c0b00c0f007200c0010100781c4519081c84042d200f40c0ea00d500410f1031841141e5400201c03039025000315521a2100e60154410421005c0d450261016518031070313080c1b0a14214444d0240c15071189810301d80b0315401c00000c510020302c03c0342c0240d42c01c10805207881041c0041e1001622 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 679462796 1250 679461546 679461569
    0x90105061203030919020406080105070c14010e150c091005090117041e0501020405060c01020d06050a0f0e06010c021201090213200304020d0b07170708160809010f0501 74
    0x420504000c030744408010a910260410024080e2502c0002100d601c64010244002160250b40c000240106840d90006000b54204003c01000c1603002303010a0107544254425503011090007191804c941d440344840189034040c1c441e410545841d40c001c2540000d10a044601d800400c41c0800c01c0c1c6402c01d400c040c003184010401c0c145a60704080303179154036000a15000080c0c5050345a0000e80d07109450440701c109541034807541130006c01e40440c4c000c1d0002404040d034603016109a030b4003d40c808400403003010301c0e20744042458900070a000040f205902e115031440c5040c000407101d88200901100d060010b90303908400181c4072601c00d1032440b00c0709800010f1091846c01800954404540c4207000c8a26008802001d42d5004420026041d001c040051701c0f1307561440410640400428040e100f4400402013000c02c9622400107281d0201c1c0c20300b071420645600c0c90540e100302080c1d40783c80807081c40c04403081d2494400d8001c10380c08820600082440d5540403080c80441700c4c00c1c0c200401050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 679464046 1250 679462796 679462801
    0x3160303080f16081f030221100516050a271706040816020109030602040e0405070608090c0d03050706050f0106020c120606090408070b0c07120c0b040803071205090105 74
    0xa03110708641e800b91451004501290038820010080b035402080017681e00104004050011201c0030628040e6030f000c0d00c0007004446045041e40300b90104600a82c540c441c140d281c480030640c60040e07500131194405401039a00d00520191555044684214104006104552a0040721491440d000401d04c43c0b80c00c1d100741440c9544da10000704901000090348810140300008100303070b0444510401c0c3c040540244003152004842e94425584003402c202d002245c046052001488401d000b9449502110310442d61030400303441c1c0f49001c030341039003203600845100300c00c1c1e041c804810b5031241e20a16015140c03031155034a03101200e1003551a900380064500040c04290740420880c02109421122401742200910700c0e2079039960020422401410100045030411003081c0946248940c080342005240c038201c8107a0380c80da0090101a02c980245a144038000d50151410365500c80d00001410b0389559923071110310081c0d101502c0541045080010401604100e00c50140500e031000008903060 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 679465296 1250 679464046 679464061
    0x70c171002030f042f0909071707060e01090320010c0b0703150f050d060e070503120304030f03050f13140a0302060f0601020102040f0e06031e0102030711010e070902090316030308 79
    0x210200c0f404051040c14028003584c076004621002801c0c50454086e14190303a91035000741400f10f80c1d032084200e0f110405403c0520040070504005403421a074819648006100045130074030418407003d07103140002d40c11a030026030300725040d01507044107040400741c0314200e070764000f0240d400711340020010b0359680c090120300d03007401000c41c0148162420300504d603041c0400030b42c600e00e0181008013072a0381c450024800c10320a100c80720040a00030107540b031070010740c0f01e2500c0caa401180c0031800038240c29404410700d0301903c6101d010304855850301c4a1944c640d4103c441007201c0c1e040030780c0c00c0701d1034042861a180b8100401e40f0240d12a03800f500c540e0428480310843c220340038190030b040d64018802030203c1c000d00c403200021603108951a0038940c54643c0403a08059012510508810303401c6851443d00708150010b500a16a542c0e50b103440c0600c5040300c03401c85540015520a03600042c20030450164550060041c061740107055030740a80110f0024040d0840a03032080b40469286e00821a28 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 679466546 1250 679465296 679465313
    0x62508220c0311090c0a120506041503150b04200d1d0d080604020903060708040f020301022701030e03030705091f020706080c190f020a050f0120070c171002030f04 72
    0x45004c05e2065820801c0c1d110000c0d202c5040e80300310011090780c850001e00e844d5501e0b004801d40d02c541c41046048079860303050040d0720040b51340c000d004550070001c0113403803030805205998149a000101c00615400440b049c0190390040310307555107440e29001d0104000845601d030746401542680242041c030b007500741c00303409420700501c50fa00c12841404540c15a417008951581c0c03004413071503e90402d582d2840c02d40c2c0c400c05c034014081d40640c40405c240780580403056a180098050389850401c86290348011401c0d56910005440366800c14008140510701440180583d40802410740150a0781540400f0001c07142050150043e03105400400034150050302642e042403600c103160f403130010300c00c0c8990301c401c100589a404203c1546000c511180c0701340008020381d0303172240503200313065818842d0601800102d803440d410040c803900c1410840c12800b003210303030055111600c070201901e0080b01c0009070008580701702c0180910100c06c0741070300703c0e0320095210745040c00c2102e000d03003060700f450001d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 679467796 1250 679466546 679466551
    0x702010204080106140d1b091503110f10030f0209030f01050a150803040302010509060c011d060c131707081014100b122502062508220c031109 63
    0x41400005c840c00310700c0c2d10740d462203d625542091003040c100511504c1d2444040b040d0740880080362800c600054040e0a54691800300da01410f21001c00c580b000d401c01c1101d11810b04640d07402501240c1c034131401030003a00300c104c00c0248101c0060402d20b00070b01080c01d001040d600b4074030595440007005410b060034400c0c45000260508a00012400d0002c441e542e4855070001a05101000c40c2816040c0c2d1901d048a281c00400402401203880c10042c0350745824480c4c031001c0040c0a4507000403254003400090300c0d0050581114403a00b03500e491440c0b400341111001c49502801b403442c01040011040185071b01d061b1100c00c000a51b03001c0c070780081d151658080d14181005024600802810ba6003000342c0300d40001d00d0003400c13903d4076a02c5030700000d800f00c3c041c5410221508421101040c1d004140c25102d04217503440c0d101002c40541da00308185580c41402c001142898000c00d070b1042c10403500c040c03504010024000400c40a0301e51001c3e0300c4050f4030803104040c0040c54210941811540da0340c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 679469046 1250 679467796 679467809
    0x6060b07020109060305040203010609060306020304060605011805040504020a05030607111605090106200607050a0e0d0b0c0a0c0501110a020d0206040510090503090406030b040b070908031605150702010204080106 93
    0x504100465000902e400800c4c4925000c0503103940c0403500b559000e6100c1001411142002c004e40c0c2d544e0f180840180d00116011341c0e0b85440c140c0000307040d5000d512000f180342040e8201d22078050078801040010b050140c0143d0b00603010807004121901c081004038002c444a4403982046410100140c0c0381c0420b422001c4d4a864180c10100b01d282c8412881506403945800e020115500c008100d0303600d4001800c1c5034a99210303c40030301054540160003041000842d80c0c450b02009082d03014000041c42d03512005010b900f041000400a00041c070180481c3c1c801c0b480d0511018403652034050039110ba940a040340d42400140314500540c040280480c81d40705d41c009885145800c2d143c9a4a41500743d50550781e8544030381c1444200030051044400c0401c0044c805c012640d00ca0510480341102103900f2200100d8110200b0700b40e0340680300307a80031142f4000c021403074148594420500080007840481d003511038241c01c1150400090611881250207500040e00e0f45d203440c207000d083d103015504c0079 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 679470296 1250 679469046 679469069
    0x706020d020301211a2505031603020f070204020c12040e16030e060a021e030c0a030506060c0601050d031704050a02310c0c0b10080c060306030307030c0611160606 72
    0x144009078260150b50010803a00041765526900c4801900180c5c50a0768082c8903400c0d04808280010f40000c06140110307902d408030742c00f4182025041d4200c3c840c04104405e02c600a0082400514140c1c0007031210074510003d40f2500b082140c7c030144640c2042d005080d80000c85010030401c0e80e0b011252210b11552803800340300c1d03e08410005500ca10300540150800317a0000380103000045103540d1400d180b10840c81071541c038901003182042c81d82110300300500190400c0b011442d44d1900001741d4040392440070240a059280204200c605501d0b02811000c2c0401c81180e201003e00b00707030007a44924064400b03840303843d11034410060047c0c0304145132034032a01002c014604404000e1458014025050800100709408020642d0782421a050042c2400619020000400000c0200404660001d011a2842c1003002c0c10004079000032107840382c0552040c8508000320b4450103000181c070780a07000000d44c00314160301680d240e40c414408407a0440d12040c10608002491261100410040032603 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 679471546 1250 679470296 679470359
    0x22505130221060d0204090819050405040501120c14011b0501050f09070f06180f081c030204060e09100305060a1e05090601290403061406010905090a09080706020d020301 75
    0x2d00c13194200e900190146540d416000c0400122500f1520000801c84c3d00d845000070301d10005001c1e91240c01024016800c00c000000c0d80980300f04001e042940c0b1044d0b001c541c40c104250f4082071450100c40030304105890082e014030000781c0c020312040d940a000085050324014110b060310280140c042c810300e40c824141000317110f00501d1243c050300c000d86010031061101c0e00c84580180400d03005001c08180701d01001451020001c0c141c1c5902e89200c1d801c40c03011861000c1138080b4050380c4a040007145078440b0701c046601d01a40000e601c00c03803490b69042806e13200d81314207290a00880d00c1c040415940c20040005401d40c0080c80f0840c0803620080c0b205241c08082191580c0040c46100c4c0301d10540d0543c03c072490081c140000da0025000c0d4015103ca58a003802e02c064a00480302131a190405404145507512621190081e2040500080e00c40e8a5600105000b4460441c0c140c5461209001610000d031080c0010a00705c4400f0300050b8480d4102072400e440180e50048036141901c03280742 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 679472796 1250 679471546 679471549
    0x171c0207050d11100c0e060a0206060102120a020705060d0f1b09050906180709230a060f020601270614030105090a0b0f060f03100c0809030a02250513022106 69
    0xb100d60500d130b0340c0480410041407510065401d05044054654480d401180c02e0041a0740040c4c064401ca60990031200c1d000440012500c0d43c1c8109280a001a003104100340200d040007002415500919200060064481d540d50380443c1c1100700b001780080c400c0720740741c201c0b035920850440181008403000c200c0c1e814070a000841c003100135070700c1100701c81d01c140000f0382c0c04c2c2c01480918000c1262102811051003c40e85581004140306282881500d071004049489841030403800001449a0000e1549900304403050500446d250041c40c004003000398038441c00c851302e004402c02040c0c0c0203098003140524404060079910014862070656100561007804078800e40c0b000751300b0180302200664603840d9500480c40b81800b001340340d40c26200300d4a140f42c1d0904140d00141c10802203a890041035102c0c03c2e8503544a20501e4064070040e0b0002c1c5100381b008490001d2000881c42c00e050a180e51982d42c4003089001c0c4a440c2031442c0d01d40d000c68010761034210b02d6010144e000318486c8085040c42d0400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 679474046 1250 679472796 679472803
    0x70311070b0408040f06020601090c09150804150c08090c030307050303041b0b07080304020907140403080c0c040606090306050703060e041101090503010203160306050604080a171c0207050d11 84
    0x100280801d011007000c00c0078403286204130780151103035035007103500d06840e480007a641d28420700c181c01a040c07800c004403c41c0c0d4401c503a02010b94035034001a151680c0386c41822180d0001c00342058608400352007003903900981c54410000307603a43c01e46486000d03107406218136040c080e03a040818003a4208001c144001030000c41100d6100780e220311104182e44445490305030803135480d000750710000c000080079014007035a1409940300d188200d44010030b5994803001101c04042d007008243d4446000d110500001c1c112101030549003000004541c1e411003a03000150aa40c2c10790b00c9030340842c04c000400e00911426004265018103181424444549480c1e2500c0c030240008001030006420210030f0b01c43c5130712400e1700f1030003404000d000307544a040800c074901d006580051204040380c40c02c4000121414100191004ca9642002a1035500c045444207182c0e01e04030850240c2000b002c0208007a415120b1104641c41d08040c500103840c1e00d12031802e030346000e12680c0a8800d018403085050040d19001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 679475296 1250 679474046 679474057
    0x30f03211801090809040506150901110309091501021b0105030103020112090c14130504080a0305060a0f06050d050c07020d020f03150a020316050a020c010f0c0b04050d0206070311 79
    0x40c0c8451415941d140311038111114988100a00b54240081d40342400703541c5004d040d040f81e04560030056a10354008001401c04118401d10100605000c6201c01d980202004403440310040c003a286880c5c0303820700040d440c0c1421601d44028101d40d05100e400d559040005090300d0700c44240300143c80d681c8500280444c00148002410040111030850007003402d5041000046d5000c0040302c0055203404144460a60f4580014080c01c9003104c40e14a00103a07000705c0e401207410000007450702e500e46004801509000341050780000011100080c84004260941d00814082d076600d92100610007411081d13039400303016204070030b20501900c2d000d651100c0c00b0044555040340d9a40f409101721012a090032241503007201c00461080c1000341d8590300d50002d522640040ca9621801140204107079031038081d044200c00140d102c0124810554004c03c1c5c188980400b50511900300301095423080400f00f005ca03412103072038228880111036103404014103a04076515040034090f042914403030328564001c5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 679476546 1250 679475296 679475347
    0x21905042103050c031804112506060f06020c09010e06010206060103050a06052806090308040b13120302010207050606030715210905030c1002070f02041a10020c030f03 74
    0x10078000008243c091011107411041c80e000340c9484a046002c50110488481c0229009600b0002c41048003503844044510034080821074044900e0710491003a4461303050b0344220360183da56203001c21403000300e040920082c0081e030b000b03022242004040c40040d00040e4000c90007070460406005031a81c02145165002500b071a0000303655940440e140701500700741d80015003220f40b40b65100c0b160200d4221010a41c1c15064200c5840c81e51494111413001d254403001e81b4450b0284400c0c824041c140001f4400050792100c4030840d25201c0030040200303200d1250880140c0c1d80001c90808010080c040d0700d52000c004c6000e4030302030b131410002c1d80c4001c0c091a2800100101c00c3c440c61664a1403420181100c10000700404c00b0b0200c40c90055a41e9101f415003032582c0c4142000148a40d64900071038910315031118144248400a500784005003080c1218140004040d444652143d00d6004c00a20303421780340e500800d07030403003510285420459851006246178208002c011038029100b04e15100800301d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 679477796 1250 679476546 679476599
    0x5010b06191d090420040c120501080f0a120c061a130912030e070b0301081e0307170a020c19060f02030313031b06050118061d28050a02190504 63
    0xb2004081c540174132691205501c00c1c40d0030310b0005804d60010601207641c00c401420403550b40c0700e00840e0744c4d0318140c0400f031100340d00c82101040004c06000181c0424010707403c2000d9403906595403202551603a16910003800d480d03010024003440c1c101070144441108000c10084038186e44c84030741012131040c4041c020b040e01c0d07001d294100750f42081210001d01d58043c0d115120350711680100d0315113075040c0040c0f0030710340c02000d2440130318004421600100e03484840c894031032404004e142e65a81002042406500590b4200c003c00d88582c0305182482d041f0701ca5806106080c01006021036004044880440d44244100b0481da4412000a910035402d07083c00f1140b214120507410321043e40e0140104018145000017070103208803480c225070030118804c18004c40e0745a14424080c00307030052400111064140101d24161058041002441c0703500b0403c4000315022184102071720801e03140704c2845940000c215581456011420740c56140d40c0c580949860700d000e140c1e00c05810100d550a40514 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 679479046 1250 679477796 679477823
    0xb04060504020a1202220801020d0c020d08010e18100b10020102090a03060b04021917011d0a240b03040b070e090711033a050c041205010b06191d0904 66
    0x241c420046d50b140e40b2512200d0b8040c0740c640708428003035004040c0e49050315041504490050b4000b20700600ca04819031399a100613840e201c01c066040354003411462510070443e084d01d01e2003c05002000d0420f804801c00701e1a0b4210105024106503903140450031a403060110b542640c0d85c1144001c22250001004100094038100003402841118a044001c2c040c2400e400c0c003058000707180044962400b0000300180c2e0340d910400074074100a511302a02e03071200c400092064410350f407142c5100801071440c50b0801d800320b00d40c408001c19942181184d00000b1041004000f19480d60b1640301103c2e00d00340c0c03001d07451440440c84040e4040c01420900c00a8440c61071894020400c0d100d42c05000b110032614039206004c407020001000a00c0e000c00440c0011441501040780106401044007030f2203d4642841c269042010035070080301214155201d4605078400d82d19000034001a0030405100d0400c0740d0804006402e80d03606601211410080804809099603455003096100e0b030004800520302 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 679480296 1250 679479046 679479067
    0x3e060417010b0402070c080f1b060a020c0910030b0c13300b01061205060901050d11030a110a0909030c06050a1b020606011b0c12240b04060504020a1202 67
    0x402c031030030340e85810900c00f040c001c05100544002c0011a807822064886c010b8140400311340b40c1c4004181001182c140008035002820110004d02c0c0c40c01d03c610582c0c003560b00d282d0000b056079109452017481410105020f0050101881446411028000300c2e03c3c58910300302c21035240b0a8813032003111030451040e1041013480189000105007401e0721416001c071804140b03401400c407442805000700044802c1c0c045001c10701c440c03291078001d40004100c3c8103203a1810f010400e02c0c668116048031440e031440c180c140e09407402c001e00210385110301207800c03807400b001080c042a030038194000314600d820880310b03101003500314600401c000c0c3c020001040c0d5650b00c40d00b041c040d041d0f810320020098007150b2807100540e400b103001c3d402024240d844080720741201c401c00202d000524406402d014410504120700c50b1141050220b692013001b100d10045092901c0709089102d103941c2c41092a100e0060101901d0644070b060064081110111700741102d0b000000c0180903da80601945e0758001210004d2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 679481546 1250 679480296 679480301
    0x30408060705120108010207020f0616022205060907141602131b050702131d0706020708120301060219030e121506040501080613020105073e06041701 66
    0x500452421a080303800e0100004155a000c0511200b1541000002140004060003190190b40e0010104400488000100003965110101010301c0002e0b031440030300183c4618840c0d018803070131140a00241840e4200310025601c1c0104140d00ca001c11200b000301040d0462035407070104585004d4103480e00b0440064824064144402961010310300c1c8803104d0010a5070003118603030441c6c1040e40c401281074042500d49002d607000003544207800e0825004400c40703941c0403521840340d490000b404010b0440c0a00c0c10110990410340041e000000c061044030001c00c15191440c0004c40e446207590314040c4002e45801c0c001c0020310301d01007458a030409141c45007214103106407000b8104030320700e2104003e10740e50f4200c0110300d1000d240400f000030b500303161070300c1418100c0b80d005e000360031555102d80104803007a100c1c210890511009008023004607610f20401c20b6422000c1d0403206150000302440e680301c4541050112242c0110404040700e0784075082038070300b200d1a510300968140107003840c2501 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 679482796 1250 679481546 679481549
    0x2c040204150308031b090f040f0b0a0b040812180d05330a02070308072a030905010806040615050a0909050a02090111060705030c160210050c0c04090c170304 69
    0x200d030a101802000703020000e0004c502800302044204808190303070441c5105402810480340d8071070860079148440e402c054010500340c40c0b50f844001100c00e285000103501c84a1034000042d80e03140071405000107502004152042c0c90036025882c2000188010780e00d0203450924414000c13500700308407104010081100903801c840030400c208601940b18200e88030344d070780b652060391350b64007003804203800c04498400c50307410030b805907510302d80c690b100141556203074902d110108031207210b4400745a580c2c0e210100c03090543c0c4641c0d9001c1d00d4920f404c0c001403080d41d004e04181c0c03240b80303001000c00c4084072101d01020404000c2c18080e48500c07038420305999100316a4031200d2280d08106c03c00c420642c2e968000e140e030103800d0b2210b11500c2d01e031080d015580c0c02c0c12189000810400c04c04100c288103128040e12382056aaa19140b141d1419800b0030035460802e8280300205d040413408010030fa00c28071140c0c52103041501c0801a1003a16114406d881149110b03594199100700d1400e000e8100a004132070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 679484046 1250 679482796 679482821
    0x306091b0910050c2e0c091502010902090609060916021002040311030d0503070f1803050307030207060914010509040e0106030c030b0a0606030b01020d200d08040c2c040204 76
    0x441d20a82d50402404075070140c10b07210b410b03020344400c05491035100c0d00c092a0410311203010119500c2421501030040401604a4007400761880001503490440501c60394003e11660003c1351b43c050720320510001110161103103116000100c2080a03507100c840036640d00c006d0100340d9010780d09030f81c41e09905040d110000c102d03110340000303400700504c04901444105204168200d0b80229081c0c9421038503800142c0355180041c0e400b9550030320680c42080e407030454140708441480b104c0c3d642d9480601d9035222140860240e04511000c020854210441000408413884014036445a400000b0918424601460700c516135a00c4210308140c005d5210b42e02440d40300c000c8044550720380c240610f40d202d08890202000c0d0a00303002054503407003800307485515401a0010004000c5a00f400c0c0c0d58042d500004801e0415580420024044204004c105d80045c58a5070007090803c3d0400c0c8201c140c568004510030504044000070401d282c10070043c45560004601c41580c8a500c0040c0207882c2e40c20b002c2c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 679485296 1250 679484046 679484059
    0x5040f0632061305091b0120010c020607020d0512180106060c05010f02250f051903020115030206040e0c270405060a03030e13060503010608031308030306091b09 71
    0x1001c08055010190302520088441d141e01c00c0c2c0c0a5014003e4580488035000282c05c07a01c030060b0809a507000401010105051000c2c10662034041c4240a000581001100313070744401076507000380d4050140e01c1d084401840642019202e001c00038029109991220b100007401d0000100c04a405a0101c614001d03618000e014969489000402e501c0d9840c0c41950b0b6035184c8480610300b1451071080b80c40865040000301021b5030544006220b030910b01e0307000e54401e07004804800008105004035060b510405119600c81202424000e003100d512012803140031034011810700160b0364401c10b4401710350081c8a00f0302c0540d601c6140c0e01407070080a5109413031102039a0911070040760b00e054084d00000a54040005507240d004000c82581c90748030180200c1e090004d0f101403410559003540402c00c0da640b000c04c881c4eaa94001c242150b1442c0d12155440d000800c0e010900d15401c180d01004100c0640114118141240043e00045010340302860640c80204500352882043c82610000d0f03e005215 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 679486546 1250 679485296 679485371
    0x31a102c0316050a0f0806010e0711060a0614191208040b070f06050f0f06060307020f0f06180601061407060b210d0c08030c130e0406021201060305040f06 68
    0x42c0c200d02c8038640110362140a94071404511034880503107030740403101158001d24850b440c000f514202458041c0c4076104000090004000c10807080141a00469041c0e40020b90549032296103080311f20030801180c8104408402c6080d040b0680c41c01c001035919400000302d01c0001d0786404641e42c81550b101090300c503004150030b4203014010400c0030384640515400e010503900c1c80340250f00200115180002204014049640c5042000c0615030001351801100c0181c02e4410381d540c81c0c2071005401310707819882030b810018650507060f1158021019140148010350500f040600341c266000d0380a0843c00c40410000103201954002c1c89a191307000c1c10740511081600b2034105490740b062500f8482d88500c50850300f80342d2085d0300e58803030139402045d42821515290307d600075a0b800000d507800c445080020100c3c0e15205030707103002d014501c50500166034010680c0480300c42001640a032081c5894842000049111400f0701000d5541c803c10024000d1000c1c01c0426005e1016410340c1c9206041a46 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 679487796 1250 679486546 679486573
    0xc0618030c1b090604110d0902130608030d0b030a050601270c03021b06060307050f0612090d030b01090e010e10170d020709090201050f03090c0d03031a102c03 70
    0x20702e40980d907001007540c0d1001408245c90b44140504580241009400045c0309aa440964500d10050000e00344162181907038050300e0260300a0415a08005080610010b1511030038054007415400740c00c110000f0b865043c0c0341d260500c12504030044030380d480c1c0b07400f0401e6280f6212445190004004104500c80018029040341c0034070384402045135032120545500003034a5106480041c000c0c81e10504050034418981c40c850845134102805000d000e890010300390242e88148120802488154050706004080d20b0807548194180850403c0600c00180c02d1a085415501c00c040322074082e840d0008001101e4032164400343c01400200182c0008001c04180718101709542d0382243d200e652110720040c122404a503009010071410021101d410221101039907001a00d10103440c0e20080c02c034041603564150b207130b044000030b5540482e8a000308031211030315020001034844c21003030703c0081f0b800790910250415014030700e1900c02d02d100342a041da03a80c0d60b04460018080d503000f03021800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 679489046 1250 679487796 679487833
    0x304031e020f0606010e041404050c13020a0c0201050a1209050309012007170f0a030e091e0f0622020a0e1219030c0b0f07140c0618030c 60
    0x218420031511492103004a64400511801c203120084050041901e80c10019202075003d007043d1070b00143c80f400c2c6211066000201c0b07034801e43c052405000d500c00d4410402c0800d171100704440551a00c14020a021503030f0044400c0c40070781d030a0078219503920310401c090b90040000060039120b0b5051000e6601040301c0400a40360b41c3e07800f0303200d4035002145c6848000c110602070002038090780c4131039410001503201c6003401d0315a600803c04e40e60800f600039041428411154001d0300425056188083d040c20000c901e698060800040c83e04007070b481c03030641c06000c03001802d401d01c40c1c5001c0002c6011640c55003006a04641c400c0d140190091345103403072001a41142020724040350030301070b080c205400c1000080e43c0700f1031411701030058503410010716181c4000b070001c1a42009581941c040c0041c1115605138000c031009090364040c0cbc80c0c8800020581c3e1410044640342880c20700c0604184440010841d4211021114580285800d01491843c5000e4000c4000c0c0612602461251651404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 679490296 1250 679489046 679489067
    0x402040b03100b1c26130b0408073014030d0b030114330d080705070501031817160804030b33041d07060e0d12081b030403 54
    0x30740c0c0a000020080c114007141013000b00d0054610246810781e5010014903a01d0682c0340300740d9901c00381c1042846c406510141c1c072140c1010f0340c3c00340700040902a4081c02c021303c10003002d001060841482c04011502d9050707600c008040f16403001514803400300064001c0380850700c9060401c907910340f0380010300308000d4882800024005c3d460b1449185d07a4510f002a031900c503080008507041d902d00f904001290f944500c2100c03c5c100808241102030795550f03840308000c950f020310042c1d0303181c00140c18020f050184581c80711b818140ba1001104988085001a0080740c1e00841003030940100c0c0b500b4941c141c81000d0444103040c0b01d42c48800c1c100012140540260f034000e07040c2c09800d0742d61000c8101c41c80c10a00950443c01c0301000c1c6000070308483c07241c601010b00c000d080403420704c80300001c8080900741000d1214240d00000003d01c08994410f90000b40307148210b410107044686a102d00c840b05101514002c100905130002a102c0005c42d882d0980d10a210303407080340d59140c0b5040050900480 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 679491546 1250 679490296 679490299
    0x4020717030c0d0f020c0a0b040c0e10050405070206100909050f0102030c120c2a010b151e180405042a0608010e060a09051305030414010f02030f030f0402040b03100b 73
    0x40c03803c40b07440814540f0031b4880524041004100030400c0c0e40358015546401081111051034000e004618044100344039801080351000d10a000307400d0104000903078600500f1041154003d60420a28410802c0d0020888011081c00901c0c0b032032508041d4144407900214003055030000007408609035084000b440c215078980751000740c1c0d4171050100203252007a94206000c04284c0b4080c21000410001a8824003511b02c0000519025100100d4408488260300192072480410005401d1035400c40306c010301015000d090b45002c3c108007590114149503024240a07503520340014041090000160024800c1c10050034443c08540c03c0c1c9403c880c8180c040c4100003224080002050b0b012000c2042c00341070010540c502c15818401400020311000340300001c680c40240102d40480c03000c2c4010000381001c4040819401c5511001410180d06082d00344c00310345c01044401160005081501c0d0052241107060040d601c403400010003900d0a5040c555050003509082c0300c41000c90382c409580c9800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 679492796 1250 679491546 679491551
    0xf060e0109060503010308211510030c090e220507050f01030908071104021c150b12071b06140412030203010b04291207141804020717030c0d 62
    0x2404004403404055403051102250050005000180c0280054006818020b41c0d403640713210390b80b450110b60682a00c402400c020509854085410441c480a14141c40c50809015491801000030586c0a0a104811949103850046038800340040840083c060440600206201050811a8542011380718240c0310f00f0303c44401d081c140d4000e00800c0001030700004014200510b60f1580c45c48400071054650340642c2c2004540403030010800d40c141d500121042c006118400750f510320200084135040120100c03001d00150060303844021206078070684914045407000103500103c242804405002400036007008400c550707800320108034034855402000a000500c0c29624280c040b44402e01441d011a1000c010030300c0b40c031041c280001e098072a0180061150a6010412035154000d40d4240300c2c044025018031080a5101d805034040980c00580e09217401072400c404030105000401c19070040d900400c4907024410048034120501d0100d1407040da480c58030090003a00740e801840b00500380d51 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 679494046 1250 679492796 679492817
    0xd05100606021209130e01060f0e1317072603250e0d0323040302120102091e01110f0606030f070e0f060a03050a0f1e0b010b03060d0605010f06 63
    0x1840003400c1d00d8090014543c0300e00d4150000c0c103115a102500180b000b41544821052001e14000d10944000f401d080340d418003c0c40c24807400780c0c00d100024106492803243c0003a420040307044100b0910800e980501000da0b20440c500d060000d61800e607100f04260b008080314120404007110042d44a0304000080d030465000c0c0700c3d44580000c0c0c2490422000607582e560f104240d08240001c061a10300031301b48000010318403240115a07200c1607501c0e402d01000407a0401c210704159031010f1010030076900a40c24000303040081189001c4541c4541c2d075150103035005500590081034441e6500d03c1003802c2d10700d02249451034655914003910f15a002e88120780c00501c0e80500880c000064072402d200412440c0c035161400100307450044c01255001d4111a40040080d004003c5440420311414005894800b03034141401001010759405c10a10200d0190394001000c000c51141940c0307080070180c4d100d446400110b21000000300008105034603290004c52000500781d0031008a030fa041d942c4103e0340 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 679495296 1250 679494046 679494059
    0x60c1b0d020102211501030f0204210c060203040b030a0c030209040e01051f0b0f0c010b21060a020306090f04060b030313050a06051306080a1506320a050c0c0d051006 73
    0x40d00c00321400170421007680031502c0f407076120303400c800a11450494094203003078694640844e41d041d00c20100600d48002c09200c0e08005540c4042070080803140085c5082615090301c14555100040640d91195030310070210050f24000d074191455501d02410812402d01c074440524000c060560f05496a0f000700013949503802c0000c032184040e54942042107081c1504030750304c26060b0f04072170240d040654075488100040e46514021400c41040703079122080b8034000030308083c20a000580040c84a900410410285464201c6403d4204031001c6107040300c0d03640c6040141c018030200180a6050000103540c840c0d11501050160a8030412102c0007030150317880300107440030300c252840e403040082d0180042103030902400070941c4c006040c0b07001291055078210009030803440c0750000c4001c281c1c0081d950b003529941c000c0030142c801007405e26006103d201001c146a0740104002d15003080300020f00c0c0c550155060100b00e180090292100c00207a42c685805502c0d240510328450381a0b01e09030002426 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 679496402 1106 679495296 679495357
    0x906031c020a06150b0f0a1404080106061d10180302130e0d030b01080a02070809030109050303060117074103070f0c05060c1b0d020102 60
    0x3501e200380390010449004d00013452050300428014420009240100c80949580d00300c841e8444200d21800c8618000641e0808040c000125000600300c1701500100c0694640b500d520212504041d0314926500f0507070300343c640c4501071445201100d405460070702c00074808060601e803c1901c940104a001d500b00820340daa01e0350b28100e07101880410b012412002d40145001d00c2052202400240300c034101420182280707078001210020448014200c521070440034000340079540460030501c1e00c81d041110000c0c08a40c5104c0300700c2c150009111000c3c400c04403030701c411100c4011801000c114208140b0402c00703101c132100070400780c010f01d01c5809070100e180d000d64a80d2031801120052280403030700881000d000d8186481400610301040c07640c0e22098002186494100c0c0e08003050002a4195001449000c0e007982000c45560640040800320020700b4000318040300d64203d41c29 = true := by decide +kernel

theorem cover : BRFrame.Cov 679316546 679496402 := by
  have h0 := BRFrame.cov_init 679316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 679316546 ≤ n) (h2 : n < 679496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
