-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1688
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:13:45.784288+00:00
-- url     : https://prove2.me/submissions/33dcdf57-1559-4deb-8319-f508c3e1ba7f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 303417266 ≤ n < 303597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 303418516 1250 303417266 303417269
    0x50f19030902090f10170a060c090501020708030405060a0f360509091c03020904020309330609041403070c0e010f031e060b100806091605030a0b010306050a0e01 71
    0x2240b80d803d004600e4211040c60f4145c05080030658400701d070f070306108000010680c25212403030180f18007040040828018443d207032510b12070b556002c8140e8984400245041d4068100020b15001008100012380e0750104940f03440655040181d90034140e40b0040e54410f594000c12000408402c04104000341c01080004005000c2c0c00062601030319501400070314401183c201e02c1613480350000c11054044844401070b400b555240243c0381c0301041c00850143d0704151809905684500e008000840e86400040681500d5013140c00d102c6003040750700c071a8502c01600b082d00a4450710301140621468000030304c28101c211048950301d881624255104226a2003840004046400041135003030300460781d00100d0790050400c012108103a609865600e13003860f0121030b801d81d110040f56440e00e541c42c0c002507455054803100f060349480c20130701006400050042d140105584110420590840709403a00710741c00c9800000c80c250340c080160014080750308029440070a0000c0028240d00d840ca06a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 303419766 1250 303418516 303418519
    0xc020d061e0203160e040b130f0605030607050d110d0203072d0203220e0403020601030b0606040302012a05031303020301060803120105060715020f28090501050f19030902 75
    0x8181d4420005940124081900c612003102e141418400140340b240c0707980304030f414001b400041c0020080c0000b904c8510b590b40010f2034247ca030b001082c40d44c5110700c03d02005000617800360446180c40350004090744240052106031319541c100701e60909402d0400d0782d4104c0030f1b01c8170841d62030806000207850045404540c888000c0c101c0c1c00d241e6070380f0215241110f1500250003d604151a404416803c11032074203035546180054400010202e020211060080340607401800655040d0b082210001c1e60003000d070790081c0c404000410050b40e00419020f00350350381e00d0854940b0568002881d00e1101c4148024003c0d20001c1000325001890311410b0302200d01c00c074020407500d07549088040d02c901942c4141015410128010000d5061003001000e100d4840c903c2914070003140d07014001286c003c0c5200c072110100201d40c0c00c241104602102410003000c0c00c001c480f28a83c200010020300310b03401401d040207004680c00c41605904030690301c43d460f040c40d8451540300054002030040c4001d40099 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 303421016 1250 303419766 303419801
    0x60c071103072411031204020109090911040e1c09140102010504230304031b03031d1513031406070906081312110a1511041d070c020d06 60
    0x105040c600000c8a100715407406044042c15418200703010240f2440b004040b0a12085501c8032855410a03c010541da035510244180c0c3d5042a00004202d2011780d08a260000d1403c100807012851b074072124001c100f4101d5001c50f02c1c0f2582218581825101800c04500403c0190b074040c07042c2d0440400815600107009405110310f200004900341c840596000e841164050411007100c00c02012014641280c0c104882c50a07a50b6035484d6240485500c582d990800c0050003441016445094a0250b500041c100700303000004000240c402e4510092524440300005031002d9441c54200d003101c01590000003a05614490140d540d4481e602100c00000040c1c0080012440d240079810f8030f80500784204440700f54001c596140e000c606454507a1000388801e440c08030b000380c60100f02c2c410200d4841c212804902082141501c203075620302d0020040c41509000038007071383c40b0304080c980c80580150416901d40d1a090400e4508420151300a9001209011468180211508403d20011808808 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 303422266 1250 303421016 303421043
    0x403050d020d0f0f290a0509070f0e0d0b060108060a0b0706050a05070c03020d050a2d0e01020c03211201060c050d0e06040e07020705030d0e030f0307020105070f0501060305060c07 79
    0x404103d03040c8108010f200c42c140b4165117211044c00c1025840c8038000381c0904505501d810014400700c02c00c690035400148020000c80d03401e9800940184003240540718561981090f564001d001440208800d0401c10000001980c6994042e0020014120040101d0b5541404c0c00d148018203800c4441448650600010401d00c921800d441d00c0010f405901038403c1ca282c80108070360540c092074125040050740c0c103d0b0060a0409a040007000710310309c695644940076024040d281500c45e81c00305065421204402002c2e031408944e61403859907190f08074250080125034940a80682c004c02d1480c00881e90021034401c0e00402200d40d280d0141088400c02003030100101ca000400c807000310341200c030500041188030581c0e51440d0308604240161040c0039210400301e03290191552000d00001c14010324940300b4107062007000c2c9507209030b40165181c40c0c09500040c1c01480b8492004100e00081080802400001e51200700915131050036161036041a03021380106030014802582c465038030005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 303423516 1250 303422266 303422291
    0xb010e1f0e0f060322061d1005010609140109170706170709030201030506030a2a090501081b01020f1605181302091509010b0c150c0708030403050d020d0f 68
    0x2128262076500a11213843e55070f81c0345180d113040104803e000303040c040d03000c41c810020303426000303281c2601c585a1008401c0c41404907610700d4180e002c00c641503424a030900500c041680540d940c001d56203003015000c01c090310100121a01809680040c26502035596083c1c809440460210115030345603450300004010031082601907003041d00c10a0214400171010001540a50443c45c0d20040017402d64901584175242c240d0103035404036140004941181d60308901c5000b001100b4050141c2e504100501d604101079140d03610030300b035070210030f0007460500801168420811400310003181000d0f9130242d42080c94040d140f143d20702480f88141c1a400c62512810741700403c0b00e2150780342d0100c06061000a8003840040400075249030741020b2490034210064407003859050007003d1061910b0358582c16410742600344941086001c2d08240b1803030520601080e40d800760303548550050343c038a65030b498a2900351411710421849108090020405560f00c00b040e610101d0280d90450007400800080603 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 303424766 1250 303423516 303423529
    0x106030509150103120c080d0b03060705130513231017150901020415020f060105010c08072405010803090f010e06040315090206031303021203040c090b010e1f0e 71
    0x6800c42c1d40300141400420100c1c04601810038a02024100788030400015107441ca16a80402c40b010912074484510711031600702000b00c29404001880c0c0941405081d0312082c1e1004954450280f040325840f041101d5906160b00c01146e030404101c090413110602004904141c004036400c0154001c21640000c078100907060140303024102d48060082e14403801d81045000d000036102003503c0d0350078400411030341042c052004689981d50000c0880156200440f8a0014160004c1c0d04000481c980400003400c00700c107035550719510016442c120320310014041c0311002030b001c0c01b1041600f06000051849008002001c203180d0030b84800e684969018015074a000340c12401070340000e010802000440c0d0342c80205400c4080440e00031036051700c103800044641c1c0054505c0701054040c203000004041d0100100e14029800c800c1b003a0451405840c1c0503491002842050202501d40c1c5032056241e10840840640726002080030003048a140c44684545907007030340c20404903036080c44808803413501c1d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 303426016 1250 303424766 303424783
    0x7090f09091703070c02040c03060e18060f3115060806060f0303041214060702010603020d02040c03140403030c111209011b0f0809131b140d11030106030509 69
    0x207031403601807042c2e40d01c0c180299440102072204002c4c60361005401640d41c0c4c00740119201c865036000c0340603800d100b41e221104101600843c1065414000321043d03c03008a5040c2c0c0c410411400019299204c5d0000748130311071400c100c06000c0d802910444030300300c158202d00b405140034034000c0007a91124400c5400f2201c607401106115400070002401c58545581d81807586500542503d003095aa24010f103000401c0007012580a0a4800c1e0740b04112006c200041d030040482c4002e00c5641e1458020403403d1a00110203401582c503510100e10650103500004111082995510900e20b800d080040003004e94034043e00028a0725210504061800601000380000c091b0900d0f1501c1007900043da480d082c844e4034400c1102e1404426808204020029520f10f800346e070f0000d9a07a080ca0b03041100f102502c10041022614150380d106c4100004144560f0002c5141854009003440349001080790240c407242d618014204804100c0a20654001c0c6040700c0c0146c0f03040c421034440079038142d1900700c0c6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 303427266 1250 303426016 303426023
    0x1020a09050f03100e06011401140304030c080403082107030c05030a091110030b040f27080904020f0405040b060a02101a041a010806060c100e01021207090f0909 71
    0x15140c00e0220389003503841c07400d1101c0c009048031084840800141c00f521051000040b85400002c01045810f002c12441d107a00314013407900c00100e13024040c4141140c040580060b0402c0701002c0050208220342040b58051f40d00840035540780c4036290340341a200c4685a500d1306031001c03402c0201d000d1a01a01400d004150203840d0b003130443e500d08101e613008002d81d8000b030380c1d4481240380c1e150150b1100d0b109254402015680800c4440781746007440140ca140c3c0e500d1820309841d0862000d00c00d01b0407014001c41d1945111008914a014203180c03207a4001c408182c0c2c0d01503c00204440c0f091550340090040f03590580307040c85030003030070420840d0034026503041e0800b41e00b02a56403201e400301a4003a1007a91300000c403901d030045003207000c101207480c00d030810000c1c005094401000d41d82c101c002d103a40078804032202071600300e0000f00251100c80d1380c04103400040e250024218180c00a4068801c0140c1c0041c04140d18505114020040000b034032912840c00041c03080421150b80c5d600600607002e40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 303428516 1250 303427266 303427277
    0x4050f0105070515070809061b09010e01020c0907030209030705030102040608060904030c05030d0f0e0a0507171207110907050a0c0210020a060e06010603060b0c0d032301080102031801020a 83
    0x8010040d0380c654403100d0b040301d99002d10002c0c04c041d020440b00c0c85000e040aa0f84512240c60158035840c0742c40d101821480d2000d5109074640300c5100d401080b0b803d034850070b282c04001c49800c140183d2416280c200302940c4418410204007000da410b03400703803920b178800310100c580b1940c0c3c56052500702e2240e405240009003a1b40700180103401c120074290b401074802e150540700b00c000340c2c03101030940e041109410040e1391540328604844025008000c19043c6c3c080c05000c500c44a6030b20f699417201548100c9944e6501001000d00010702403003250488400ca5105990300c120034503085030ba546455292920401d42600401c183c2441030b01074030324080d69070300c038103c2c036048c582c080008007030909903c18214403980c148200081c40c0343c018107d1001c0754400030074055046c18405401d40310310350441860b0890074070501030616800191808903405c0341c14001070003400540214854004042269850405d0f1b400000383e0301015802103209900040d0306040f0740c5e9010300c1541c285e2188050305030004d803 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 303429766 1250 303428516 303428539
    0x1c090b07050709111209011406180a05070e030a05010903110a030c110604090f05010806070c020102120f040314030a02010b0604050d02011202220e01050409030248040f020405 77
    0x148241c0c03044d0313100700700548000e0806140303e101c4024a903040316050410b94403440110000c0c60342940080e0800c008a078480440030401a0200400c81c0003807000c4040c6480d01c0228100500a070740501000c0d401500341c134101402170a00a000c1e228424044000601a40e420303101c1c42d0300460b0601040782d05036103000001516454600030003064a510f598858010800001e200c1c40c1c601c40c1d28100510488040f075a585000916420a8801807000d03080c0002604100010717a030101c0e0f1501000d9000349002d488015010324400540283c1d000189060440b143d2481007800000117002c0c800080d41c000e00012045109028160055200369034000080c0064200158001c1101d16124004244010300b00003030542e80441c15160360390002c104000c000010321400c0c00100070036015040c15a0244842d103e2540d0081d514007405800501c2015001c0d81c800019908903208824240d40d000c4900004094450310b02070040c12030f01c12480b07145001d4425120050500070389007120001021a00c200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 303431016 1250 303429766 303429779
    0x305090a0f0606090203010611060105090106020a0f06180b15010c0f120c08041e141f090f090e010b12030a0f030e0724020c0d030f030e1c090b070507 66
    0x200c81c651011505207488a0004c1181941440a180248801c0d0703a180c041d050620251340c01c090041e0480c0340600d01ca6801403048540018003040065071240b43c60f004816141070820003490300c0400300c2e11003410070001c082848115140d42c0c0c000c480c154003042c000d5003000015511000040f100074003000607842080081544060701100c10000c0c0d0400b8101580300e5a9101e049610507004032580901524a080355080c0c0b03405104041c10050410019144034600040c015401c040001c141d41c11401c40241c0003a03102c2c1c00d0440081c00501c81e0080a1a1141c1c5940040d114184041440390310b0604500040d00e03048581d440b4000b0084055841c000390840100ca110f041d0410301024140c5580c01807410380c008000b1540280f4401d54450920500010201c86030034001c8101c00071940001323581d030304598032040e0780c0b10710725818101100407500031703c400c3d40a40381c443c0b00da0415001e14070100210f52128200c60820214582d6842038903a182d081034081405208030241075680104c0d801d00c902c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 303432266 1250 303431016 303431033
    0x15030405011407110709111b0a050f2b17090c03031204030201151406070609080a090626010e0a0204030f03020a0c0b04050d350403120305090a 63
    0x900500010492182c5607020320358924040d0342900003e11840d82290b0804424020351000d0308400d0b80600c280c06032440000f1807805109104000d0300110b080b06010000308110300c8480592003020b0741e08541400c82e1031600c822100c001041442e070151a036690030101c070000210714400701d841f900300507010340405454611000b44515280c0c841d80740701c4003070340d64200068190000d0110f2845903901d80361600900350745102c10200c96109a5590a11514407003921040901c203017551000d131188a1814201e001d0801414003800300c01c000102203400030fa2100b41c20080c0c500c0b5441d500b0540200c01041640b11000300c00c1c011040d020003005016107c8440034050700110400009030510f5126100c1d040346001011044000d42c0c01800404200019a90301c0c00c02440002001810685132001003020012400c8004009000f600b19000b01e04410311303500b500c0c07140a411030020300c140101703a071460f66010303000c01d6070801c00510341c0344070145c4640104d0f03125050150103015220510f03a1000c08 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 303433516 1250 303432266 303432271
    0x8070b0304061b0f121d06041b030f06110f03010305060907080d0c03031d070f0f050307061727030406120b0307050105160803130213090c060e03120f071a061503 71
    0x25039445000342d0321b40036010a90b100104a0102c06090141010f10301006d0908129040181c51b0041080070004107640003110100642c11081c0402c7c1c60340c6010410015200e40d60808405000200c00802803104c0042e4141c852424602140d0107036407108402681c0c0c80780001d0703003000241000850070029106c0e80040a40c014201c080c040302403e451561402c0042580101c008500e003400c0070401700e0022001400145010b6010749612424444014800720200b496021a03d0108011075a071003440507000c1e10b0088080301c41190901241e20281e140d5001d4410840050300d58194082c50050510480640c00d10040c020f1480074500801511550010f00d0440c040141c55441ca03404103549000031071140b811100d402008032014070400c13005400c00701d0b60340c000c81d180c00190400500c2c400110380c2500d01c1800c10308201956040028645840b070103031400358180c0030803102501c030044809849258440c6503642484000d00c014803509000c225141ca0b481001c1d18002204441100000e54 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 303434766 1250 303433516 303433547
    0xd1707020409020409060209010815130c0c0c0f081204290c060718080a05100b0303090307080c04110f030a05150306070c0b0106030c0905120708070b0304061b0f 71
    0x1a20b040da50001070440b00740440c165003203034000406240a41c1d1003028581e200d1040310b0350120101010001c110fa4140c150092444265105220000680034640e0382120701d512030110600c40341c664a030903184015a1040d4840c83c840c07102ca620702107100303000f513506480100385000800b90758450f01078070a09032594814580d2a0810041c204c9040902212f84600182c1d2a080440038215102130020125503000d1a00c0d500030203c00e600250000c1840d4041c0f00e40450003180342980c3d500041c0c154417400311200e034544101140001c4844010800e4800058100c50403c00501c0d1109030014522400c905106600c0041002400c500515408a44c01c11040448140200001000303c2d1402c141079449201040e44e12640c1001c00407124411405003244c0d01c0e0a100b001c27035800340508400124001c05116034064140d40309014803c01c6000b0050004404035a00c40d0354640b64603860303034001c0d5070540f001410301145403c00d94200c1c40301090a05943d42c0c0c0d44074400d01202c210340c07101e03c002501 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 303436016 1250 303434766 303434771
    0x2150a090c081c0e0d0303050c041203170a0605010f03180c0801051b1e0c150f0703060b0f040b03060d081902010b040501050a05240a0c030e0d17070204 67
    0x402182020351001c002d410914000d21112225505036091990203200e10001c20440150300000d0ba298900d1940c00150705083c007140a85070501140024003c5800015540d0820301140301815800102c152141c44484520441501d030740107440c064804501409006c40c00e4501d0078031100c1e00c80d90104c1400c0c11446d00001c1c0d0003107590b6406405d401e0329804819269121010300008603444d5074601007000d031046100303242100740701707a00303400002401c91006400004110b0070086038081c849480150b8040082c2e515500e40080e83d41c2c081c2000f610184002032510301c000c600c01f101d410440b40062812581d10b0f040a01c0c268110b1085c3c0d02c01030900d46c02520700707207030a0005102c0d140038261001c0c54a01c402400f0340305a100908442c80103548600c524103200040003103464400011040c1c0f5030546808182501c11503140f8801d00091034a11000400014981b41c602d0781302100d030050b94880da88898045c1c07a92400c10808800401018042c2c40900d51400042e07c0000d008200651024001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 303437266 1250 303436016 303436031
    0x120d090b0a03021309060305060f16050904020f071a07050403030909050601030b12010209130603080a051617030a11190e030a0218010305160303140d06180c030506030a0302150a 78
    0x103003080115681c03045d034486803070b14030a004208090001e550310003120300301d2103031510b08120003504000f4107003615414850700103002031054031250125102c84001003039032680c0350354605d020151a41c0c184d038950490780c0098082240c0d940b00d40c0449048035090340d00e50f440b260410000c20010400580020705044d5200507070089915102e4641035400340300000141c03507000c01014005501424420070307003101d19040c030a0000a83c002c050741c104606910300180c441c07400d8803d00030450810741015004ca5400c0c40c5189082c5807140045100d01000c4c14140080c40c035001d031f6041d4a00075001050030004c1105c61110426101d1040400041030007011038040032245d401191560a000a003412188100701c010300c20b05c041009007103840584089041845890354070003c2c0b0b030881040c603114517240f00086d19010510710b82c01150180100d0b042100310703c13008940100040c060301200d100400e040c040050020b14000c91074114a0380c140d0040c00e10070194176010b0311403840080c414aa05941c8504 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 303438516 1250 303437266 303437287
    0x11032509081615030204180506010504050603010308071a0921041a03090d080601170a0209041a121903230408070905010927050114090c120d090b0a0302 67
    0x2082c08007149071151003203903818140019449030529480000703050041100304200c10400e00b007003956542c8a1000506502c40c1e8004841e5489642c0c001035000c2c10110002c000d03ca03056004100092040008400f2901400000d40c41c0640458010103070b9006200c81c451041e00c0e000d1140e0181d0603080c019841c1a440c0c030300442460010344450140a003001c000c01c11519010030a00c1c034042c41c54200450700c2d00c0e041d800201000c241c0e60b8010b2480f448980410f9001c0000d8050f03c0002800800c04e1110b14a2000441c22800007121042d02c80c40d408000030030202c00102c1e1100410810490010395840c9649043d6031140031036084020702014074010410a2401c1000303032000e42849400b41040a2400d142d000581da8180c2040c982545400015445051014800e4a10750f481c9420311441c00300904019004045144001c00a01c9a032010031001b12800702d012100d14100300c401c0041440d050703441907510741e015401c0c0000b00e54000800c0c820003075070700044d003081c0715503290141c07401d411a078 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 303439766 1250 303438516 303438523
    0xa0b1f1a1c1506020f070806010513140f04030e10020c04020703020313030305070c0f0602070302040c0e09072601030b1305191b08061005131508060108011103250908 73
    0x15a88040390b0319520103000d181d40c180250307800700a4040083c0419400e1583c5036468813410b10420b4881c40915184035002c201582006545001170b021941c600c0c6020002558a0001140c00302e000840d00f9003540c05602c0c00c41c0b001c000603a5107078000d05c00c100700c0301e00344402580184c10039001c2d4441070190015028600100101952095407416100c8030700c1d00d8030070b043c2c00da40d1300900b00c07541c0d0101c41882002d500280d0b400444c2e40494000c110b400d60b015055a03801c840d611242e4103c03040030304203c13240350000149c40e08186100c00c002241100c0c01c5411040c02801c1c00000c0c4003200000100300480184000042c00307074012020f803440e11018040f486e201c81d0034001c04960740d004d440d40384a003003060400000001c1c0340c0390300900124500040e0781030411903140181407148020400103050045541d000c6686a440310000349105500c410980b0f64440d000d200b2840703d982444e0012169003010401e680c005c1038007030203c21302d02100440c070600030801022480200b041c100400a6010802c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 303441016 1250 303439766 303439781
    0x2030304091b05180108070c2109050a1811090d050d020c0109051c1112100b032107030203070213020904060b03010b180d050a0b1f1a1c 60
    0x8000000300b000003000320b03146000e040400a42030003414040d5146004142d464603100e24402d1a05d02420f40c1c0d80001641d1100110780301a000c1c1c010342496454050a0209500c114551501c0742c5070800c1d80c0ea010000500030500030704e00007029404115081c22001d811494940140c59030403401c01110101044203e80020b009403503c3e84441c0c020600f15805104400203240e081c60502442414900400c010500c3e881180400754124070b80d101c14409080c416058081c0001c00c031017039030f05922525590321460842d5280c80d103807030050780d1683d602e80004c801c0c60b0003842c1510b020011440002142d096040300d02c042e03040d0b01080111b41d00590b1400030585481003000e030010b80718142d130802d000031240f6175000004000c00030001802080d03040800d442e2544840d403c601108220600030411030a1003490061180c0701e0040414100400c0960725440742c80411001c14400512810070300b0144114420507054100802104c0d80313241c4a00002e00c086491451b0798020f02c0d01c48020a401ca0b45917 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 303442266 1250 303441016 303441029
    0xb090f0f070915150f0e0409030801053c0108090309090c0d0e070321020105060609040902010c0c0e0403080c090a1701021c0b0f040b0f040513200112021e031302030304 74
    0x6030300c000726001b03800c0b441c03407071030070f03100355000c0068070b03100d41c0d014201400c103004003441a003000c0c1005045c411000020100e60950340e4a0282c5004049411803494000506207070109039900d002034000d03640001074070b06001004003c0c0019495010704200344e80d003c0c1000b04961910340308040c11a04081001034000c40c420710b1802440c00c2007a540b00c0c141071303030f0107054411641000c0521965a03038000c1500d840100840340010081c4907440140c03480c00810100918a000c0c40310002411103001e00420712a900a40f00c3d05060390303c500548459201d44544640d20420503023043c081c100380c400700360f807001010344001071400301008001c24000010f03030801c0360081e41b0755180352045e05044e074002221030801d540a005a8414000080101e8000300803140101c2d542e000240501c800e18410100c600c1e0040d407800e04c01c01010101d45902110766883c0c5010400500504900400130300c01c841201e20a801d403130300c07240040300c0851038a502c05060f09880060161844015035020710041005218 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 303443516 1250 303442266 303442277
    0x30b070503180607120e01150e06010f0207120b07120f150909030c0204052703091009050904060b0307053a050601060c02040f0501030b090f0f07091515 67
    0x2c00211031a480414203911020a4200d2418400f01030b402004840440720b0703848000c80c0c1844404a00c0e401881d400d821146200c03202c240000302188903a292034040e40080c0e99488114401040070b9035521414031500240b45410492980401d251080044e0002d0007490902039400c42c555241068400700e8203950641959400d0043d0000b100440090013000115018041c4681d6610082e246005030300019001c0c5072a0341c0007884180f042c1400002c8482c80c004907480b44a2900d40c0143c3c2c4c2e4006002d040d00a01600b40120f0503180030701c420004031800101045200c4d40c03140da4a00c060202c40c2c0100303400d40319619010175a50340c1d800c4804c0603000016540180011001000c401c6110032854544a0721001d04040001c1080802d00d2070545845003480301080300d0a1000c0342c000c01a03d164040640d140400120030401901c1c07a2a0040c08540c04441030103600804898607200b80c0201400a94041d51040002d00200d81140c0fa8070249282a0034989585026411341010010b525500240 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 303444766 1250 303443516 303443521
    0x60f1b0510061a04090f06080d090f0b070b0402060c121606050f07140708040b04121103060f0105010f120603030503180a080f0313050a05060603190506010608060109030b070503 78
    0x581d1881004002c00c141c840d000c0141400800c007410780d100e2401000300040d244d07807407580300001c1034010000601c5050112481014560402000840c040c040c40c014040d01000000c1c0001c6020252648aa000009103585446542c20481c469010100b0019140142c1c0da480440d04696405403410b005040e020908402c582d180c0f0f0002c541c3e00420303041b0313007070701c8802401085980b00c00789243c7c551380590310b0703a9628100e061034030940c011a0b1206500d180c0000b00800e43c85010242d03407034131a00c5103074070003211440303041091388811013107a040711341c2c1c443e0400400040d840303140580340601907030602d000f20344c030041c0075803098421a070000e4005c65400400e00130020103e000542503891401d024200150705c0f5915950688594102e1707e40700c82c00440400c0245941040031103000d03500c002281e00320401883c003291541c0040b00c14520a0003200260fa03602c8865489405586a125001d00466800d240081c3c0301c604000e07003460304001da91200880040c1c01d00c09560701808094072240d4030791 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 303446016 1250 303444766 303444793
    0xf1008060403092d0b132102062b0b10022e06080a110108060a080d121d0a1e08160f020604061809060608060103090204020c030a030b040b19060f1b05 66
    0xc569a0b002c10f0700808070400c03028181a0420b058040c0c194100c541c1d8ad0713580004480c0101d03601881d1850150300703030704800c0c0642503102c1d0b5000c81d6030303030300203580e44540020802d00681e1600070510419404059000c1a42403c105411030384030403400c040700015255482d011501d14207018a0401c5501c80800301508540b90380054180740e10800c2121840072030780c28240c0144e220000d003000803003400555800c1054103c101e40208100365075518107840e003c040e544d1640c0d901c2800110564101e58a172540506003105c20920486084c1c101809619100c13074034803040480b04500605031944220101144016962003004100030010ba030760f04401884221646088960243c0c4040d800714500002003110b45d4001d0905644060700b400e000840c030f6a140003050191080c1b0b0700d03110860100099058205030164010074802e00180e40800c400e20f048402e020801400b0040c040d0b0f404c1590004000c02441680400d8010b40d0515140301140130b03143c1034118002d2035200850b1550480e10800d900d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 303447266 1250 303446016 303446047
    0x20d050402041407200a0209090d0e010306050a12080714030a1d0a05040507110f0f0609010e0a12050c01051503010b0409030f0c0c08060f1008060403092d0b 69
    0x443d08040404803007802e1800b005010074101c0c03544099410101c00302040d001c071051103080c10554014043d0360036490f11303003e0a6150120040401c01003000302c3e51002d083d5209126003800e4440203080b98840b5030501158000500099004980e0a00300300304800000c2c610a0920211480d41c1000b51307200c0410950247c43c118160b0001040407440c50904c00e0507540d2007040030f040360010394001070148c035032803021140310245010101d040e00c200f1680f03000d051030000c3d18640185403802541d100f03071a10400d0398265040d154080300d940d44451707010004601d141e54030b03081c1c5a941d810242d00d800c0089140c41c0c02d450044594108800700e48210aa490400380a0107440301011242004030041980c1d01403d14040080e0040400c21009070f10010410040305c110302400c0d405003129643c0c0383c042d180b408070f820201c07a00418440d4600300051027200015040e03004541c1502e41020780c4d07003064509030011300800c8a01800b46044900042c000c4a84d01072031b0701a00c1d88842c819591050144800c0c40e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 303448516 1250 303447266 303447281
    0x20c03070302011d120d0e0309030f160f12121b050d0801060315180b04050406150803070317060a240809030403021f0201090b0906010e0c03010506030a0b04060801020d05040204 78
    0x443c1c00017400c50403900088400c8482049001e6400101100c003617204900e503001c3e0710005038141c416051100b000200c00203680054103025118404183e03100c1200c072030030340c0440c80744280300002200004c00151000c40c02d03100b11440c51618100303408103c00c103000c01410300c83d13050f109504020b071020060f40c0c0c4008801d007d450181000d06c61056490001c1e1594042c2c1c0c4200300c502c5a03c09503501c881c4002d03410061a004004005120741d0a26050010042104021100740d51241000c00141e42c1c00c08025541a10b802d0340314030f000d00c61315415910020380c0082015500814081c0c000c00d94060300c840e0361206a42d88030145012841c081406002c8810161106001e5882400200016038420841814008000c5941c011241c1303000000c1e8003402c0483c400034800d102010410503041c01c00210745040343c0c41d1904103056629420311050851000380111074220800300001210030003241c000c1c809220020b130001038001c2c0d682c210542281c0251400c19078694035030081c48150700e410301071000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 303449766 1250 303448516 303448571
    0x240901060504090c0e0d030c0227091015090c09120506060406081b131d150a0902012f100b0f03060f18010b0a0b0307030e06091e01020c0307030201 65
    0x460a00340440041d0746c1c6a0001001030401003032503004411900c0300c0c802240100a03e035149006a000301c04030100b46102242c040c0d28074070039100703613044c1d2001034000d00c1030b014446000501c0f01810300790803030b002e003512958040c107020902c1170014002031660032440c001d6000d200a001b1034241103007040242c1d451031348141c0e01544041d6160869010740064a1400e20f0708403904010040e038119054003802c80c40074541c1100b001c100b00407000702d5000c245a0b000c1d110080344401240c5c1d07610070b81e0007194200034010380011883c0041c07200b6140c0d8040140241854112102c000355015021180380071141c40248803103a8480900b69000e0a190444004140046000e040d061500080c2d90032660b000610b8071b201c1c248041f00c003924050007035202c00442c8001a2048000a0310358808011540c400c0d10780c440040e20307001d010744c440840861141d02075034035080584030951818030f60032120b1500e031315242d189550802140b490a20700b040184012482900041013800c0c080052085180c0740e40d01c3c40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 303451016 1250 303449766 303449777
    0x3703050105100b0f1b070303091a0f03012303011d10020c0c0402070c03060207030806090a0e060a0b0109171509070806070f030b030312090c100503240901060504090c 73
    0x80c00740743d28501c181c6054084403000c0a40f284c100d42d040c03004140d4401e016000d00e000f91040403082c95401548001580c80d041c030711100d82007a1802401080c0314082c8480240030043c4014481321102c48041c100d119103015074503030003000200000e801c4070004c14075a148043d010490941c6a4001e01c10b009020004030011402e103070061a42507100c0d1550450075201d558000380107810814000c90030b001840c0c20207030031074480c01c0600e005031a508064a83d648203a140200048140070107000300340c01102d0200281010351a000588809004000380c46418010741c040085403d003094410000200380110003001c06540e04c4000103c5801d0160000f01d9075045908103004030140000c02c19004802803800c45c40000810400710000d200d066602c9074180000112220920074251801380030b100c1100c1600c4480d50203104010315100c801090078081000ac1c07002071145880d811107860000380c6c10f1240c1c071181b50041c0000b00c21311002d030080300115001150500020525100700c8140c2a030600f0700 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 303452266 1250 303451016 303451019
    0x20904230106110a0f0203030712030203010e010909050a11040f020d06030b06190b0904110a020d0f1b0201030209120a0b090105010501020d09170c030610050f031902370305010510 79
    0x199446032a0f80e0700103805c030040c5c00394020454904004030b03140c4c540c21046082501254281c014041e51003846446404076181001107810030444c45008102507110004001344c1410783e480c2c000d000211603810b41c1c0195036558114081485000a01c10071036200d00000d55142180382511640b100078104c070307014800c21107621560490701ca8030541039488242c80180c07600310131400100500311032800701016150202d07442403540d0700018038580907251a1640d20f10b0503d07034903084501d916110055405007074a1500c0c040036500950041c01403c002500602010551481b5a89009100001100c00369241e00030800026404c0c420035014041c242701030201800307000700042035050300d401000c2900012007010348111034200300101d01c020025094460901e024840080707081e6003881990702511039544002e1227454040f600c0d440300740b01c1da58401c1c03425170380760240084001c00c625a828442541300c000940640200c0800b092021010a2400003508515146080d103001800c400c0c0408601b000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 303453516 1250 303452266 303452297
    0x90225080322020d030e27061002070b041e090203040b0f0a090c06180602012703050708030f0a0f0506030c060307022803090f03080706090303020904230106 69
    0x12a0307000380b596240c10300401e6455103940084510702900075408044000d800003016000b0746644046075080311403185241e0000007c0400000216401c1e03034902003034001a0031454803581c03c0d20201030910454003041d844494400030350740b0641090703031031880039800d003000c0b13445c01320101c0c1c064010414158118241540c0d1641e20000103810000a400604000707005000c02e50300c6056140d8000400b803c441c0e681c0c0c0000b4100740480c00c820300700401d04100c0410200d00500503400c00129141340071262511383c80390450008982481242000070400c0308038085528240558029034080901c004c40307007440c41c0101e044035180380102042500341030030031800303541c04101019050030580b0300359a41da0b14040202d0603c440640000000304140c0010902050003070324189540e0711030340310755421540302c10f2910340d20b0f2058407000300040d004006500025845405c40005907110b07040150803c8009800a010382c0c03119420850460341c407100d220000300000d900c090041100c1c1c10095068a80100c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 303454766 1250 303453516 303453533
    0xc06010306020f090315181911010513090509010617062809060902091e1b09101806031e05191103040308090d0804060b0f030106090225 60
    0x84090986070b80407400300000b68a05040301c50702e0000406484002e1444101500140415554400fa05204619195900400103421841e41d00c525500000018a0340c4d40c0c0009042640b001e41e04005060048071a60403504010002400b2181404111882d203980a6801c4403e01c2c0c2c00000500040050240f6000002c83d000341c001290b80c10310300c000594800c07a0842c40800e60300c1c2500702c5203007400031400e120440d40810b6580d8030865020946444900c242c424855001c5003001d0307442c007800301240a84001c222001d040004009a003420300c400740c0002801c41200841c000082244d0441e8028256110046e21003e4040d5080800414600400361044907041030418080c10b580d03500424281000074034450548185450280070b000c10a1246441c543c0041e101100412036440105a00d20400b0aa41c0800113250352440050703039a60300c64102030070140784982e40104000400c070029480c00c2c001e240241100e00809a0346009100b8108002e01020070803d02040518860500082591 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 303456016 1250 303454766 303454769
    0x110409110f0a15031d0102031510031b080118060f0b0702030a020604030f0c0b0a02060a0203183c0a020d0201090b131404090c0303030c0908060408030612030c0601 72
    0x5072400300c100110038020458140c141d802c1140e41d41c18190300d07075034000c0c4c4c15004081c00f8000741c0c440400082d201c0c600c0500340c1c007056944141724075040014000320304000d00c3e850440d042910300807a5000c45501d1240c4405d08200c186d0f0005003101c0014001c0c600200031101d1000803d40c3c080140702d15201450841407968001d80700d0890000515400755a170821481c000260010440c594482e60b918144400d040e5845084844a0301c1d40000503102c603441003520884500c50700a020f560713503600c00d200d000754001000e0030120915041d100880000030042102c82d40302440c2c0e041103070180141d00061740c03910001002c24689100320342040c08000030401d206181da041d5041e0721600601d10040c1c0304a40e0382c3d004441c3c802c4010444040030b1461121100071500e4006030004403900c1002480181c60b030b4510098001240000c04000113840385e0b0050f04007140900c0d0040d01c05840f01c0a0a052100607202543d0305203000c010f03ca460716161003060045c00300d410045103007001c081d01340c54450405 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 303457266 1250 303456016 303456019
    0x8011a10080402061c0e070305070b0307050301050d0215031905011401210e0a08070227060d23060405070e060310050903040b0a08090d080603030d0e03090414010311040911 76
    0x4908007070003001903501c020010900080c284519456500c04c41e030381f00c8480c40306840f11312400f000051070030039800481e400b8141c10f560355440c2d60300f0182072009500b01448202c2c0c1126882001d180c0403070000001e0b5000c0d1a0442c81c0440300180a10b07400140c80040c0c10484580301c4244804102e82e802c00e03501400d02c16880c51070000440748110300c02c010607901c80307203d0003070080c0000d85007000175036002000918800c6441c000b51991310820442c9003c1107048941004075444040f8179540303042c0080c1200300e8410604104001c4016858030010380203844091605e5209a0500c07082090511110b40901815200803c04e0302c0c0c9140081d0b5200b04032040800e407241e803480415160f260505c00c40b0003070502e150380d4607079845e00004024200102111842081d000b072101101070588070f40c54250207a00c00500540c14021215003200c02060004500c62540c482041454210b49950281103d03503445030610620962440c10459030400714024480d224034544240c941c0042d00d44546403031041b60 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 303458516 1250 303457266 303457279
    0x5030d110c04060303080915061c050f0712050f010209061c061a03041101140406031a130b031507050706182102070f050312031f08011a10080402 64
    0x200c000c1900e0400605086480c1c1060502ca4003006054202d07440c05e00034070814040300c2c424251061205403500007901c001c0e503c4403001080b402103a060303c05103c0c01c94095425110441e01d803604e02890515140c0c04090040701e80d64152050090034042c81401d141c8540c0290b103030420b0a00003528900c00c2e001380d841144641904564074406903805500500440c842110654880c0070240455400403a012200c8001081030f4181700e5110702c1c103c003601c00e9288606801e107802c0a500707038003400d4503e201c0da191520907601c8909036600d00c00b43d010055080c407000074860000205140c10020002c5181e2141180c040910080d103600c20100e0302031940003000041c00070301103c06441110b00e0064090728000d8040c1e50024a000582c16800622166800301c90041c0c3d82c84114440c041c06034402d15030315420048890703560110210045038469001c005e0744249a09040202c0300428198221705141e0f0b548210b001c1c94101042e140451f445403c035400d101001404000502054008100030300809 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 303459766 1250 303458516 303458537
    0x203130602030c040906090b090a090b0109020f09092508010303091a0405030604030e0a14030303160e06070305070203151909030212180a050402130e190c0302090406080705030d 78
    0x4802025134014100c116400c3c000c080d640d216007c040c102128100c2d03c21040704000c40c030000400c5c030843e03d059600c80380c1d844140e807901205038001d401c140c05003c1c80d01c5040150440175558689007512500344020f0304618a0900014001c0c881c0e40040b1042c1400402401440480d030040c0c200c00c12a10000c207106030303e56110000941600841e40840c0d0107201c0d401c01e01040540101c0d80c44603100007586c2c07003020159104441114240143c84546d01600100042004c0e040b05070074000d5280c810781442000320320f801c000b107400b6600c80c0000fa40090000300d0b241c02146014403801d9001c1640d5240d410035070600111482031000b00294a0030029540d4000c5010503000703001e444042481d00c030341640c4501074401da90503c20f510ba210382e4440e188507200030406103014400d40d00d03180c502d0340e00481c145040c0081c40540d50805408070141032140e0702601d001a501c1d0040482d201c4599030f016889220302c00a000c00c0d100c041d0062603841d00701203803d01450b00e0006925203404030134178200c14507d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 303461016 1250 303459766 303459781
    0xd090503060415090b0408190e06180f0909070e07080103080d020a0e15120a090c15140406050a02010b2b060f0c02010902120102071a0c1207021b04020313060203 71
    0x1032155190042090000c9002c100501c00301c100039103408146029800c010320300c04a42290300b4445104014ad100c0c00c240400c00100b194448100c805500246c110380000084400060380b9600884550321581c0c000201488005000c02c016a00103070941420001541595202d0b00d05000303191003040015401310f01030028521440400c10100f10240c200203491210140003401d590004111403a54a00d0300c01140c803407030b01c40c880c04807007542100e0350200031402c0402a48922840190b10310812044445075000300100000038402000a515416540d4009000280c00d4901403e0120300c11038031000c0104440d83c10185900d00f80c0c2b020b1240c4070801040d880c03d40c00418504101d491501d1602d078089013800c1d015405601101d000b102d01c804071a18541c2d001d402c0c0d11480c54010034156002e1141c00c0010013525005401500c40d20a0a0803ca00e520341d9412043c412a45400107900075203000007146001c3c1c0108000702025602540356142a4104500750801c5603001048543e00000041c0350 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 303462266 1250 303461016 303461021
    0x12020303071434050319020d02031002031e090a020102070303030c05070c0b03010518040c14040209130506100507050c0603040804050307181820030c10050c0d090503060415 76
    0x4900c102c020508003031001607880d609441040103103c400505a00100b014540021000c40303a11030440d82d801e44004950a202c3c0ca6081d815080b0b802d441a0802117250072224000396120307410b4903e8140c00c1e84100c0e00c4510146001415440030354100c2107491003d41d0b800b01d440f0090341c1e018240420b907240317805030072552031140c41c0d0003420b00c0341c0394003012520f444d00000a604807941182e19a4801d01103455410702402e00396001494250480c03420801c1049014800c2100c00c0b00900040c181040400803804448650300c0701410a030fa19020491145002e0a4620402d03480740740071820201280d0310165910000c110492044d03d01000240821080030304960107450081c0540f08074943e20b585441c100c011440f00707105418200141408800c2001039000c048503082941e07242c500622426609260200706078058160080784006002c2d9214203003c45403d0210740e88450380e5080786c05003c1d089c4404403e2400400401005c10010380e6400641a5005074116034403411090301890368800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 303463516 1250 303462266 303462283
    0x100f030903021204030804030c1a12040f1a0a06060807020316020a0902120106030b010f050301050d020123040e0a150b0f0c070f05031005010602070612090206190207120203030714 79
    0x1000400091301100f0003080c4000340048a1240a4140c04607032501c0e06c040c040160400300103507420701403100e40008800c3c80318243d0024026154207101812988030600301c10030320900701c6044844102800105000340c41100000e05c0149480751040c03c250700c0c000e45030300c41ca5015817000401002c3c07100030b564400141400500c0e4ac0b510842d83c0340c424410301540c0138002d1007901e0110741f400c0c007441d04550044075400940e00c210740e50a444e50303090000b0080b007005035200130307410040c42c04241c0d070710082c02c02104060014a08404c6403200c1c80c241d048011113500600b0200c00d24144440d61502c903015151400903142912100c60b254000d00407900700501440e425100e2600c508203000900e209282030240c1520410b905440d40c055010380b901060359020300c106030040c3e21111081190601c98a440607140b4100c1c000458104581d8002440c00e4124150600c86110060064008107070100012801000100128100078990f900040d460b03000d00c03070025001d01e003d454804200364050001c4030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 303464766 1250 303463516 303463543
    0x30624040b060d0b0a060912030327030302090a170a0b070519030506100c03170a180614010f0b040303050d0608010c12050901180611070203060114040b100f03090302 73
    0xa841e00343e4107500b14060b02c04100c0c50b81c00340c036038a00d022400620410f1a042950b034071078440700316249507980440003400031141c0094a030308200a41401e5001c1041c0e41d0010f58000e68025884000c50820003000c00895480100d10717010301c2a1220002c88085080142c00f600039558481c980e88062060320117208004162000e06070a00c0c1da4005c65825034441c80c018002a1102140d042c1c50310010f880d103c9010308080c0c046040c14401c440c0801444000300d9014a5190000c01d1301c41c5082186105c0300c010300300466929440d203403170032460428040a207004000c88030803006036034a418032480b558400e070b0001404000d00000d0400000078982c21400050140780000c000c400031200300144542c01400300d06140c2424070010800022050003040b4591401c8203c9046459499032004014180701b00f031544020003e00c408001345c0d0f0709001e010b00901c01080c1c01d10618100c0c50070401151009814184035070191480c441a10390300c1620188020f0190800040b610f40710304041e0720702504102c894 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 303466016 1250 303464766 303464779
    0xb040306090309050402070b04111909020903060703150303030504080405060d0c110f151e010612061a03010302010503100b0a020c01021e0c0d0804050a03030309030806030624040b 79
    0x812669511044030765000c3d42d5034a400c5502d4004000030b0b403151002c00b4003c0340c0d901f0003260110300c61031206001000000c128581208021007180d2075440b80341e000341d0107a94049051001401c1c144151a441005860100803051084d078005811403000e00014041680d280d0000341080681c804803005404000e01e02c0e52115075414115001d001403e04040000b15400c2025031038101c0010340086090b5080007402d80540d90603514405524014054030307903081e02410346012a625503a10a000c2c104a50721554102c906080079015140355038005a000181510440c4414101c0800d0b070741920790902c1c01a030341c0e1310342d40700788da124403469005140030900c0055000b03445038002900040032030086e0280d0700907580760700ea0155214001c1c02040425000602e0716005883c108038000c080e2440f1302c110340e0415403170b600401c4440e0807a07003084010a5469060301c05141d04220180d41c4608124018030152800d0312500321a44091007089200c4407150203581c010365515008441e04640140c401c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 303467266 1250 303466016 303466019
    0xf0708030a3906050106030b010801050a061211070308090d08090607030209061e04050a08030f1603020717160e06010909180807211403072030270105040b04 69
    0x1103c0204002e00c00d02c2c2c04607107001049003540d405806124100c541c000d106511682c5804c3e07081c0c54645004022411042d90b075083e402c059040840074015203402a84c0d20b0041d0316000c3e00a034070b044580400304090014000401044000c00101d01d1f600211500d0096164003904010405074002c807102e8100e56420f204003e58515202c4000c0c03c1200e0302122a0101d540c1d0752075a00752a84105010050103d4040000ea50000214a99041041c0c420320448043e00d82c0c481c64800308060400300300241c0d4100c03580d4440b00206658940c40503028452000e440d6007045000680703849910f00c1020086a100c0030390390003449401c030509104642000209a0b170b100035182440c030a6101e040c2014554044100160f107151091031a2800c0e0100380c0140c918540f0b898005071010019203c035900461494080d5203900c0b6000c1c441c044003210100c4203000d84890789203540030300440d40e41d1007046400c401d0042d55103000c0f0524035880041c01c91203001c0f2880511400495031445242c009060b42c0000240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 303468516 1250 303467266 303467273
    0xc05030a181710050a150b031302120732131508030306100801030b1b0405040905031c11090909030f070c081c080f0601200f0708030a39 60
    0x1000f58101d410440100f0041d50362442c07120444a00300940c043c6c003c41c1c0c250602c09001c0f5a001580c00812095901000e1b0446500040303a4080150550030a0740100d1001c1040301c0c09008500003c00e0b1a11075020541e4119400045403210000114411018074840c1c440805240d0700000c0c0c1c404950a51504071516807078415625401a1400c5008002044d255890188200c040d981660f80c03004c2c464082d074a4240c0144880030520707030040d001010400c4005216070319071240ea00a24401c038055074807100d1f0038034490300c181040c0c507070a0205814114038078009600700d01110fa58410445800f0b0181e15804681461030007061100d1034a9840058990288010121044200d0300d9000803202c03c201c540c070344028202e00c1d20b041c4c400440d0f031250205440652442c00581d105406260070728004c00c52503101e5421201565003015560043e01d8000c002810500000f000740010704011841d1400021000b06003c4204c500e00080c8200341c000028000c030f0190310b0041d68502c5035500f80700c10a4505 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 303469766 1250 303468516 303468523
    0x50106020109140105010621240e0603120d091103070311030607020c010504060c0303140403030506100c02090606160f1209080c0f040e0102090a0b0403060605010c05030a1817 77
    0x8400b9121001442c074032410700c1105005d180d0507212280c4c4c83c3c03c0c1400c0d51816001540c40030031a40034040b03450b9440c020709030680c04c0b000152048040051804c4034941a42000010000b4003000e029402440c1c14a101081c1001200c440204c0c40900140c024603a01306141608419400c8584c1800b8014002090004401d591203c2d80c0c0100c0640d8096100c1d00c0c3c3c01e0f607407012840c8025000c0754040c04200103140c0152006000c1902030304000c03d0045404078110a100811102100401d56a40c20f0000d142400401010601254106004440c000d500003a03030242c40101040d201c0c2d503002902001031044940b9013000c15501c01046a426a0f16150807001c840b0400c403101d00003645000c00103100030000650b000018006090400040705640030302c030117130610004c840310542d000c21002e01c81e1b444030584000104039901e0030940307070790462901406072000782d405281080742400d00640800d030080110b9110700c80a080c00100c151400940c640d555031181d010f50850082c41e40c404c1002d20010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 303471016 1250 303469766 303469781
    0x5061c020d0203070201110c120f0d0513050f0304060806040e0a080406020c01030c26090708071409010905010b030a09230f211b10020c0a0b130812190501060201 71
    0x40e0001d00c030001c1114040d44041c0100c14510000758406071501295279003242c01458004840180b0a10389440385645100b903a07402c5d20070b4003810f1100d1a0072010f001c8140140480301402a01039854245070010091010307001424091040d952600741b50382d0500204080042c00754004c80c41500e865640c2c2010303484150b000c1e03840307012904240c5084945446006005140504182da2080082088520090b10b5100402c00c9611f071140c08400b02d459102040000c00400120711342c03501211000d0140104c212041e8010121a81050010f02c10310072024245c036405000c081001402d071071a4241005064051994402041000041032010741000302d10303018998140710803120f0040030004900350050032803092089000c8140b1a1312000c480070f400b20000410b1a201301d81c0041c1c09240d91a003282d0047c0c42e40071140d400442c00c4001c110524a0a41e409080440700000e09907085d101c00d080340c441c000103d0005544400041c0e483c01544158080241d0101c0301040b0f03640c0c48500190003032001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 303472266 1250 303471016 303471031
    0x6030a050d120b0307060c12090504060b040306150608040f1104021206030f0f031803070e070807020f07031703130f063305010e0102120a0305070906030b0a05061c020d0203 76
    0x1e080c80f00c443ea0900050003001c1300c9031a5607488510900352541421920700001400400160140008030369031507014000107003008028081d41e491544ca0843e0031101e0007080b4200034a1184010811f05800001c0381d076105404c0490084454010314110612100f030102841d80b091000c100101e0006480000c80d00c0b4840a03021543d40c03500c0440000d6659404d508407600e164010410b0010041024500c8906144041c0c11a40496160b200300d01c2014030440d80f00c000907507044200b040d511781c1049403800e2100400081c1c400c0781d05540340e00901406281d200c2500000000104503a2440c542049112940081111100310410310303125010f005800d210001c01140e2204154000782103000e4041484901e040760503c59140c200151413060003440da16055000701010005059400d9005001403425507900080034a401803015154201c20782101081525005400d0160b446151a4100b44e46040724035680380c1064240900b030590b200b611211540340042780c2d40d02d064800b5009980540301c0e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 303473516 1250 303472266 303472271
    0x4060e0c030606010e0a1a0c0105010e0c03040f0c0e040501060e06060a0c020d0204060503061503211b0c0a06030f0b0609181b0a020a020910150806030a050d12 70
    0x4441249940d106038260140d8150070040214420b503024100e00000703040003802174100250b488000c00394400300d502c0c401048090000b06096100400e101300d90241401c9100e980b80b9090115031707003296000003400101039840b242c80c40002d2003000c6007210010103136885100500e01c1d04d480d009000c0c000c81d00c00c803c081d083c5500131800a1400c942038920b00000e540c0c42829145441e003c00138044080141660400d40e45c1d4030115140e10b060000a1240e4402d422010f032200d0f0110034140b500ca84403d0004002114030440c2c0c0007441103c080380d80c0d144012402c24030000c240450182044105d24013164860f00c500da0026200d03401d5001104a84440710081011000d044148080c41c030503440640d9204400010000d0700441d03039148182c000101c140b001e44450b818003c0c085080d4444422000564040e201c41c5e02189020700695a020b2118080c1d1240c00340b409100ca5514032a1490400038041300400040051310304022031b00b0325942040c1290b59000340f050026000d9101e152807554080d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 303474766 1250 303473516 303473531
    0x16031103150c160f02060a08150a0302010806100e031e3003100b030f040506060f010f0c110303030a0c090b0a08060103020f2119060e010e04030203120a050406 70
    0x44485801d540329500c001c90440c5010b04010034019103000d04101200d40c02840041240581c41c3c00020305066a0140c886460700d003005126044100c80070007816129680b200c90a00050368000c541581112003039422104c240e614142c151626506a0195a0035205075120f180380341c0070080c90070050f600c409040d03561480d10795803102164900c8010210000c0264011150700c183e803000110344c0048407402e0300c01090740340e5507520b41c294000d076480c08400407410180400e000c4148083c60700700200720f60b441400ba044070000303804c000c60b0383c42c2001031240c0c15401805220980f01c143e085924024252a40c034600039164200a165161040b000a40001e20100f603000082d012191f0900494550038601d65840004601030f52058656240681051165440000d070041c0c0650601e105001c1c00c100c189060600c5001c04d95140b02c10307511090415104000400c1c41811407419111496101c4609545074101a4603611581c3c48800c1201d940404021002c0c2140d4001806603200d01400d02040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 303476016 1250 303474766 303474793
    0x604090f03021e070f05010c0c09091a160e0418020310060303031808030a0510120b010812040308030604240303020105161d010315050612010e0a0203040b01030b06010216031103 78
    0x130110740c041d1100d01101d40e5810f1240d50b0160600a24180c0b040381240c244c00d840d020510b00307403100000200e4102c01038a00341c000b00f04140d0b14507540041410b40710003c156824800408400d101c00050f03010306e69501560030700b41007604079107615070f0300681245c1004030b85040748001002030744000d400003840c120b001050415420011400c0c6900300200740c2c110744680e01d40c0d0005210280c40c090340c00740707031100000e50308a02d0f8440e40060f50203a4049a813030741c03500e2030540c00d0518405d40080171309010802030001030711010541c0d030409419540050310303019a1130950003011098855440b40e000d011030000c20154150046803140384001c0170008086100c4405845810601d0708030440010760902e000d03001d5100c0e5100001268107100c43c3d00d0580e41e900d010031b0155006910755404000a03500503c000300b040c0c81d6864200003106801c610f545410340383d00e4401001070100920b440295030102e91f16a10030040380c0d0000310080070300d007501640e81ca080c00782016052055406405004600a002c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 303477266 1250 303476016 303476023
    0x19050c0c010804080a082a07030f051e1804061509090c1e1403150109170706080c13120308060a031e0c08030406050c07080616080604090f03021e 64
    0x83c6504c900054140780c0405025202010010010345508032180d500c50206d031000e005182c01a1840000d6560f41c2c5038504005000740340080c0b52400748042008007a41c5190190030004455100c040309c240c6a45500a04142903021080b00c01d074054184200802c10035011900301d003040895498445102c0d60700e085003029a2412624100840c03400b080c40300d401d52140c252482c0060051a02008003c20003948007419001036407102210381c40000c0040c070741c0d6003150744d20010b08200820307030111a002c003800f03e6641160f40a41c00400c951107000c143d0382c44902c025130700500d2940010600c81e070744828504065101014041d80041d000002156070740c14132845100a8a80008140003101d907100315101d04089034140c01c44e40c42c0320502e03000840c22028070140019026980c0c45544d513503804200107290501070382000c0361035003001c4240901c0040c040140306c0401d030305040c04070720742e43c070500001c00030230766241c01811980c0c16020000805502040c070288041c60b8043c16240c00c8074181d0b10303030364 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 303478516 1250 303477266 303477271
    0x2010e1006060c02090403030e120408010e06010b030705090a0305030c060a050c070b0109200325080c03011e08012409020408030304060b040e1609050106030b01051b0319050c0c0108 80
    0xb0900d810441401360a00c0703035038168003500908000c0f03034043d809012113140c0302c0310380c10070034640c1070104090040403001c1c000c940315203034940020722295040038030f5980316200280c840e00034044005250b400c0c0340c489800d10401103410000f941c0e200e106518100d61691812595620072070302d8180041c0d03007151010140e07000c05e60010a0034020360309000040000b807661001000891400d501000b161020b1000110311400100310084c0c2203112001c0d100c0c0b00f20180741d00b14424084001c0130880c4803061801a00d0464038083d1059900c40948806150401400d4000060a5080c0030407100d01502e004400c0101c0340c640840a00a50341d00c00340079041380158040c0c0d030303000c0e0420008140456000e8001030403000c00107000040348030b000107030103141c86011440004a003c01410070052078480b07206441c01000941420f1003000d05940000b09240f060a4100d1121850744035030409952080041d41c0c1000b51405141d5000940038401501036000000c0d018004c1c80303889610794031940704002160 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 303479766 1250 303478516 303478529
    0x207031e1a0c0409270314090a1412010c050d2c01021e0c0703060203060a080d0c05010e030301050a17100f0911041a060f0f0f03071e12110d0c02010e1006 68
    0x1585c0b240c0355500302c80d441d0010120031003090040c810441c40356100720b00f00005019a218150300150980d00748800d1451400c4241c003940d2500c4400380103642c1040441d07130000e810900008000c00352181000500700e00c01030b40b91641000c41d0100c80344072070550040c00900642001840668038100d00d00d5100d1280d2443d2101a410a80c01000003a190790099034000074001e090f403a10130345070281a80341c1a00400c2c0c0f0ba00081c400c2c0040024040700b031048005113018400614650740c140004249804081d115030128030b14103d40c0d0740316013039090104550640100c40c00348140d2401c0445800641988101922007040301a030200491a282c07140c1050703210b50004910340d0114850402420380c018401c0c01380340038000c0080b250400e08401c000c0194940d250011600c0c1c1c00d1842000740b4289001588030800d040b030864260405402c4011340c11903041944003c1285e00c0100d000e4a00390064840d03211142e0305142500c40815019000701e0034442d01c002c21118907040c52040581990424405c29 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 303481016 1250 303479766 303479831
    0x207060b1c0302100e030c0f03041a0f070b0402120d031e060f09020307140c0304181811060c1504020907081501030b010306030812010f05010207031e1a0c0409 70
    0x500ca1051745c11a6110980f99400c0d00e08000b00f00e90310f075092140e8016240302c00d400000c1d0038802c540e02581038240400301a071009051010314501002c3c5407103024070280c00031346440c00040840daa101c440714418280301d01900c4a2255841d800b402038405404107908101c0b9442c5110350080c16807041c03408031030841540e100c40d60316000f4204000c0d1f001404001c2004001c441c0050076002e214002d00d042a441002513555a16040241d07150224403410f1100c450b049c00402039902d003000452040c102e800c0000d030081001e900700080c0651148003149409806000d13075940700d6a0390000d1161007039000f41d5601c03240359140e000484401a04440c640050103030b003200e4a42e40d51196001104800c0181800900540c42ea2210030041c2c0041080442e400c1d0785030b0044c00f1200139012100d00034502800107181281c01d40d5601d03911505610b008401303a1100c0003c0105118822030340c015040056071040b400741c10081c15104140d4403901071801024142440e0b0221881841010b8400b85e81c14030b280e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 303482266 1250 303481016 303481033
    0x102100c1d01050c070b030901050a020c0a02100912150c0c0506130303060b0409020912030a17060409061404200112091b060507030305090303041110030905010207060b1c0302 77
    0x1540c64004200a41e810442c09215035251850100880005018201c014584074900710424030f0950300d000300b141c078207240184080c4d20288000242408074075411606031140d20380c0420b0480e000492644251040c14503400004280714224100d45610400d007a01403101c14440c4c202921074003494800200380390321038000115000561119028428400d250214615660b02c4000034107801c950018401d1a41c00144403d640c946240c01d05000103403140a581451541ca00140082c507640c0050300c048510b80780010700c3e80d07849901a1125640c80342c020810f1110b86a281e014414044500711a9110310a144100c0c408100405d0b811050b0143d4688114450084418000e030000e00c100b00c600c40100c004640140100c0c56444024090a54030b0355115061424001e082d40c074041d000704102d030020010321001c00c012002c070700740842058480140c0408003180c114000c01020b43d015046510104501d010040e89030001000d60008481480d00600c4440048460882c80f42d0000e0251740903240 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 303483516 1250 303482266 303482297
    0x230706080912030a05012c010b0c01090203010501031b0e0c0f1614030a030f18080a170c0403060b0402160b13081207080c0720060708180102100c 64
    0x1035521181c190240c640303000d02a078401507240c00540e151034005840b0401481140b1000256030308203904c4440c80320a0360b41c242c980018400c410700541c20107660000351000380c0303c0250090320b03180758007400070085584e407030502c2c2c0c00030482a5601001c82122080000e8815480308840780201c11103a009071801c0c02103c94028140d1100a6840000000301101c0e07020465100c50500103000100280d552005007403c01402c4a02501c0498a414034155440c7c4184000c0305c00b03050b000c2d901000e025a030380301d0382500761400a5115001d0301d1285a40c0200b02038620b80c1406041124418001408201d00301e0302040103a0040c80c18075040c5500d2010084003003085100300c250410540515400c4204550312002c03800e0780b001d0304200741001044140725040380c0c800d414503030103e5409201800c10321240c0c4c6480c80c0390600c00e1030845044040036002c510b80d4404013141e40705544004904d03980c07014500102039500c1e007081d50383d025004030402807650442600410000d88080e907580030a0111110 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 303484766 1250 303483516 303483527
    0x150a0f0501020601080f03090d0213020304440f041e0312090308030601120b1206041b03080a0302070809090415050106030c1709190309090b010f050703080a0e030412230706 76
    0x1062f40c1c4074003240c12090340711185100640c0600d0182d01821404a84d000d0b02e250700d007918403881c1c1100c54001c602a4050103100381c40703100ca80611451a5034540c0b00d0352811f90310340203d070041e00ca035642c074442c10451016200000340c1140c2c41340500b003841c400c080b0000e640c00d0700345210140030344030304000043c07003984200d400b1224040c60324800110b0b811080d0105102003810035264030694001000c0c40280955402c02c5e890390b00c80162800d9016040d95100b04050051041e00d4050503000309950007040048025a002c0060103407103031410f850325080c01248039811440011001c0d1034200003040c46440780c01a14540c0c071461f12480f101044039900701409101c01807801000e8020b40750b0000c14030100c00da0315942035001e03a881c002d00c0d90915115508a440b03041c00c450500c4081d080d1508440e4103c01507503a8242c060505510f260344181c00040a0880c0350003207480c900000402140065030703400b035071b04941c0c021060856015486001130f1041d4075041f105003242c0c1d01008042010900c41d2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 303486016 1250 303484766 303484789
    0x10f03110f1801121a1501050a030b0306130218010602030f07140111091005180603040f051c02010b0a120209061c0602092706010305150a0f0501020601080f0309 71
    0x81c00701c2d0401c01c0e500345000c0c48940203800614078110365015500c04c0c460800c490043d202c41c00000e9140c2802c1c6801d00d148030b04181c44020b41440404030b65064030300c2c026400180b1004019083e2415840d10000340003d040f0407060480c850016507410182803681b0140f203078107030355803500158640b82d1140c02d10300750798011807002c40b1400c000d1274800311118400c0c021020a044004145911100d40308100700c4004d19030a00e12003000303001d11280c1800d1641c9000c901c800403066070403a6680e21507042020740c56143c7c000241ca07034411440c0030131a942040300b03900028207281c3d00810440c04030104001111003a44030318007200c0e40c40b981180240c502800f89a4000e04001c0650310902000c81004600740074040c019520207a000c41c804516060000721103450b0002000c4820001c00c06034001c1030034031005003849040640e110300007840c04404102c10000140e00403c1002425a00e03038525400d503402e8000c260050052a00020340c0c002d00040420294a803c030166080899100501840440a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 303487266 1250 303486016 303486019
    0xb0103120c05210f0d0905010b1c02010c0c09020a020c010912020d02090702150903040609050f21010f0905010501080d0c050607050c0a02040c031a0a05031504020f0a0608010608010f03110f 83
    0x20840d8118601140d0000d0529480c85e020100360719080e03003042800c444400342100d0080d40c240410100030207803d222840c61541c242030800d02c0742c80c01e081038130281d02943c100d220207901c005500319120341c0009013040b050009a0b28003269a8580802089501c8000c10003900310018210701c01c01440c09041059010304a441101c50b94402020307551a0503400f5102900c060300000f03018464180c4c001076041c00f9000a8907000c01414a56001c1000324003402c18400207240043e01c10741e04ca01c82904403800c116000c603024815968a801c00ca40200003e2040c10f109200304600b00b42101e01400500c401c10303800001a01b003a80d250102640c150f440707030104c82c515008412210380141c0d524450460303148219900081c0114004108003002400c001946204282d1582d042100c0d58001403ca14081c011121406880e00c651011803070340554900300c0c55000c0c81c081000310380340d40d101c00c50030b040301c00a940c1d006880c5d0303a48180c8003002000c2d00018066080c901e1a070300e101d0402c03041d682d116460 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 303488516 1250 303487266 303487333
    0xf0f090f09050601060809060901060b03190b060409061403010902101215180b04050103111509121c0503090703061802030607020d1103040e0112080708070b0103120c05 74
    0x7002d66981c2c1c02c2150982012020400c00014003502603001c00c0610352121892008000003414034111401c103000081c2241d000c15911a1642000c00c5640c2020303100c2080030345400d48698981d203440b000780c5150f014801e03802170b0814100741e2514050051f81119500941340401d6403c01d041c00301c0706400158030720200e16495030110200c50540760b4115009155032001000107101403807105060301d000a40c0540f05604082c0140003140b44003144401d050801c403104121301504042d8076055020700e0304007580c8480b464105005042c6c002c90240100710501d9080018040b03440801d8130340d40401e031803060f2158080101480042d5543d88484500401e10040e810050701c2980002d00c0c0120444240005802519902c84040d4101c594000252000c502440c00d15040901040c42d0000510429203184064a03058041c802c4c0790084400ca1a0024240c96454599041c100d10328013007807008030707140f801684000540c0b6100e0040d180c0d00950100280500c10003110406c045815902c183c030801d40d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 303489766 1250 303488516 303488531
    0x609010905130b072c01020c2206140102070609030c0509040c090f0e060c16110604050618100c050a022803030221030106122004090906060f0f090f 65
    0x441402c0c4440c858041660f4185600c1c40c03105500341925400340540c0448080b541c071703115541e80c010a00c9413010105940040c1d10000c00603c10448038052001204414030b00040841c40024002c00d028503080c081e021202195a21007080310009540d10008e003031100e08410500c120f1404440454005006602d105201525020440110790a00f103405640b00d81d01c040c81c0454041c14041c05030b01910345400d40c3d040105a50703d1074021441d0340d2004240303624541d401051030340c0340c0701542c001c2c1101514054488207810810200105484002441041c03001d4201d46940e12510300048056444006846d1041040d424001e4502900404020180e8007518400380740345580360303110084d4081e134005c2c5800036034a5045211b2104001110200c070b80100014890700340c0042d00788402503100040020828100120b0054045090309030303c100c500006000540c42e40320360040c0c0d400354010b120070000030b80d4901ca42228090302e40300d05040c0a52104c02000141016400760443d5a40c2020124100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 303491016 1250 303489766 303489773
    0x30905010b100e090109020a1b1713080705060405010c020409240c080606130302090c0c03030c03060108063a05010903080f2a070201020f0105240108060901090513 72
    0x1100d5071a882d400098004020042038580b268003a0300402d80c0c41d104514210040310002c0c04107155100500d032960f4490005010042601d4044140400804500da101e0092015005407450984601a010322034088082120314045080710225032050b120f0460f000040e07800c2c80007a2503049002d40e05009008000c07194886a8026102803000a882c000361170131102c00c000d0400d28014220601400e4280100042e00058401c0482600c2e0125120062503658620b0800c580c824100404142c1c0404024070818115800186000310800d80f2a0310040d51030074240100310390108110411080003503696024100761013410a0203000011841d0f442d500e4680b1640e0a5440415080f40000c03038130410401e01c80c540381845e9402209a585851a1101604400f40602181c0200e4451490002900000c580c020440648154141c030000c0c49240f0b030549491100e42001d4010101440209600e01c8643d0b03c00c2c00410711608000f016600d0b05d03428018060000e0400812106200021007840d1010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 303492266 1250 303491016 303491029
    0x30b07170f013503091008010b0d200c0d03051608070509060c15040b0132060918091009031707020708030304050601090b06030c0306090406060909050c1f0807030905010b 75
    0x1040030729002141c5c1c501c3c15900780141d04c201c640070082004030840040c003c03407140100300c6075101e10703404020401c0344528078011740340050b00000701145034001910303120702d44020031280d4010580382ca00f00151313515600410400303c83d0f014040005040300c00000c8091b4000d0300548001c0304c02405003810f0400486d54131713141c80082c5042c800d0b001814000c00082007040c0314442c0c05401c0446104032103440c076618984415a80b8682820102400005030407643c0340c24003900c2941100401c1110002250071841c15000c1b4280c076094064042c0700940c92405499009154005505940e10315600c0044251a03000d044081c0c840c8086005404000990701020070240d80240c0c01130340a0003107549022501411100300c802b1040c0240014400c2056000d0540266540300100b6500405160f903145842c10007802d0756080110694035050300c010512900083c0c1041c4c4140031b0f2417000c00040c2c16000031141d0480c441d50725000070764540000d58090321079001441420312075000400c0f5841080001080c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 303493516 1250 303492266 303492359
    0xc030e030f21190c0f0c0306050402150a120b03210307080a0b060a081003021504030506060607380a05061801030228030507030b07170f01 61
    0x100ea030102e2520002c100b41044180160b440039098a450180072041035215540c500e60301e0b8091041100e500000e1144200c06103c01d42c1d48000c401041a441340791580081c101030301d0aa025072081c51031a02c1c03818a0030201c42b4140040e84440030301c14688114a80581901385115415005100143c01955090404a203c42c010540002e40780e1034010341c0108240b500074132030794206003030403551103480d200d400132950013407140d117405121656805501c410b98031150740004c0d04001c880c41c80d100b24018840c09030040c0da1144050f0785a030745a08007008403c1c060b844026112403064241560481c81140f00050300c0041c480229000883c5c5100303081c1d40303180c2120418456604d46081000c1e078070349010b40f610302d80c00c5060005450750641e008101c100d420070300c5800301c00f0444a811072a51400c88402c030001e5500500300d850140d22440c0a44500c0d2007542d518022403142c0c00309032080d80e0803044181c170609442203814142d0303103008045441c8420b02e0000c2002e00100f203c644c81000c5000c2c0303103000f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 303494766 1250 303493516 303493543
    0x110306060a11120406180e040809011b140c0603190203071b030903030f0201050403140901020f060c0d0605100e0d030e1c03110313090231080105010605070b070c030e03 74
    0x240c481d481e01c0c0300500080a003d008541e40706d17040300b0600c000c2c150014000d40160300243c0700d40e15000340c000180d8100b451100411580e0760f0100004081025140360301058900b10300664a16441c80b80034440c240c0003c0d204641c25a2a054441d401c6c00b907264082d44e070095003807402030030309412014014550306800c0c0c81980041e08422083c001d250b00300040d8607507000c8501c001c00c618078050301c0040248505414082464000203014446a0310030414101c5420881c001c3c1c44141c04d200c8021001580912541c2110b03e080c400e0004561030400d90700855007005440b0031051050071010088048594041101882200b66040d81d003a112000101d5a002c042100300d655074416080141c4600c5a403146002c03564002c01c15455407501c3c02480c001103a00707000c805a140d500803800701d400000001c651038082c0210070920b425032500103c0c01d6007242c06a00007002581d03242c0710201c5091050580140c01c40c1da80f00046000b00b0f200d0074049007090b00900d8544010f41c1030340006801d0454010b20700c0d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 303496016 1250 303494766 303494803
    0x6090201032012040804080d081501050a0221190e0415080a0209040c09021201060906020a021507050c0301020a110705030f0a1401060506130602010f110306060a11 72
    0x542156014410400d22803103240d0a016581c0840041640c64460f4050341c0d80c4244102c40440c2c20003020398192405440c100082d43c3c07118942ca240184400800c98048801620030340741600345500400c1210068881c40d80601801d07a450100d031080500c510b180b440300010108801c0311040c801980e0303940501020744e80d580c0e00420107810002036a001400c1034803000744d02e030030410080f00000340c800401903050701d06e5003103650380341050450241c0039801040702c40d0000404e48180700042213a14180c940c580c4441400b03a880d0b02d4126610661554002c3d08088100520190b0740404400f90a03d0b500c20011100942d80071800705e400e80e08201ca4803000b1641d1850b14013a800800d0001c60058030341500204043e081504545544a030b48405c05400c43ca0845800441048203401c01c05c09481c0c06400907941d0081140707030a030f1080c800d11602c1300551801d00103180c82c5040e80180c48812742d00d504c00d10300703603121401000000d50041d00440144401d040c66000440c0b000d00200100c41314441d0782 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 303497266 1250 303496016 303496031
    0x160306021c1b0c020105120901050417040608061302190302040612090506040b06061303050c090a0c0207051504080a080d1508030307050304030c050f100f0b01020307020f0102070e0406 81
    0x1140038000725012505411070030b05140ba030b02da104280440298040794501200500038038001a113040c032803002512560a8154200609480150000346c0118802c1c0e555800904c10315030b03411280d00550081600140d20301001c23640a02c2c01e0b290f14051030304031440051809040d80c0500c0d2140c42251800c0000c00c2e0040b41c20000b4540014004c0101d001d201428882c40646a441c0e40e250380000304020b000703480060101c1c0d9513844440c207030340e0240482c0e100140c4450300d9080082e40ca00340c4204140c40751484900240e0b0348101d5000ba903c0d85541500140325480c142010015031031400040040d40c1807040c0000246401c042140c00c48650044d0030082d610891100000103542006100c0b104a0308a8401000038403000022030381e1180130f80c82c165031a0f4031039143c01c4403000c40c0f10310040c1c01485a05024449020b000c00c010043c190303858000c2100b801076045110039501071004403405a0000c2c01003002504004460300540d04051050302d003116110f0540c4000c903031050750165000d80e070301e0a2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 303498516 1250 303497266 303497287
    0x12360607030c0c1109250507051623011826030a020307172106130509190c1a040801050c030114040e0111030a020901021b01170916030602 61
    0x22400341800c80d15200110840a444070150000e101400a001741c07500c1e4001540c0b0f1083d0902c0200d800c00f615209680380c20102002000ca030840c0c2416234440c0180c110110000082142d40d60807103000e40a078012400210301400783d803000d1b0042c420b0500c06020b03000050640c032020010007170020f05420000341c910000b0741e1600d4851280300c04610354420001c04a40c25000401d65091580c82012141035101704c408415080c001d114040d200021814200c20124541a0b240c0384900b5080d2446014910100d4298050b070b80c003030702c1805a5800a06500c84613240200307200c29124010030030303c410b10395a00c1600401e22a4101d440400700d2021a01b408500800e0080c41c0e0000303400110503045504004c240c450418509030042d100e00c0d0348919a1040c04029002009810101440662640380000700c01002c6c6d4401c4135068010f020f156074001c01034804209080c0112410380d030780f88102e018160703146240d18000d00305401c1413080d01300c00844100150100300c0614815000581c88100607070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 303499766 1250 303498516 303498521
    0x30a02150c0c1e010b040c1706090f01050d0303060f1203140901210b0a031416080303040303020a090305030d140105040e120d02120f0403020d051236060703 69
    0x6102090341c4004100c00031081100080250140410a10b8480760706241c0c40d0031401003035020311190b00141000711720902c540c3c201075010080004201d290806a8644c010415021822030b041200e1b60304990050016051140070510a540310341000500710392203d80da03d03091551684052140b211001c241010194440c2070000768101c2032819a080c00318800c0003030701144c100784401003054119500041c0c0000a030b002103845c90070146c0300588407520f070b007800d01b00203d10740c5101900d842103102e19520300c407451601004a4443c00c002c0c50031074071165800c4020350b014000540c10895585408004600140002e0050040111000400c2543c480c41c00700c0d41c40c0c05074401071080d483d103200100402d030041a400c4d4101902c82c3d0a0b5600c08151011800078010003404034088940601081071103081400c686015078006d800f02c1c1d80c0d00681c41c0c0111103d200350040d10b40e840c40c501000c290309000948000d41200401d402c14002d1041c1c1e4007582c0c05440300044403043c1a4056000c0c82011034062 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 303501016 1250 303499766 303499771
    0xa0b030c09032a0901060e220f0b03010c050a0c0609050a1401050f16050a0311041e091a0a031101090e0a02070210020607020d0e03030405060c0a0b0c071211010905030a0215 76
    0x64404e03c160350f140ca0800b502c003000c1895100d000f0309140b1120b070701021a071941d40e84c90200b50003040022101405542008003400565070f8003030343c40d248500034114003403c2525820380030b540c1e84c0d000311340f52030b0703940c101034038484c00121183c0c4255060140000d454070004251041e5090000a003854900050003441e00098411500d4120722034144c440b0541c0002140c000c1c0505060204003a00001e10200051041c1d60085007031410440814112181d4400f5650446045c18410b21195001c50480d1004c41030000c1c0c2c0c1c44c0c0c0708a80b01d10400004503012540c0c40c07802c1e0b05040681285540d12020b02c05402c003150840c85242e40040d50f001103150841c01640b4404a91000f41074516180ca40030703543c2e901c0c884c0d21500340000c3c1e00c60448507a0301041120040e103405021161502024001e0940d10403001100315542c10745503001030305c500382c264281d0341c90a0308114150407a4000c0d00080d11410f02500101c2c03007554031500c49a002c58010030082490040359802040d1481d010241d034221007002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 303502266 1250 303501016 303501019
    0x36010f03020604032003060c040303020111030f01060f0e0402030103060e0f0d1b0611040f080f06060f04020f131701110c031e041502150705090a0b030c09032a 70
    0x44000a00c056160a800d55064a91141c180701c1100d451a461100c580080c8646950510501e01040302e1140785030054000c0724803d40081c820718001040b040101d0004642d0861032a0b404401048900c0c81810080e168200d1410550307043e02182d030109041e60705c2600309407246d03030300c590300c10b034a42c4030070040d040c400120b403005481c8011140d00d0007081c08400c48489103c00508800d068103100c6564000d0011030403c00e40155610b80c0c83c401504500b80502c01c6840e54040c0c69426400200081400c85c400c0780003e00c0641c00c0b00140c01048020341020a658809001c1400781911008120805a000d4140e9484843d05500510400b07800c4d07e8098080d411880d1060119003400b0300f0000030f503a4601238140640d04580041d001c603035054010342e401940c9801001c410000c42d2078000c01e003802030901c840500805662000001c0c1c80c00d00c61410520b4000b8511070f001c114030f06016014681050304d03000100d01c0c040520000903c0d01a0240e5141c0042c0030104108500701024484d40146990 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 303503516 1250 303502266 303502289
    0x118020f090f0601080606090402030a0f0c0801120b0a0b040c1101060b0f030408031e150301140103120f05040f0303120501050405040503270406151103273601 70
    0x41800280b9a401d001501d45814852440702041c1103588030001d07940000f4001c3c00c00c40d26403030822148005004101c80440019180c00f0360262003070b100300c4d020b07030685070107078000004074200360383c2e03005201d00043c101c2c202c46545088043d460b664900482d5244c01c0e807695240d45031500400390030b0844841e035000031b0707510904008c050380e007174115001c0d680d00c036401074200f036125510405180c245002e030217500608091b000e070400164040f2042244056203007a4000c1010032401880d5100082c0280000741500009010a5001c075101c0c1200c001a202c00707250090401d0781c1c0f12000000007003103030821400b00f010962401201303034441c07003518014041114148460305003620f800ba03d0303124a900358a05580c0440f980d15030802000500d00b90980058420040d00b503941070702c0c41d00000410311400018080c018192540080042515114040e0030680303e1102007103460108540c01140c4055080f0290110304d0074504049170604403040070303401441c0c04002d020060410400d00581042401c0d52 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 303504766 1250 303503516 303503521
    0x3090608090c0d0f0209040c091104060503060d0302072c061f08092107140f4209060108010204140f130e030421021e0109080118020f09 60
    0xc400086288014038107a91000d81c0607064205841c2e058074004c4084e41040000041c04100400d8801407c1100d100034001c01605c169500c00f501c551203507110b9240000e0040c000f1503c0d038a8240c41300c1140b10310030b0045034852960ba41446820814401da8210071fa011040e18800c0d00210541c069801041280e00c944d04a01801c0b0150080f000862540200811840068001d84041101c100c00040c00c15260700840d502c601c9044080d8820f0b142103400c0c0000921818420000043d0b410183d4090300c00b13440c0c00d04418001c10400c0d51052801ca2806a070b0014075210240d03050b88100c1045002003060141d4038085500515100042e8010880340e84100420008240c0420030f2014030031048030f090a03903006800000b02d01349802d41240b0f12542c50120035040f07802001004200b01c4840c0c0260301c04080558400302040607841c0e2000e904003444c107042094521030b90300c7d0040c00c02014108200c00341d131240c80701030031500104080b8003c41a43e44e80391040d450310030345000340440c1c121890034152 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 303506016 1250 303504766 303504781
    0xd06050301150306091a1f050904020a150e0d0c0602061f060e04063201091802030c070b0106080417030c0a030504031101111b0703020604061d040606020a03090608 72
    0x2541a8070000d000300d41d803014a82d0130404403605550300d034905d0019005c6c85081c00031400314110450b0441c0f14510408540001d29801c00088c450700c2190001d010b03100251404134106000140b080b40030013000800b4021040715601c42c2d80079401c5a0041541c0300aa50900c0c0e1701a15180b4050504450070b207205541c01d5444888000e41c03001e503040b52409103030410056010a0107040c00c0c0c0c001c130107444e106031001c4400800c02c10032038500309a402013105445507a60015070b400c112038010700011220304221105542b942d0380041d904106600c1e850361410034180c6540e4011802070704020000f0704000b090205201200e0b000080c682007142083e45941008196084280302e0301d15000245901c1da00020103160282490101c200c10560003131000100764030030015664010880303040f29903800882d002d400b0000180a2054070382c0907154510301418800292110701e80c407540c041102136110800b4500c2c1c2c5a5008840c010803c540081000d941a4a405071072a51550404010080d4220810508 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 303507266 1250 303506016 303506051
    0x7030203060a0b01021507210501080309091504090c060305011e1514030c090a15020c1903050a06050601020f161205030c030f040302011d13020f1204080d06050301 72
    0x70401c2d0b80000036612440380c0050341012a800655032200d10042c0800c00e034a80c0040780f82d040f41402c08000312407000400d0580040740c01c00e0150440d140d2091002c04101d0401d5100f103a08502003088403804203135584001820b4544044c411918212060070421019400d80561400740c40081c40042c2a04410855511240c0071445040740c108030186040100901807094443c80e41000d0300d1040e520b284c000c9000880364000021940138041200300091030342c1c035400c400c004854665000d012440302d02d00400c607a4002a452112070704003c13002c000f00280d420440b00c0d030b00ca40f0441c404951442d2650000e810048501d40112540c2c0060008c00b004580c448140015150a44d200308481205820042e06e18003880200c0d514a04c400140320361040c071034002030306c1228030036680c40302d032030001e03601415258641f51000c9400104111084d00008004e801519000300941c283d5420150160500444e090301620300b50742016002821072000000d5003c0d10b40540029030007070040000b481a600c02 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 303508516 1250 303507266 303507271
    0x5010302011205040303020c0a030e01090e0415020901020f03160614130204051308070c030507151416060f06050f0d0804090e01140103050f06070e0f0f06040b04030303090506090703020306 83
    0x1102c65035000001e04043c02907050f03500740c4200c0c4080301d11445051401401c28400150418082040203c0c00190302d405201141c1c807550f486800d120482d424103048001940280f040d850643c05505580b66032050200080c19060728041c80644c42446035007400c4044807208208030110191000c200114090102a04d0340d506505886c00240340d6515400102d8174642058010b10090b0001051000c0c80940440344003030302e0280c070945907820f50b181131031240580707108501d0010911a004800e400c4c044840900000c14021020170340c0031007a075645508803420100c0c400d400700c3d90740505102c2400e2000502c2c0000c84152804100340d211034070707225054000c0380b0600301980d40b24914095001000c0d000300d4054050025007560950b124606070b5145c48405401c21224403c15000076440780c800c42990f054500d014125030380c0480602c0500410701d0f5204d16a07038010404000000b1442006030041000f1400795500155032003040c54100e05001c005028a1041e038403605080c0302590300030030300c0c070b4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 303509766 1250 303508516 303508547
    0x50f090307031d04020705010b0a120209070c03020c060c01051b0c03040e0a02190507030e09130206031b04060f110309031905161805090a0816031205040c030b0108010501030201 78
    0x4084560440507000c00030f0f43d08003a0003900204526003084015001912026400c50340102220348400b07801c141d860600001a600c81d2554010904940c0181d1004840c075001340306035080c680040300495465840395407807800907951340c002c22062046050404803034540101c111880c100080c000c89a980c0114052180c0f800521000b01c1c1105807554103c0b0ba5080700544031140106840401600070742103420182c0100f200780d801c0d079806140900a42c0c1c459111310540700c1040045400703108151300014440d00c109120100302540c00356200300503100421155603400030040c041800103007120003100c01c04074154400d0119039082c0e580401c041c032000c851100c48003040b111500b44031780f50005440c48245550450403000c60000c000d101c0a03811030442c030b07409001c9901c07407103841a55800042c1000e40500002d0025040b500c40d811070707000e4400e0080c6084544003a070201181d080304c401fa0740c101d03141d40040380b0800400c1081c0396010b00400d0910020003140d803558001a01d211017810300c59 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 303511016 1250 303509766 303509777
    0xa0c090620010603050f03030f10230301020705010e16091a0906031002040303020102040e0108030901091401020f1c020d080118110c0102030709050f03010606021009030905060703080406050f09030703 88
    0x201c62030000f58880402150030404441e048844030068503182e60090b1010741c003c494075400507030b000e84811044e0045803080b03409000103e1031020002c0b180d404056480750b065400b0480b00780072803000d0290f00300000c0c00502500c1903142003020328003e1203003580903100c41414454043c40010904482c01ca405005840000c0c0d90340d02c070400207041000c01c14030103440e1351011a010003030590540c0540309440c0c001080d41d149980301c1c809280d403405040481400242e03c0c190a01c1b2010001e1001d40718054180100d845e0300c00c0182e040c40c24270103d460140c034045883e02c0c1c4982050307410003c2c2c2c92a2600e5007002c0b00103505140c00022485506014565025203a0401d001092520300848030402d0400000710348070300700028001e040d0a03461082500c9195a00312580961406115090445450b9001056801d105445140150100794000d6062240d03203080041e254444400030090030784a56030756403151810b850003a04584001d440e8040b0103040c0340400180607800411202c0554050810 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 303512266 1250 303511016 303511067
    0xd020a12240507200c040f06050a0326040602150603031201060804060b19170a0f14100c080106030504051c093008070501020409140a0c0906 62
    0x24070700034a41941d2444254600c800c840031507a60940c4010b0040700c0750707903a10421002107104880c2c803100811492600341c021010020003490240d00004110100c00c0010400d01c1d80e800004130400c1c0c042e4003e80307a400d40106c81000291000030184010140103180c2c0b4241424400d00070b543e2a00c08a800030305c0c0030140b01281ca540c4e4104242c801d004c851400859040d030310f801c00240101001da600302d80d0070b42000551110b80c03500b01c2800c0c000030011006041a42d00c3c01c0a20b001600c0205003008450041031f00c080040743c0e4580d0040d0303106010740e618180c0d11890400c16031401511403401640c841c030b410b0a14002d40d90020003181119841e150205081c1c0301e50500034107184040c281e40e0001034441c0c0c85081d0558002000500700c40600311916044000501900034091a00c600c0c02c800008050601d0005103000c0090140c80c1c2c06103000600b080d0f01c42c04502e0032220201c2c103500c0800c0c041030800c00c105080340030720500c041c501d1514000306403901c40301405162204206100c0102c0c0d8008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 303513516 1250 303512266 303512273
    0xc070303020729060307080c0d0c0f080105040b010801020403031202180415060207060e0306010504150801020a03020d2322050604060207030e091003150b0d0b060306060d020a12 78
    0x1070714105078011025a11108100c0f010401c80c103941d042c42d000300e08034500018080d15000c15110110395401380500381800d02541042003540c103513070741141c00200d03802010800301410001507029140c0c0344000101c0d8281170402d4952500d05a0081120f030303004100510020b40d200c2e58071031201d506454090f0b102c0c41100c0442c00e941105003c0035802c1850200245450722030005500120b894913003d440e522600c030001114925410341d4041d41513408803004001e141400e91020010060721542000c55985030409142681c2c00700f41d0345400241c0100b644102c413559481403800c11420641c0c10b00d01003140211007280f0030801414000016441603040440b4408514201c142d20f0b40041602c1031840d1030b20b0a00001c0d004540d00342c002a4803012501240c1c00c208040c0d90040c0e589000104200e450340da2074091120792283c007022915260000084c041d1520300d034201c0d140d4860f4544401c2c43c90039006140c500741000b084503200d0308600c00d209003d40c40d20304155080e900c4810140742d0a019904 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 303514766 1250 303513516 303513521
    0xc06040f031502070f11040f020a090312020703080f03011806030f02150d0212101703030a020c03040e1801050903041a090312070302150c0306090a0515060406050a090e010b030c070303 81
    0x22005068146030030450350403c90441b503021a4100101d0b010420300304018003480407030080c01503140224145a03000e00114142ca4001c500d005241d104440b91a5160750381c0c0c2129030001e20311140c0b0840040010711108035085020b945101e00100100101491621101c0c060550b00501901030460502540110f1800104136981000202c800750740c2d03940310400f90001c5035001c803019454046107800120303218112000500d85440c2d044011400e5031120303d0391000a520481101c0503610081000094074106c0c000e180744201c0c207250520700001c400034040d034250746000b0305401050300100310500120381010200140110500200b0351101d040f00d001c2480c10b8502403032a980d41001189100400d035002941c0484905000e19080254a27114100c214038042554000e61080030440000c1800c80164012076000f0511582c0078074010045020030082e501030f800c60b90000300005048101150030110741001420211400316203036151400300d004030301029040380c0c0240000120f03c002e051003034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 303516016 1250 303514766 303514777
    0x81b030601020106051e040b03030307020c27070509090f102303062e120305030619061d060301051503040f060216060e160e1e0901020306030c06040f031502 69
    0x380c05100451b80f2011030742c04d10507900104030720460401160325403038240802941e01402c140d800920099a56104002c501400121208098139203102001c030f0408548401900540702d54550503075950000c414000c0300e04000300350100060700c20007404000030621418108640500b03c40d41001185440b5000b404802500001c0e403500c5107105014403032500800101c0d00c81803030704001e411030b00755180d1201c03451140e1081040070030400f0348820210f0301850085078000001007480040e40c13448100000254819005200080d00114044901004051343c0840840c4100c8945041d50324080000340c4031981e2140c0800b01c600f0220204e0100440100d00c4d18125503c0340e403d40d21030551030000d05c10045504003da84540c00c0c02c040d05008500440d44140409001c440c4220319803c0c00b240e1444043e019040200009007a80307401d0500903000007080c012a0050005641e9007000800c0500d0035404007491480b400302003004107c82c070b07880020301044035030009120f008034020701e0600000780541c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 303517266 1250 303516016 303516019
    0x17072d060f0b03061618170705030d08060915100804151116110901080109020a090c120e0f0d0203040e010501090f1502031c02030f070503010f0303110f011515081b03060102010605 79
    0x944c81d007c00c035910348958003030440c1510811500c005545a0170555180b4520700c01802289440001c1403003030420701d52641c1d100e6014004c12031254000c41c0483c078940c408440b181d001075400428030042000c2090341031100c0c107403207009010403c00440c5032100e078803d910342c40c0c0c0341514080504040200d502440b80c03010740014078007240c5603034808825000c0c140010381284207007147c042c08503117076005104a404a044076510010111040004a401000d034111006030030321840e8114400d140d4100700c0e0400e4160307150702941c2c035a460048007414100c01a000603050103000316007070080d43c0b412103e1404940311141a000b01a00c42281a411842929604547d8603110305a0aa41203810740045001d41e10301c09003410700e980d60510444190100307004000b40d03240c19590030004a8401d41a000106807020242d1701c020002204150840c7e40c11800041d50016140c0d00b00301d0340148003c10103410105040c064502d142550346640002d11002c50000c0500c001310110304039034400d6100d007003c1c0c1340 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 303518516 1250 303517266 303517307
    0x40905070f1724010b0c0114010b28080708100e0a02030108150709060e06120f040209070806010f1419090911040317072d060f0b030616 60
    0x7100c0c000d04140c0b00e040400400b440c40381030500108140000390810782c64401d0400702826034241004900e0b00e03441024540e020350340750010011003588000e08a8000c1100c05005603031081800036010840c118108001e01600c910b0a64504042c2c00401182d030050b16440c0115050352281d840c0c5c40200410340102440740304040804c040300c540e55000354141d9040804440c90340c504d101b8114590035088825074001030705210100300c0b007405165100b0318003400030310f818100040102502c10403181290741c0300403a01582c041c0010b5050070100c070f42d0069801d04d48800249003080000c0c0c41c4220301c0002c0070800802c080d4840d10b030410141a0341c02e0b200610071107003800c0255840104070526501070b24500300d16099041c2c4600340c2081c2114200c0c4d45c880c1d03480d040c28030742080e03413010783c0c00940044c0c9331441c0420812000044400d0060054600032001c4800d44105040180803100d00111555a0500e0803040c25129540014180d62050b200800c0550b116010401200e0089514000c20507069 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 303519766 1250 303518516 303518519
    0x803130c03140a0b06091608070201020c060901141f0e0a0906180605010b0a0909020a020f0a0807060c052118032d03010b03010902090307031703250e040905070f 71
    0x300c003c54040150380c06040c541203103803280400c000102d001500c0700345c06c00300e00100002405000701c0016501103030500005040885206005040070421107406150365560343c604c0401026110b501508448603000790070403e0020301c0441007140907805502c2c421801080060320100850700480c000c247c0c8840c0c03d105d203041c070710800707035183c54004000c0300d906040000100d1010700c9501a10000e80c01c03640e0b11040d041c80d2030100f000a41c481004802107000c0c40030010315150301000701c1ca030154410500303280c3c2c0340b4450800e0012a030009130300d0070420208008002d5281007000141944205410904031140c407032000240c0401121218121503000200700c1c000c002011a0383c007260019490240820952192141c503504d01c401d01811003012820302c01440071920541c00740401045c00f6048600b4552030b5101c1ca1101c0841d00c00700d0040c580000100000725110891400d4002d000151820a01c030000380054400501085128044ca07500d05d000c40074490700b00304d00001002140c405041390b5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 303521016 1250 303519766 303519803
    0x105030718120605180c060d15030c0f03060e0319080a09020415060806040207120c03090302030a0b0114030c03070506130f1706130f020d0302100f0c02011401030803130c03 76
    0x3080c045441850704204c560790385017020070201701145a02c1d4010140c528001c038000d60039000741740707448021403405078241c000b0000591a10402c0050b0000820a4250380c0c55440d181d803e1b1060341c162604140c00c1802040f404c5042c06907051900e01d11424030400070b075900200c0d040200144c202c0650700905022030540d40e02601c2d000030701075501c680c3c1d41c4189983c0b50700911040c1c1c480c080b40105401c04001c84412070522520405a420f442864007a41e00b41c0da940010780381c250400400e503100c3c0510801000100b0407001e10204081050b0003500042e1040d00001c2d848032014881d0900a1200299000e0b210360a40b49000141000d581092903003030701e406c240000a04100c00351401407282001080b00400d403c1118802ca6510514480190380182d0030700a4081150100b24150b2140f0790783c0d00610451070143c50b0b00c081071101c000841800c00000242507a0f40c009000341a002610f0060002c100180b0071260311000c07182c964981021603140a603c00380d4903500141140d1114440c040c00b1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 303522266 1250 303521016 303521021
    0x1030f0e0a0c0614070c030609050f0d020106090e150103151508030403020a0b1305060a03020c03030f0f010614030105041109150304020a05040b010219030e0d2f01050307181206 78
    0xf55420340c2d4071000c0224452054900d0340c802e42d82c01070200320116804000007255a003040304114030072002e41d200900498602841d14075450400c5c0c0250351202414030142d090b500c241c0140d1010000180020b0000e081038a2208506001c081d10100301080c607411000702540110099203070f40714240304441d6465128035100e4002c2d0004034441d19003c1d07400245401c0b4042903c0000e024580700700103180c0381c2020050558454010401815000c2c00301c511400350501c059032048140d80d00c1400c0901e0302803400402107005801400a0080c4204c02502c5050410140c0341541e001381c8002400658000700100d40c1d01451801c075034041800f8007000518032004000e103000e54405c0c1e622108050b00c4c5c0040009440b2890b40c80d0b0700503848000c0d00d6401428402020b400e6078068205405107000a02c040340100641034400d880100d489008821211442c1520b500e08140c0e952110006408920008040e032001500e102c0070010102c1110465608526103000240100031200e80d08407001d01c2c003c000b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 303523516 1250 303522266 303522269
    0xb100b1b0c01050910080405011404150b030303090d030e030403120f02010c050a0c0213111603021e15040c0f060801031101090302150d020c1203100f030b0601030f0e0a0c 75
    0xc602030415115219401030082e5071001000501807281c000812908940300d5000070400d4a5541d26003507081407400554009038002d038000d0703e40410501c58914203500340c841ba1f10000d40203a1041040181821000c02c0703440b401901031402182030800c0140051960003140c01c0a03000507040c0904100854007c00c82549940440d0000c0c00800b141c100c041d83c05004803400c030b0020940300840c26005140c1080c0007101d40038031a03c0083c14810200202c0b2240c0c01c20f00c4513020f40400c0c40000d006164040150b01d03001603001c030040010200d001c80c00360321020810300d200c48203145540483d04002460b05200003420303140c041046a0341e504c40e0028075801080c0320998565480000442555118480707140a41c0e4014003110040c290f40b031035070610b5910003001c00701529070a01000035130b000140190588002c248050300d80b030b420b15495641e200325459000708441c040d401400c20000d900d81c044154402402d00b0002896038191004802403c400000910309004488142c010849049107140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 303524766 1250 303523516 303523567
    0x120f0a08070e06190c0f03030b01120b0d02060307140a020109020f120601170a05010e07060e0901290d05040c0603050912091519030906110a0c0b100b 66
    0x8205403149502a145202030200c400c3e0400c40c10440c403c01c0d4190072640d03081015861406141100311501d0310300ca88808464220b000075250b00d40401c966034440c810141c60507100000b04000044500006d018a14121300240a030038040009008a4052401c610409001c135034400d54502c4d666900074020158460b0032482000c036681d6402a81c2004103040282400901c0109526400c0401a0300c40d01a03603941454644102c1c9503c03000240c0078011030110305aa00b00030000c050030310300068101d400c85c0b102ca40c0076440c040e00401030030038054006104200d040c1c0d00307104883c1408854046a200b18410540e081d400c200c20f01c010003220300c1c0128100d9100707540811884e2140300c1402d03160b03280041d0b0000c100c00e06101307108a034640400b82000304a9142c2d0070314902400207500080c031203440c80c08440401c4d9100030302c3c000d001c0240030302a83e0040401d846880c0501074800600b40c1e12031240d002c0c140c44110000120307106105240d00c400f401e07054590701d4850000c07035521012120700c020030381d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 303526016 1250 303524766 303524777
    0x14180103060b03060c0f030703200a09140607030504090504020612010b030906070315050f0301020409050c0304110f1003021b07140310050708131506060c02030607090f05040e120f0a 80
    0x4217111551030a4440c141c010105a41c995160307080100c02038101c413603060503020601c2d51380d03600308607028004012580b16501c400344460b03c0c00142c1da0154902c0e100302802001e04010f01800281c0c0502160196501000c0009960304e442c008507449005440780344400450410012031800c0074500618420354110044400c160384450044050340c2441a2001c9400c40b1040e05100520f054002111042000b40c0014201540c40c54508151501a200020165400814030040c07201090412111000039110b1601c0c950110700410341008604012400301075000c03c180f60132510007500e050004800c20101c440c4681c44415000c440840c541c0c01c28464401c030f042c0a0811406405114801c0340030740c0320b0b503503680c0d00e0f1440ea455514007035000300c5050000301812010f4009604c1040d010b8485642c034a1040c1020348145450040040e11032800e110b061101049200c1000080038103442069a000c90b100d50480845450718102014504501c0b002250758a0032150110190100b52495981c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 303527266 1250 303526016 303526021
    0x30f0406091511031b0c0d060e0d0201060e07030b130905010209011d13020304020d330b0901560307021009020f06190306050102070f14180103060b0306 67
    0xd450711201d86400c601a500140061117062864002030200014441c1c2620803048040c4005800e001c1c000708219100c2e542c2da6150581c030002003002d018130f400c0c580000c0028605200b441803160301300600c40300c10142c1300c180c003a000307480d412120150003c280605010075445458014081c1d04400103050000d013502071825610120140c200c100004003816041482c03200c14003010103540000d01c240d8201078440a4040060002c00a440881c0d00390b090040d5441e6078441041110740804100e030080d9800c058103469985e640d1000e441c116a0541c06403c0e4055070102c0c1144441a800802040c1d1403590203081c1c14014012908502202002855030540c401c200300e00b0090700098801c000160300028082c8051003003a401410031500040080d07421600d044002045580a40c40c05c00c4c440c100c2d00304600c00c041e00b50159401a0030b0074000340114a040c4102c400840c0050300c10034010781a01c80c600310031625170910003941c00591500014040d80c42c0d0504002030f1280d01803280c024400c0030f00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 303528516 1250 303527266 303527309
    0x7080c01140a02070b04120306170303090d030614210d0c020a0906030503030f10050d05010e0c010f05270a0f0e01050d1709040b060c010609110309031b030f040609 72
    0x8030346a50380d114244011760b4440d5194000000149013441f81495030b5110301041c8040310520107103035040824021a0344c2c0c80d040d0314203810305032107003117850505013400300a21040004203801d413850401502c66000302c40b41c159003507540c400011000c1e071031030056000105076980d2020301503641030b00913a5030000540d500c2402a084880328400a0010381062002c03425003a1100c584940000c0310306a1400303415203400005032907086114045401d40e42d54607400401c0718041c0041d0402c80d80900b042008101d200700040c04030722501c111112218031100a21080704480c2005280c0061b02403c10006140c45e401428601201400307450103c913404000010f00780740c101007046001e1741c400700c00c100300c4070301e1002501c80350440c100700c0d540141c5820a2a415464600c080e01d0104100b10010948078540351102003200c0b1131003007800e4001010001c01564820010440700c0301c812040c40680c103111422420740c1140030752881001580c000140c00600d1f2607200840000f60f4108280c440b1140e0030010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 303529766 1250 303528516 303528521
    0x10608061e01050d03050c03030708061c1203020a020313030b010303082811070f0602030a0b0d1e0203071701020415030902030d12090606150912030512070507080c01140a 75
    0x368150034242007000601440c201098041c0e0810300c01d003003150600c10106903650445e00308850703000005001004010041c03030101c40c10301c000340032407000000c181d43c20703100d031300c03264007450040c905054002500803180b80c0300700101c075800380301c009006010035268070b8505100042840240c0001d2b48000c0400d40000380455000f68008104880010950300d00d20200083c080d090350498114100380b01d520046840b10a0503450b291040d00d006980c1c0ca000c203a000201d40490103ca80181c1c184220480041c84d05080400325100b00000b0030350814451001074038041c820703040b00b5203500f11900c1c9204880300540190090350b280008007000083c5928084003110680e900c0030758581c1c000c140d00b0841703e00401e540141f400c001c02c0f0104003000d444e01c030441600e2140d88014941c188001040c40400c2e40001c0e6000600640119540d5080c86614000d015006c2d803941c6110202d60b03030020074495400303401201c038883d0f030040f03009841d1650092100e000f01075600740001d081c0d0514000940248032403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 303531016 1250 303529766 303529801
    0x4030819081311180a05010305190c05040e0102040b0f0901031808031803090a2601050106090b0306030114070309050105010e06031b13090c080705060f040b0c0c090901060806 77
    0x7561004101c4143c96254030351030081081c581141c1040c0141c001d407807114070224800d20100c040810554598a0b22500d0040c2d202e800f105060380c20b104d0703c400500c017040550301303d031811a0013127003c2d40300c05009802841103910440b80a03a00140a0168000d1480a4030196000741c90400c00013900302d40e0342c0c0010f0f00f0210000c0161004000048900c80160700300c0d81e400310f0481c2141e040c442c00c1d1001c2005002180c20002c1012a04040409404501e860301c034030703180e2a00024400307035140c20800341030020070340114080d112008c80081c295807000d50086049841105518109041c14540035000701584103080c1c4695003450300110f501c0b0b140103d00c50040d24083c0041820000b40c0c4100d000c000e901c17101041d880030a5031401510501e0500541c082c29015507681f40078030786807000350f5107842103642c081802501c090140388402e02c4c41c0030580301144c610710005665404045022810000c064505a0b80445c880041c40321103e0b05500540959407810115103040d112100c10700c8518204 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 303532266 1250 303531016 303531031
    0x1030804050904030306051908060a110307050706020d05072a050607050c07050310020c06070f0903060209010e040509010c110604020a090c090330050901080408090105040801020403081908 83
    0xc0004120a00305180595442802460b0004400da00e81002410f40c400740c4421036103459480b50248400c2000384400da0304100600810041006034004c4088103000050000e03043c0400801e8940c140100d940442d0442d080707002d4208094a003e580140049805400034405128410032104826221501e450384d915040b800a004a540f03102085130103622010407844140142400010591401c00040030083c4c00c200c4050f80761406c80407081c0c0f40560080c090000c00800712203541c8460f41140c10302c010f99811103c09640c2e41c0c81e03100143c505203640141c140d000f91410701001800c01040d8000309010045903039503a4151102c10203d40e40d00350942e006035100301d0f01a002c00c0500d40b04d81c4840c1e00410b6a042c01080c3c15941d1f00d900032a03440c411a0703803800b241c0384000103016050300320070044202d01e50b00300b03c0d044c815400300080240e00000c0c0028071040c0002004101a80220243c40042400f1802556900d489160190907034001d2040148141d03a559881810180101e01040c814040c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 303533516 1250 303532266 303532283
    0x100b070c03020f040e010216021207031110031b0f110703021305100b0d06050a050d03020a030305090f0f03040806060a03020348120d0203040506031807080a11090103 73
    0x1c0d5002c008021060303080381584181c1e540070041400304c082c0041c00c2002480000c0340062001c9005014040048158070032203508224414070000354200d20501081c03406480b09090498006001d43c02044407000103503420f030544840381c072140da114402a41005082c4e480c10741c0f45903003802e0581d5032020350000030b512100344041c802032010103074025540104405106002e0603a94095400194003022991485c1a15031301c0901c0f8605007149000300030542a00c040120082903200203440341100200141056240d0001c601044000c00c003080b858a100002d0b40d250b00c05a0a042e5901da100384a00f0341c1c075008070740004e0018502481c10780c003102d401402401d1109400b070000d02900c4400350220000c1b20b00095500002c3c09004244070000300a0045401801154820003104035840300130106142d000b4030300c1c6040d183c0d01206440856605039549038a9490324002c040301d06204200814a901c103003400000d19210015000341918000c0e000710403c108240140040701e5400d00001e4810314 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 303534766 1250 303533516 303533519
    0x106050702040b190b04090c050f090d05070803040b130b0403020a1502210409050f060a2112020c1e1f030b090702010f0c03150302150c0312100b070c 66
    0x101a042003150800007006901d1048039040b00c0c1003000f0a43d0810410000c001c54140100303c1f81d0311403241b045203113040c050b0030854145022a80d0303210b290380c01401400992221410880104601d1000c1d05c0298141c0f0780350707502ca296000c10342d08140c407211042002e4032000502300002c001241e040c4d039005089841042d0401d80c0b12030041c0354080c4100114030800340307141c0c110700805e400c0f0588640c9010450b41c0d6149040d08840c05e41f140902560b002c4201103041c815595120700c0c50008548050700300c80540c1c1c0a052480703140f0640b5980251910310b40d180c5070381840354007003812a950340044410042d440800982c100145000203649500151400c01180301d61124003100110860039180c040341c8842000041900c071181a568400540c1d110000b000d403854080c0a8061419154070b000c003c41042c482d080642c2042c1407001034095120305500e42031200c1c089084a44100000c1c08490342c0f81070b050700001401c0c208580301010007070b03400004030f025184403048030122500203040c8100035 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 303536016 1250 303534766 303534769
    0x605180606130b03130b060102010c080f13140604060510030302030f130302060a020129091503010905030a0f0e0915040506011e0c02040e01050702070e0702280c0902030106050702 79
    0x40d8030440c0e019407140c480c900c0c0003c0d544400c1d4001e51051074070100f0302c0c00088240c548903440da08050b0015066905040310303441c1590f44030f442e203507001040c03680c0c0300e0f82c0da103400060020340c094081010f450303400c1042c182001403d00181302401140314080c204146c4d580e040d20545c5d9804680402001030b0070400038510102085d01c00f07002c0340e00742142d414492664a82c0010751552042c16407801507510355014500704985d0340e1003060890648041000c611002d6000a00c0705600100700c8000011a800846240d480943c012584290301108a956545209001405880c1d14600440005204c0c1c21101d040d8141402d003580503000103034010a140303d03440b040001810006252604100408100d40800c0390f1400d546264030803140c50b42042000c590060205a44610740744001c1c030f0f030506e01032121166001072076070202c0340c4c64040c4600315200d00000703d06011003030060baa010b0103501c1c400140d02a1040c00111103610807a034180529607140903200c00c2e030000b44a0000496424803e24015 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 303537266 1250 303536016 303536029
    0x150c14030901181202011109010e0d111801030512181c050102030a060501020f0c010516080f0f0901110f0c012d0503010519030809040929090106051806 67
    0x12071000c000100d2410341654011404840405094980410f6188001e141540a110b00240c001035811060314100344280040c0c00001c1e80c003420750090000e0040348050082c00c01c4c40c0c1103100801007000b49010b0b03400004002c00c007000e003c1074500740600011282e45004400845c0c0b00241d4584a0704070580c070000400c0820050b120201d1013408228807044005a000e2000318811240c9000020b1414100b86c00285801500d501300010340d400b00703200e40f8841e84c00c801034441d00010400503095542c8a483c1c615103501a0f0010421640f201003a0f05508440c1200688000d441c2aa65087c140300803144840d90340c0034011107403256400c000c8800c0b1300d551103000c80849000384031248406101d105035919210080181940e030000b80d001c00144500d2034418215000f12500d880841c40c020700f1034540001c0d9124045400340704070358030a1a8810400751040418030130300c409a00e80400c1d07000d034a8035800030781d003180c2c070700920352809001007031514020030400302824800d00501c02540c1c0d41302c01d1020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 303538516 1250 303537266 303537271
    0x9090305160b010609142407290618010b0a0203090303030f09160605030a09060e0f010504020a09020c030d09020a030b0106050903060c040e041704080712150c1403 72
    0x1001010861104401e01210081081074407a0060922940c5040c000a00080584e0804070080c008040c00715881d983d081d9032003880440c410b03000b20103041c8101260100303109001c030080ca00210050428a0380300c000e0075008a52501d9860700249581e12410804960100b99400261007922401442210003902c081e10004885004482c50310f068040002d145130400c0310480f8120b403410301001030812081c000700200e00d40b25003130b28400604007030014082d400002c0038850a180d40e03c1207081407201c03940140e1500110b520613240126040302c0228042c103c111410390240d400d01c0300020354a80584200c070150410b01010b181800d460243d0f51000d007001c480b041e64000e0001c20040080754042d4111030007000031b612a503540e201500305042c00c080000700b1391409100107000c02c0095000080541d9031081d0302c10882c000109c41503140181c5030041d6008541d0b1440b400e600070903400c009011800e242400340040c90522070700c0c580c407e02510916a6144005607165084d100f10030301c000040c54 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 303539766 1250 303538516 303538523
    0x5010f06080d111e01060f05030c10030509030d050a2a050702010302030406090515040615030b07080402010c0b01260c030a03080a0b041b170907050607080409020c1f060f0909 77
    0x40f144400840b18800c04501c88010784016592218101300118070051fa0b4001040b0580161420360f90740c5d0000380c034411906144034180740e02c610000c0d130340700d80610860710101041c99040008d07017031020644004001c11079003070034203269000c4c900c02c04054079510752415002c00d42e1030354904212a80110065000a8021107e590f00d650301140010414480d005208600044030003084c941030412805880321342d1810300d04002c10500a00200d42c20901441d0f200010b814107078429222480122101415200d000d801100000000b2980303a20424078009004401d12000503401e050382030290300c074150703203e04640c03541c8980c1300500006c0c042c0c400640c1c80b242d05413001900b241e415001c0307410740b07d10180200c04d007101c401c0310502068020301d921480d01189425403545260406515079100d00324043d0b40e2090700003040b6282085000340459002c5c000080e4255215000003908580e034207070110421002c00b0300120100071081d258410801102d40e401070310800e403440c051001005100c1c41c40141d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 303541016 1250 303539766 303539773
    0x100f0614041d041707021503090a02030a0c062309150d0e030403020103060e0402010c1416031a09060c04090c0c05030a0c060b150304082a060405010f06080d11 70
    0xc8550704a50341200c44407102c81050302d14907040c80c002024010b0038074500d080e20381c00e004d010050784415140c407002c1d044020403d9641d8803590002850a03600d110000c0d807522801e007103401002407403c05441200d11031f4842c02544410b491842007511803102c114001c0000c03d102c5211f69103004140c04410b071000e200c0c40340c9480020128282995070942142810340d00000c1c08000310350f41441404000e0420f404030fa01c2c3c1d4101940001c01800c022100600100e40000b4101d440034000c1c010755107001035110105440960741d25040e00706e0410941d0740841201c01800054640b500400c920384079090b01200c4501d010304092002008241200c0020100041c007146040000c80810003000302d2001d5480c0e890b8080c804c0d2130300c4825582c0c04014940542c44440d00c1994005044050701d8005030704c006040e232601504406044d07170b060301c4505200c003480b49000a0580030300c0841c1840c0228042d40092014071203030180c41c0140da9803845444050fa01c08400959154031420b461031f414486802603 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 303542266 1250 303541016 303541019
    0x4706120a0c0e01030b030327030102181207050d030f050d060b070606150203091c02030114041b060503010312140c03040806060a0b19030e1209030105100f061404 71
    0x4240108440c0c0c08403055541403000e8015801000d011500c010903e070502c0440a0040443c0c2c8034051300318502c8050070b01a1036108280c10114449100c0c1030090003c42d2500c8000140d45403046903440428000e07140404691805000864120240e0304054030a46030b038000c030354003200c400d5050100a81005014003040c40d5100f55802480020201d80301203d0b218901c2d070801504039140d650000401c510031075002c0145c140c01005813100d155044a901c80b0030300c1c02c0700c01003040f0010800001d602d54030b490000980001c16041d82402503007c0c090004585060095405804080c0e01488021800510042001800301c1d00f400f603420545190410130500b42c6ca08294050b000850001c60030b80002c00d080c400201c040000d41d40c44503007221880d8071b003403030880d8040340c0344101d0142004e0844514280c5004d43c0c069000ba240d44049102140c080070a0501054003c1d0414203440c0e1082d42440049501ca01d07140b601c213415a07903100240480d1628000c0c003566540300f14090300310900301c280700 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 303543516 1250 303542266 303542287
    0x51507120203130f0303080a060806130819170903040b0702091f030804060f030621030903081c0c08090c060d0905060f0a0c020601140f224706 63
    0x31900002e00c0120b80c11691303541145000791040a0090096903210b1800302d00300701c6001c000454076003141c1103001c044049070305414000d115214404251540038894161000419403001c0d58800c01000700702c03250710b140c84e4800119182c1c8124895105102014031070007016251800d41c080d0040d03103900ca0203282c0f0b880d4250940c20320315581c2c1305a440700340104040041580210f901201c140b5945010012103060071000140409ca1101c07a00c045440d12801104050145500d10003a41d000010700d503c1e003071000c04040c40d0300c555400c907640850400d5003002400340941c405c20b02070700e0b108010345004181041803250940002c001c880c004c1d5120403003000031402c14441c0f0740c051001c1962245007460081d441d001950107024440342158044001000820038090f04510107a204581d60b0802c20010742c0050030801c0c4800103543c3d01107150b0301c030954514140e44485018083c0d4800c02607000204e0441c600310110350410841502c080c0c0022440f40ca02c46508601504030080110b8208808502c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 303544766 1250 303543516 303543547
    0x80d0203061f0903020f0f1c05030c030d0b010e040903020a020d08091c140601030c0303050c16081e07050d080c1203180606100c14010e030c070f051507120203 70
    0x801042c04a90b88050900650900030b1450224901c141c0f040e80c2e80103489004610790300b41030415400f0844440c0e20a00401c1818811070304006050001c4907103d0004035a104010615122414003103481c03116001914241030080ca400d694040d005070101e031144d5000e22107150035400c8100c2d180c500410810300d05a44012255500718102035142c21414000d1409448154407608903481ca0703404480100001810603031200180c03681442c1041d245c4071413070401d51802c0d0541e0400291762800e1a80480d118200254000c0010529000401d422480040507502c80303070a401380300d03000a2560100707004580c3c41d00090849442000486541180e40d00d1110030725002036948c005d000490380221840d100e030810081d50403100031500d002226a80d807201a1058403560002845514683d00e2101c2079242035020005241890003030f01e40c0c51402c3c5d1005178032071503a8042c106100110782004602401e0180144070000300383c1d00002d2a042c05d41e107480e180612500c08d43c408510081140700e04008080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 303546016 1250 303544766 303544819
    0x1403011e05090a14010b0c07180e1506030d080f070c1a0705070506090f030306010c1119090e1f09020a18020706050f0f0a1d010203040c0609080307080d020306 70
    0x852000582c4c840c0401450300084040e401078003075080c00d0202001c40c40001c100b42c0210782c26500a1401c058000715604007404074a03260a40341e02401071809070400b6610111031240000303d095458008a04c0d00a90301028161081d141e8004c41d4400100414015441940d049000d1750001000c5010f403c4080340200c411140704000460101da07013400c0010030400103400058500c007400004408046541c0e9070300009010504001c01d1410041c10f00c103444442601e81072020f09410150a0302c6005a10948801d1091000d12440d02004d0b002050f00892000b070015480147c8800640d803082101000d09407a04080c2d900c00c0d02600c00081050f03805030a001030301101500541c40310071600b0a00211500100311001008840d010004142920710659504c5040c1c001c0c00140d6550041c80b03601ea510098641041540c8004184820321400d24034400c00c40d80d8540d038462400d5201e008090300c03400388444c01400ca135800d22546d560300c070b1a60040c651000000d490580303401d1141342c7c842c8240154 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 303547266 1250 303546016 303546031
    0x112020c0115080705010504030305180a05030a050c010f020c090c0d0b062d070f12050c0d020a2d12050f040b030a1104081207050c09041208071403011e0509 69
    0x5a240800103c5800d015240c000c001c00d09220b4142451601e01500e00d100ea41c40c449440ea05808082800b56035641c0707090050075021303084800401c95842c1070b0f0f52340c9031075810282c04116240381d40c44505200244035144800094a0300c0b203e5242d0b0250300c80d564001c00c10360044c2a403200140c0c0400d407107400142c02540030200502c4182d041c1003444101c4902e9180244a1003541000f1140100700c0381002107000302c2c0e100380d01412200c05c081c01190300e4050f4101c41c4615000d0b060191800a0b8001044280f02d8015691040c400300a405040000b03000241c0d60030002e40294817400103c0c00d038043c0d03400b04000c6403c00c545040e600240f101000c1e0310a0700008545a404000d002105415109024840c40000a100d24040c1044049070340c0d014180c50640300000300180b12303010014107010f504031851024041c0e401c1c6090903d4a01d1740741500c1e50404001880c02ca000500f103d02c54011150200c0100300d0061569003002030841e2040c151181e118a001116000007a56848801a89200724903 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 303548516 1250 303547266 303547301
    0x51018020c0d0f080c04050a120f0b0c07020406080606090c0c0703050613110102210d0f02161a0705090f061b100b01020307120806010c050105130311030a0e0112020c01 74
    0x240031001800f0700d10040e124110170b12042c007060080d5140c8600c08000d507545020480c0100c40d01e40782c10480c44842c218001d25281c10303601808042e110607000703402032a208440600c080d90b101c3c1c4110340d40d131104880aa03400781e02c280104540426000040000e00345010642d0a0f05440351203140c5030440036a1415110a1013408060501268000781d0b00c202c0780900c05007004903509030b258101d10100e0400b07260300100015626140c08a1903100902c001103005003903490b88140071042c4c8803075400c9c2c002070f11212403400c0100700c84050110403610681040e11268109000e800c10f0240820a503901ca54000704100813503076001400c103078451001c20b0b9120003041320111000b990015500c0c4c400c42d0506551003030240100240c0390f1000354042540c1890b2070100380d034035030004840c4070341c10709000f0341194600010712103001c12104102c811180240c88903540b4a6120441c05e41c0d9101e455101400220380d509800141d62180f0000b0641c190b110002504044103502042c1c01c503806004028400714 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 303549766 1250 303548516 303548537
    0x302060c1c0e09090d021510180c17040807060b0a0b07110f0303040602060109150314100c1418010e0a0905010302100f020d030902030a0b13060b04051018020c0d 71
    0x2c3d0151190b54004140005044000d1200001a40d50b50b039024000188031900000a8000020316009100600b882419240d4603410914407100030b0411136248000070302d9070002c0140007040120814011940072a4081c90021140c41d100010001c0c080815405004120001010900900a0700703070390380680c946200a01c00721003003061401495081500a030000d0200300142d0b03802042c00c13411a500c6200120301e2440b40b07066040d407001036802c001c101c0d454103804001c0355003001a21840391003000c2c2c0c0170018031320340c400c080c1e41d41c180f4019001100700d800c20a4007940c0106910b4840e07080010306040201d001c8074000200480f41b10703045088400d5894004009510700508400f03450780c0d060130019202c1c002044000e49a0389031550040c14907803990b998a0840d1000c21240070520b0300852410b585003880034481d0140d20410109460070340c03e180c0e502c8030070300e0144100c80c0500d09070810b1107a1185001c41c80f440d5a0480c000c1100072a40c20300c51440206828049000042003e6640d0000319 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 303551016 1250 303549766 303549769
    0xf0204030b063a2901082122030606080a0303050f0c070f050a1208070f020114010501030c03060807030c0510080106021207020d2a05120303010302060c1c0e 69
    0x145844a040c11101800340940c2074036202c2c50365414100101180d0400700c3d800d042103020f1812500307544ca5182c102d0700c1c206004503505948039050311040401c1d1600408800100b80221480007c0480d0303145c410801079200c400c810200a08000c07901310b5050b9041e80e07a072240001c48031981e024400a411603501042015890701c60305078003603000b00468900d41010081050070340115000181023200c1c211101d03042c171008201d01d805181c3e100340c2030308040701d8684c001041d90500b41c2d00c500200d00d1402d02400c1c04c03030042c080e80c003040d0268904040e85038030b8040110090b058070801c02c0103066941c1008540600140704010103540598506018240707000280040c81c00b01403100c60030040700000501401d58040f40301640c04120100f0640c8030707602400000c0c0100c80c1c0d184000c00c0d000d400c00712010540d8403918004c0d0440c03030b11800c40342c0c81075131101442060400c83d517950903a600100010300c010f04d440005040c0c10352500e811074440c09002916113034405050211030011895a000480c40b6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 303552266 1250 303551016 303551029
    0x302010b12071d190b060409020c03121e04080a140c030a0206010f0b040e04031e0201060807061805090903130905040b0610050d0b010513030305030a050f0906010314010f0204030b06 80
    0x402c5032030a0f200c03200d458070146141d250380760f520040201c5a1180c1280946554080a94000e4040000d08558072039500c03219035034a0380105007200e80799820500003490313040c0f5040003c026040c0381c04124a950303150381c0c60580d5580400840403e100701702c00143d0310b03104144007800969a90030b006581c6c03003c130f90750041d1401d80164000749051100a4080c441500c43c0c405450444150807003011842d20786260940e5094010100c601031250503d4a140810394150031403070031240b190065074581a00c0744030440b580c240100740c2d02c400c403a602408201e103090285406500c07164000c00d483c103046031500032071b48002c5130394003498015490342d09000030b10030308a20317071a0000c0c0c0c200e4094548995a0398068980e00401c594005803d54030041400a130f405141114030041ca1081a258082c2c2c076131034050701540045d10a005110702d0003001413103403e4a01c136014060107604006000a83c61a60350751f80c20303024079020305403e540b120449220a03c0c20b0028202540c880c40d000c1d00780d0310b424410f05c006e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 303553516 1250 303552266 303552299
    0x1008030d05010905100501120b030304030f05010b131b0e0f0a06020d080702010603030c0602030a06050a0f08100207020102060f040512030709050301140c03071b020a0b07020915060d090302010b1207 87
    0x1714000c0c000070801ca02c0c3e030030030b081403590100c0100c08182c0001c00c2e40003904600031940060902c4080040441c100720041d807000307071040411110343c11100c2802e0359006c102c901800414204086400d800410140038411900642c10f000346020030004460700030412408050740600c0242e40603030741d109100760f00400003da20000e58802084640e03c1e6417001040c0d2000502d000e8045540000800d41080040e04a20b01410000c0c000c0c0903641c4c0d072401040c00742d25040c811410107000c0c480780c0000307507640d90085401d6507405900030004d5803185000140141005030045030144540e121414149030100e01541c828a20341c1c0790710184504d44030601d400e41e07040100c401c20031004001040481d05800c019030350440184e00c4d02c00c2c030050031300c0300b5041241452100a54429014200040c810118400030034820f0310a0b0744032045130326402e0484107d81100e1500d5903100800303000c54025942039a02601945000f0310001c100e00c40c0c02800300300c01c480c400700103103020f400c101000c1c0a01c2d03212100488 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 303554766 1250 303553516 303553531
    0x201090209070c030210020f07060606090f09140105090c0d09051605010c12181208030a0b03030705280204050f010503250b0a0314010909050709051e1008030d05010905 74
    0x141c0f24580c90398001c0d100d4024442e1070340081d0b40401c80b076140c01c620000341d8210541c0144e041114a88800c8080c24415652040300c0400310903c20101c0c041515004072441600c61048016899090004211491200801d40d80555005122a90213031041c0d0007400740b00c50003070014200d80790307200c0501c036020141070700204e05102d41764559034005001c0c82411002413210b0328021100520320340070003823050040d6004076401442c215848040c801101c005500a41002c9004c010002e907003000d050f203a014240703019105400101102e5114450140b000783d101c001c1024442d80340020f98002401ca0f44140c8008403c0c1802070018440e80c1810481c201c0030148420b2000307421071503203044500d8113107140142c00300ba00d4041098070a85020703802502100b0f0786882c240205607100d940240085c0700c0c0030070035181c9100740d400009582e5030034854680944c4035400b40d274800e211102c100303080b00d800c0170389000c801c04142c001c0003c0302401070000e45200f61510301c01144c213525003903105098030009808030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 303556016 1250 303554766 303554777
    0xe030f0d1e090b180c10020609070915140f0402030a090b0705040f0b09040609020301080a170a0c030c1704060314060f1f1b03050403052a0f1f020109020907 69
    0x194007241c0800d07506903000320303804141c103600d104d8001140c0c2002007100071540c0002050030340303030391035500494440c3c0310385a5241150034240da83e000d154140c400034644c2600210f05190180142c0c0d030700440c0034079004030103804011586060300c042800c81c1e200312094130310b0541d919021070800091900040d00070dc000d02d0070601301800c21442d0b401c1c0d54900d103d942c2d440c3c0000240c03c100b9860300d4211200034040d4540c01c544031369440e600a6120071391000c0444025103401100c0c2e008001007805e41d10f00710200c0c3d840340130340892a60165944041030034241c0380c15a8941c2c40501040ba018000d00240402c0d5502155054030203000c10109000913041e03c1c452505403110010b217484445c844084a0400c1c5c003e40b5850590800a07104c880803440400b582040421b182d07401d054106004108491241c8102c82010600c100500d0710602030901d0745615203000e45001440d803810a002c110784085c000c1008020021500ca0b10380d4401040612002503510f64003680c055140800803540c0c00196030400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 303557266 1250 303556016 303556031
    0x308032217180a03020a06050a021e16060f050301050907020c030a06021c05010317070f060501153f0b04050406051f080d1d120a0b01090b0d060e030f0d1e 68
    0x41030351b109809a40700b00b20001c2600c80c402403080244503805100c4950341d04000c0c03610007200307403240c00600c2801c4482c211b0a2000426a1141c8074070b810000c0b813039803014196401d0400700401c0d905c02070800000c620880c00c03c2003555405200b0b03079a031244143c40060b680d14200340c541e511094549120a00c4601c0c102c0100f001c030300300d00044848013610388a15660303001280341410340c80605640241507646804004074a01110012180e0506555245c010488580004072000c01c5510307041078110341c00480203040e01d2036518040540f810040000440c01c41034510100d4101c55040350140c80031f07030300d44007031042c1c040c6072018980007103141ca44813000160400c000d056640e074191210354104078411000d0301d400300105c46080403800303005084040c44a0815640e581e103a21189064038044891000019204480e00c02d82580c40d4000e0b00c0d448035100d203500c50354020460041105030074002001550021302c00c1f0300c0207099220025400140300d5600c000841c031142c4400b1200b0340751031720701460b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 303558516 1250 303557266 303557269
    0x30b0d0206070213060815060f0901060f0e01120f0203010f05090c040e190c03050601030e07140d14120711040902060d09020d0215070605100308032217180a0302 71
    0x111004a601610b04c445110700a0030540000d09413584511400e0180107a0302a0315190108014003d10003112802d07076007041c9200b04210305000b840b41d140810603100145141500669075003010a4050401860180781c03180300748140d4841c2540620100d0740000148112041e82151030050401034842c01407518103c04064440e110b00c0c021503003e0401040015126040074030000042224640140a070784d0490f040680900350681d003603404a41040342c0d510004500142c4071003111810120040950359200500481150745007003a05c5240b460a8880c1d0144030400c07601c90000b4940b0500d9a58440710f00b03000c04422030800e000d9125608052060000da0341d1003007034a40c0c1103080315001410070200d07c00241007071940340340290011588452801c1400010000d440c0c003500070301c0709018a031b584150300c0301a00640e0200404103c030030300c0818200001000706040034030388280e011505151680340c2c1d602c0815284250500c555002828840d0f511411803028866a415584425004d04690 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 303559766 1250 303558516 303558529
    0x405090a0b010f0e0711030720040509010e0c0616060e1e161a070525080601030b07050a140412031409100e0a05060c070e0c030906070c030c081801030b0d02 69
    0xc0026081102c004801209040103104890b0290f0703100011082c040c0c1070603100707503c0c042e140b2705482c4924039240000d0b10140040c000c8581d107560030000f1f42904882d16003042050340280c8040d0b118000384903d14400900c152040b264034010300360040170414a040717900301860362094558005030704004100c42c0b50500da614078009803468141c82448600d81c81c0e10034070150041d01c0004d0250711901080502e540d45200750030180c00305503080410701c40d8a03041419581c260a02c40104155580320000e81c0352131161010340806601854414003414070f20100780c030710303410507040b16400c20301da40f0301346003055040503e18540d5120881c1c05402c05015100180302c2c15810582d10080c070010a0055159540f604144409401c005103200d031a034600c1e010303052b652003080c0a86008141b030710b00440c4915105409581c402d0176888014803c950b200b040403140000c03016011001e010707900e0401c0c00000e0000014060961806014615242105000500f52442645058021100248044090380381c45 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 303561016 1250 303559766 303559771
    0xa082b0c02010806120d0c020f01020d0c020d060204030b071218051c110304060203040f090b060708070f020d0605070f05040f09020f0c0f03030106030606030501051c050a020405090a0b010f0e 84
    0x2400c0c50040c940d204001700d001030b022103182440e18090b120281c0c11a03a049100e00d94051300940e01da00407400403200691b61f50f40c940002c400484c0042090100500d480f5480701d0340c1502c152000342c241079496486107441c00040d503084008c07890750711b2142994042441610a00005c0038903403a6a485203482e41c60300e510040442d80c1241c1c0f04109039005c403a0052003500c0d0a14500030850303640b2a642c6500a44980141c0241d81c41c3d600700c201d00184880345c40c000e100488100034402454010341d0364407007038140d024810850b507602c4d00e04200000740c3d5494181d031403482d0041c1804101031412007030050180c00072000c5103051240c01d00040c094044102d41800c1903800c84d40b00103035100e002d5500c3c02d00d980503000100c5500d126940c0300c0b40c050380001c005103040303d105442c140b0401c0d071130300300a40c107592090151941003081c5d40c03202a04445d400304c1c113605071400b510a45076403002640104042c1c46c0201c540d9103003070707122189400401008c0b4907518014240685680004e0b41080c00d52a48c58001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 303562266 1250 303561016 303561019
    0x50a0b2e060c030e100c0b0a0204051c0507271404030806010507020f090c0406081614091903080406091d0f0705130305010c14091305150a082b0c02 65
    0x8410070008060190325003100003940146041c0345040c1c0300381700424021101e00c0c2140c0000840340816041d60303250003901e09503000203040e0840440100101d50b8000b03644902503945100e40320002a629401c038890325030340c001410301c0400d210241e01408050f02d0f0806100740d044070444c001c002c0401d5202a00e56080764007441c1c810764402c1c0500019160b41104007205501c50b0000c0309221042c6104bc004100700d0f0381a80707802d1a0380c2d5408603082810708240c1c2c1c101001c01e00742c1c150101034810b80300041c59800c8009014111124104059550034250398100315094000001d0503c0219001480c0380014042c5007035017195459403051000d0001d5001d08010210720740c030070108000c107000d0f1050341c00210402d4544603240d40c0e6070600901904000031300c0c4003c03c022900220080080504031450703031401a109400305100000520028903004100c40700341d0344c4403421002244e44203280390004002e03040041526490410400c107483c154442d03400a2080303c203e404000c0360304400e01004d40c0e0b40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 303563516 1250 303562266 303562277
    0x1b01020a0317180f06040317090307081e0309070f0b070f2303030f0a060501111b040b0409050708010609051608041505070c030e0a1809060603050a0b2e06 68
    0x151484140e40303401c00030f0394148541c0130754190450007030000250503100d2400b0343e41e28413600e0201e4240ba04d040c44296400381031904200541d0b000302d2002001803241001c004511160345140c0c0c09108080d42094680101942004804000300f01d001030020340078112600100b803504000da51450003420241d14018004c6144507036516284000800b4110841581e0040da81d4902e8010700c1d004a002c2d0445e4900c11091030001c1c0483c0fa5403103450100340003030151000f41900d10104075180080031100c1c070700d641c0c0582c90b00d40c285c1e82d5031101d00425540e1132084004050350b50800b039411f82524210342204515901e00380403c00f03d5414900050401c00f000d09240469483d1802e06400c5400c0718420010f0840c10003007806501c0d40d000000c0418280a80e48480016181da0208013600c020f611520303200c4190b2582d841c012011903442482031a2080500082c40c070750340da40740d80c00c1208040068802d0b003d040201305d404810501407000301b20809420102042844410650b91a094040c00c401c121 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 303564766 1250 303563516 303563521
    0xa0606090501030908131d010801020f03042307061d0d03050702010f032003010503010507030e06010911070204050106030e0d020109030816120509010b0411070b040f020d12021b01020a0317 83
    0x9004802c452010104840341c1c0305980e19802201f1541020200200c00f005510f400020031403c18030030340e64542644032030a85562129150301180e080c8602910040300e116441c1070070b402c00c042110030000c01603512101c120a003940f00206040910903403c0d8000c100425003040060740c81000c0f1b07000b039542403c00c2c0131208030300d040032401461000949812030494001c840c20110188024604944044009000072b648042c8218280c40800a21141036404100103005410b9540c0003d03404940c0b998810303003014540d400060682c0c80031f81c0404003003507944908030907001c000d010b20001148180001d0000a00b43c2e50001d100c00802001118000c1c4152940e002c0c542c401d10050a90b2035184209001e103050000c28603000b003401d00207a42c462864001038003031240c5100e0542c0c000d207070004442c3e0b12582d1592140345081c80c824008036400740301600c40c41c00040b801c00c1d5442e0308041d658020401400243c00c904c03180f1110001450540d48462288070001e540841d05a681d2410710b4401c94964 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 303566016 1250 303564766 303564773
    0x1080303070311130f091a010806060901020c03100209040b0d0312020a030b06070c05031b03060118020702060304060608120418090602090a080619060303170606040f0608060102060a06060905010309 87
    0x107009000040d013034a14050320018000080810f00401e0307480790710082003140180ea50080b5803408401401c0d0104451400080e01442e120002d46036045060054455400c0b014000a00b052456040c0884603640414003102d036042c1071141404100c8250340c51481c60180c1d0b1406003a080000740c5a003101034002500003443c034826084000c0d10900070b13103025200c0e8140c1c5421886004c1c640143c500034400d5602c28000b41e80c4009101c07800210140180030715034280380c01020740f001c00040b03014a140c0c0800402c030050712610000c600c12802030300d00141d61402c040420b81880c00041044855107800d0000340000c00c0711210f030925107002d6481c00203101141d442c00c03601900541e12415884141801c002a0504011604520456944040c80d4403103a00c2e15003007044501d2400b0250004140038800c22194204544036600a4002403000e82003554a182500c203001c0d107500f00305c000898040a03c40da03942c040000640051a10a00f40610303810560000c2c0308200504c00c1c1410142c5941803441032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 303567266 1250 303566016 303566051
    0xb0706050a0605065205120f041404021c20030c0d050c120105100903080f04031a04030e150409020f09130605090a020f09210d08010803030703 63
    0x400020340304544441c0801c005d011000c00a0a680801d0341c2d0701c0840f80340003181e84610380c40409281164030000c10201400320312655080d070040340c0718401c408106010030701078405030030001e5801c00c0c16981d0300d08140824050450030100d0078001d6005004841c894442c541e000c80210079203100c0000c0c0010a0101d4840d00f021070208000658070000034003000030511002444400045101441107448018440c2141d219a80d2049481c050b8900180035514056100c2042200e10380780100700320340c0701e4030b8400c441e503c82d40445140110015003001040380207030f80d10303008000c6552142c00d80e1426490107005202891045449418400050a4507040030410b0701e000c0d0150240031074680a004070182c402e42d00540101d40304904464980348a646c26000304010f90758050180031103600d032200e401d40a90804101d110000030309100c004070940728958088a0103e824030f014030244403440d070700e81c2401c0074502c03010100003c000052100b6000001140e4002d0242d240001e035001404540001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 303568516 1250 303567266 303567269
    0xe0103110405070219030f11060412032004080c01030b12060411040e06010e0106090e010312080606090d03030b090a0207050a02060d0e06090c03063402010f090b0417040b0706050a06 80
    0x440621840c1205d06056110f6004006500c2d551144a203412071855010303505e0604890040100b2130300810380941921a030880c4410b0000c1142140c90303000f003d200026240c00541182c1d40700e5003e00d0b20b582e555030b810300652400301c40503601506580040003110340c940340000d00c0601003003011400208584c40e25404200f0225000040e03d503e942c503214118040c00c000c2c404d031000603860000c0450132940b030992050480c3d03402812101d181605480c01c0c0c41c580b50003007296a001c030703003404400e041d501c03a074001d80419440b1ba600003411a00c200204800340c1d5028012070b1100d841404404006000040c403229000d40445480d61a42d141c0e4903030308050b0045036120711850050000307004085a0019040c2c1450400f2030030344020740d50b010b010302c100741e02521180c01d9545040780c81c126040c0c00080c42607110700c5a480080342c00d607001a0a00140c03110104c007141d60401000411050203806654404690314000e5000c0c6014906400b5040d41d00811201900d41aa944013285060345680d00c00e80 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 303569766 1250 303568516 303568543
    0x308090d0510060f18450b0906090c010f03090c0302030115060e04021806070309090c0e0307050a05090f1f0e090606030a021011120c0a020a0e01031104050702 70
    0x40543c48074504e91800202d4440c42c1212588110300b004108150700a40f14040342200d0340781d4002c42e00c0da51203100655402d030440e40e044510250345220441da140002281d0b40202030050341c50074003601c3c030b81c0341206c0102013012036007054514810b640c0c2d1080b00c14022a8152801180c4000c16040200a00c030540d440290300d0740c600413001d40d02008011240b81100c0c00f41d15121211600c1d2070511080c0d11465122945480d226030354100c2500e050000341c01001d00914094410030344070030b442402c6030002d403040804a81382000725842c1e0b1804111181c06040181d5a4158083c0b410000c40c5070504050103a014164011f800100301c02c100d52840500c0d0700c1038203000798000303070348003c800300d90710064131020024068040003071514140000c8800c115540030f000202000a00031041301c2060000024103464014860030b41c100d00c6215000d8802d0000345406001c056015104004c1401c0e629840321580101003801000490080c1d590748a00c2c0d0703810b41d8041881da0f55034500300d081048413030005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 303571016 1250 303569766 303569771
    0x1140112020d0504260904090f05010e160501111203180a08031512060a050901060f1d0106020706080403031808030a140108010228110a0501090c0e010308090d0510 72
    0x11038105095800c040d010798050203058407200d81d1900c8100e541070310b03501c210030058420091421b036070134580d20000300e030360181d1075901c4030b03000f01d50b2040d0940380c19103000c1c3c10591004000108504002034240010720342400c141e05002201c8650944940707400304c0c000041e40d800b00005054941c404c43c1c000604145400303403060581c1626001e40c45e0307002070b646044068088040000c0d14200500081c08070200b2100808040ea00d034146e50b805000010300f10495952180400981e00101c0c22040000d00004e184125800c1c1d10708095003001d89050f4461000c40d404440100641500304100c40d03000342c0c2503e008038140c034607042810b821124401c4010043c4000008220311f2000640c800b10800004420500e43c07a6a608a0b2134244e0161880c04510102c840c0000b114100100c2c0400200b2400c0d400e000c10003250300840c0038141751030720380705442c6a5106c00d544d000f000060564a0090b29102c50400d41c90350658551b114540280c07607003140200e031107a22000c1400400c00040caa84003500c00d00303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 303572266 1250 303571016 303571027
    0x90e03120630030a03150315092303030f0601030606080408030c04170f010f020414190b0c03280c03120e0d020c03060609070525020301020f0307021b03060114011202 73
    0x15141c0d0b9a00200480b40082c0c941403401d02070070f501044000c2182d408c1074042c94900707a030356452001008046403c68040350480301c0c0101000008c4da814256030b580b00040c540764940504114101040206014100351410700e05010792070700220342c1e1341c1041e0005056034031f81d520341e6146051403007185c000ca01c002c500d4410089100f20005520341504c0e00301d40007404035060300300c814802d85c000c0b4040c007100b0180c160704001890400410382a190220051103982e021303a50707000208698408040b8441c5a0000a80c4407084c003072032135240c1c1001000510112500d00603c10080c46680c10b501c00404000030788d00142e600050a03003100803400064016039625601540002c0e68880401200c94000d003d00000a0300d10302c1d0803244144231701c2480c4c80c3c051a000c201d51651140b40d80380c0c1d481c0150069014103410168400348060401039860028140c2c0d41e0608200180c507060054400c12544d80340c001141142c1d440104840d0304544100074200c040c0703107084005071920901702c0f2000d0241840802d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 303573516 1250 303572266 303572359
    0x3080c07080d05180a051207060f0509010b01300b12060916091103061909090605040b09060402010f2003070c1409090d0c08090415090e031206 63
    0x400c0d405007140b060000d04c03890b010800951240a00d030809000c6410101c100070000401000070804188181400600d5410010068049400036140e0305110383d52050702c0507103940c10004025494448500c0c1c2c40c0381c1c1c205081da40021130f0411128040300c503150010300519403105589040f0124170341094560782e1030080c0040d5950740c0010203907c0060140700d4000741060705442020815903814082c0e62035980c2c0e0341c06024144401840c0200111550940021500003a100c0d01040c644107400c045018207182c1045101e080001d402140326030003010611006030381003944802c5508d181d0070400741c4aa2846c4003080c1003910140c4203480c50000103500303801c0045c14650b480c2950040841c140f0154100010f01400380070480f840d03800c5500015504401d10300413400004224424850a071408a0f00c402240944030512601440200268014072055916000f060f20f2643c3c0c450007181851010700e010000c1c050050301c9a03003c0c00803040d40640b0361b40808042d01e4205425012a00c12034003040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 303574766 1250 303573516 303573521
    0x2041b030e1006030c030b1b0f0c010b040501270b0406091515080c0309010f02070305070203010f0c0c110a0e041a060f460306141303080c07080d 64
    0x116100e0381e60182d0108421000710510030f00c0d003940e030011004800b45040d90b840140041c000360080c0304840c4030b6003124034148080700041c100d80360746003201511215040d8550382035800c0003c880d41700340d0804005100524501c02165448104003a05040803070278158048000c1008001c080d4100d0709255000c80c8030100c40d040311800011001c0065000e65840e0358a00c804038017400f09400144100b00820b02c4585090042c580001e802c0000242d9000316010810490307205010450110b800441d0b4403003503180a22403042040e1a0410070304c60200718503001002501d9440d0002e005030842658030843c0d886051184010b4820743c0d5407401d00e404c1509140124000c01c040100e401c2418900040550a00446d00048076030080c09100f01c2e4030042e4000242d440807400d0071440031180400358043d058a05030540c5445042c0380c1c003400c0090443c20f010040c2e403201208100501160002c1c00442040481844822601458264600d40301d8400078000741c4146540903009480110324003000030f40c180d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 303576016 1250 303574766 303574781
    0x70c1a070507020a1424161202100c1b0c030605040c0e0a060302060a030f15150e03030c070b0a0c060509070f06020a0515100e0103060509010b12030301060c02041b03 73
    0x1c0f04d02d00041c9030303518080300b0720141e00c19a05030081c1c4280d2200649403501a0040285041107010900b08422110040184585c4840a80d030b281800003482d161641c060000d08585800b8050500242c41c0d00c00024148542d00e140c1c66107003584c07508500c0c082c042101d0282000d503901070000d02c41424141800303044c0e8940c90240c1081401c0c104040b0700c1c1940b040c071841d0112640501040d003050032000b01500141050000700540f651118607520340e400340088000c000d04000c41f03501d04080c052450080506031140c861034000d40c8104110950a0f4001881d05c04541170310a026030340302d607400c000b16a208062a00103041d0760420341030020051000c41e0b08000d031f900c4402060280c40e99250120f030355080d03140d4040c107141c1042500603030750082c442020b03602c0724201c008848500c2c5e607040310528a400981c019962581d860301404000300b000e0084110b09001140d944130f01c40540d180b03054803031006110706002e000f003000c0c8040454646800204518000400d800c00c07001c030b02100a80a41600c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 303577266 1250 303576016 303576019
    0xa050d0903030e0f06040905040311010506040b0d0212030c0d0e012307060f0b030f011415090708060f0402040308030618010f05090405010225120203040e070c1a07050702 75
    0x5016210160611800d42042120742542d591100030445038184030f600c01c2c04034120ba030016010440400c6a4507240601c6014905c00e540d2012520858003c803404c540c40640b07414400ea090000c204c0c0c00b603452410f18000150100c079060100800241041d1442c441c010b022800c60041d0b04080c03c1c1a600241c02d005c0c2c1c10800e0300e40c00990000034481c3c0010000300041c01071010024012100803880a81c032418a158007440000b4418122000107480c1400044041c601e076911446840607644582200c0f43d001602e040c4680340c0403980701c0005001140080540040200850004d0345603070700c00440950500001d80115038580e02d074104200b481d40203c0e6542d000317000d0724105d02001c000c0041014120340820800e01c03011030600d41040120440900203852a640a0009074003000c1d4500c0200c4001c4041004608a4401d030301e401c540d09070440c610310044d034005110400c40e02507001c080d0303584518586000301c1540d1a914112000da00100701c40000c2c1503192081040072078116000b000708500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 303578516 1250 303577266 303577273
    0x120503130905070c060b03070f0b1c0204120f0317071d03210a0507081201031a040803130510060308130b09030d0309080c03070c15050306010c020f06070506090a05 72
    0x40301d1030310509803101a60038600003040258440e020a590303911500381d080c8001e00f50380c140d0703545400400c580c0c08241c02c194404080040d0800210845480c01c0100b411b044005500305481d00d0340846030805541c50183c10701c0c0920300000b081600c164400540710150315828205401c1c588001400710f50a00d80c1c8598000c204426225130b407800240d48010a003a00040608011030b072035a807001504043e41b5041030110034064040058109009068560021030b02c801466166080003030519040b154161401540d5005110100c3d40030001c5942c4864111540c0348003c03c0c40c50013034501030403c814910000d00c0d1a0300801003181643c018040b02d03d000c41c0074400251203000c80000341c070400f82007a90560080504803052340c003030b03007005180b030f80103080c0d4605261a1244880c11a44140c000b00c0d4103044ca8001400400104205c0380750481551070418254130301140041c01424202c48068800e1914001440e820340d160700458840d19442425244941030191407196218001c0404650300d00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 303579766 1250 303578516 303578519
    0x20240702040b01020f1e030c03031504050c1303060b0a09020a03051f0602070e07020304030c030c090c080f04020f1912150c140a090e1e0f091e030412050313 69
    0x1071000070074814020905003d840d40038074240ea60203070b1440e61800e6124a00081c0480307048c030801403014602c076200308a041c002c641d004204000841d0300003042d00c10b241d02c091011011181854030110241c0e6440319000400340c440c4d800244402c0d44550021030124000246103020661640200d406025081d410360308000c000e12080500105501600303005038000c90040281d20103400110390072031030034016640f074503071280c803800541903a40d0003ea4140c142d56004120038545c40c0310f690026400b44c9003440341c90501f01001e40d09081c0c080c0020313110324001d07604151966240c04440f0641035294040d44151691031948445c0c40c4078108068035020a03440d04c8601c00902401004003c600994400c1004104c00c2c40100003a004030071034004000c06090041062188242c809001701301c4040300c0d0000300d02510440c4510000142882c0e5044032500c184541d414000601c40b85111001311808090032851070018514012036000701c00c00038013652840c1c20300101200601104010440c1200c466 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 303581016 1250 303579766 303579769
    0xb04050a1a0405131e0206040b040303020f0303060f0405040c170c0310090b06091803030712050601030c020303070c03110303070804031205060a0324050f07030e070320240702040b 79
    0x310012116003205907020302d07145001a403002c40f540b1030205c08410050018500c2d4000c5081600950003100701032200103014814541c0400850030041d414034020352851800e0804500c148900340825800340e500c0b54003040800c0500140940500003040c04400c010042d950955a541050b80c141d600a020b0001d450100d00d450340506420560090070076003441d201d00e4140002c1c280000c0100c804001e000b2140454881d080c402103009070169651000d0602c0b8041e0203804035103001c0d00c0c090505280c1101e0100e81d82d0048140d0340d00001c00d040621501c40c079818251480f244151b000304190000004204280b0341220703856029601030b60f542d145408040c44000201e41e0143d070650760142800000300009801e032812007038091548a0b4000d00b40c8003268040090302c000396244a200c600e08010050540e615102c0e42e02ca0b0400e090003491120f25640340ca13075100c3c0d0801c0200e05a808d818440210b180c07101c849402c01c1c042008509000e602c150030445180c1e4004a4042b8421820040424060b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 303582266 1250 303581016 303581021
    0x70320160314031902031b371712060d020d0803060307080f0706081e010311010e03031204030210020f1606060506030a24060e09090106051509150406021f0b04050a1a04 74
    0xa1103103c0250110f11002001031052410040074500f14206c8841e600c030307000804040800d451108442701d01610342a00840005180c0380080c1010b00480407041000c1c09681c2d50344164010301e81204c20740d941c1e600c42c1d0000c02d042042c03a802c41b03c103510407290744000c0c4007800150801240c1c0c0e940e0b500081600c0c0c0d91544080103035610851111030030300c3c070014804100180d4503011030440c1410321808244090000c2811500b013000311043d44080303c0108024160180100900f5400c0000111f01d409083c0710359040d40e01880e01c000000600e8501007404000141d4030580203410020030301e5403280780aa400d83c0c00344c030030849400c1d880030321500c403141e160328800e0369901552141e40b43c0151003510304050100e408001841d0146541d2914000141a140c8546540d100f440c6004000e07a03994007141440381c02c00411310031007040c540c00c20080202c0340c5c1c04210800e0007044131103920021601504c44402414200400035802032421050100c4019580d201c5070310007110720400311040c055401007008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 303583516 1250 303582266 303582283
    0x6060405011203080604140a1b050a0c06090510090b0a0e0a081207090504020a030b031e0a0f0f15020d0c0f0203030a02130308070320160314031902031b 67
    0x70300a25005000c2d0010f40940919036203c0d04c0a400020030394002c01d10f003000c440040e540040181e41d1101c3d00c0b250b03541055640041c3d0314160400074035000310050010a40c0001e000c01818065407130400d10300704070080c8031b50000102c09800500041c40f20303041c075564002d0191203064880e850229001b1044c0004991803040981003400301d82018041074010f01c001d003004001500f0840544070202e0b040e42c451011342920413407079400050000c4a80180351401100d01882855400380d903c94213903000001580801e0710340d00440f1382402c080640b0300052000d0039480c004200c01400c0c07003c4040301501ea4054408030044a1703060200301c03580754080d0780301ea8000c518240144c00c00c2002540700051a0000e201c010b203080e10507803455503603450b00c105039003101d04110b0000342032030a001e42d600004400c000f80c4410384800b1b02051046544c4030300d06681c00c0d12004015500381c02c81e02ca0000e8050085e01e41c0152024504084820a02c81c02034a0764010b540410f050900e6803101e0140d1000007072020f6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 303584766 1250 303583516 303583529
    0x9080c0907140d0e0706140c06040f080d050f0412030e0606090c07021906090b0f09040f270506090d080c0c1603030306080c010f0804020d0302160608090606040501 72
    0x2051a1507008084500307038081030254044020400c50031041c03e81d81e124160b40060248094403080c3e083c4040208801c640200c8171040e110244805503542401090180e0415031016498021140c10310386030345d6a0141c0907c4101d5280b41504101340030540050076803207144520443c5000d03d0b452101941128413000b11011140c1c401c000244890502c9601da54000c0380c24903007141080c0e203941c00070b80d5100e6460780d00c00e0040c02000c000c028140d0816032840240c0038842440e803e0040e04c83c100c409600424111a2045d038030343e10b4080b00c40640b540604100c081020789256984000c191595070031404c80750850b002d11440c400118114400704001e16140301340d94500c0c44507110390140329620707049840000318070b01554030540510740864a000d0300441c46910042030030b40c81e18401c6e1307050030480c610180c148a003031840c4400c100e5011070303590780c401d41c12a40d100302d810150504900d44004041320b0705c5060801500801c507260016905072183c08044100c03403259a88400b80800e0314400e01c1490f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 303586016 1250 303584766 303584779
    0x7140a1a0d18230f0706171005030604080a030f0203040f02031005091506040609020c0d020f07030206030105060706060b030a0f0e01140105060304060b0301062d030201050913020f070503030709080c 87
    0x10300f000c0c420150785a021500080403684100c0f90300c00340c3c90501c04c995005c4400304180411004a0f012540c1d0002e40c4481452441d450161421005c60f8540600a01c01004180700207140350b483c5020303910030382501594070421134991820786000400741583c0b400a1784688641d02c46009522803a00420344240210380240c45101c00340316140d000a000946402c0d03006032142c0010030000e02910191641010f048002c20140341c0c24100a4206400040d01316002d8024100502c003503215502140c0c116081a50101d6440005051001c0204005d41110035040710000c2404180c4141d0381207101401d100c60801c00140341c2d00d010031402c0b07860401005c091540c80d00c00400c824079104c0702135540180150404100900040c000a003141d01d00d0b0804409219880001034848880802940400c440b0002c0d0120890864002804034021b403515548107116446100880c0961074040e84c518540c2d0440d52a11049685000380d100e800480d0950700042d600b400015a42c10b00007000d0f0b03281c00001e40714 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 303587266 1250 303586016 303586043
    0x60605130b0a1203050904180b0c030709120201050d0608031e03090a0b04140d0503040b0c0307120c02010e12030604050c0403170703110d030c0210020c07140a1a0d18 73
    0x60000c1c0c10360003c10707014410140a410003035140ea018640706c4011205c40c03603042e001c941c81d100d00104005005043c02c01001e004000c1c045400c0040074003035a408810080c83c01c1c0d8140b0040f80d240c0b04100c8458240e41c10100f00044c250b000001a04111201e81c1005048040c0028440321034002107960b4420765020ba40c460005c40c00c41181150094042c1c0f4440040c02502882540307000e5074900202c00140d030000c00c00042c81803520916400920303090042d85542410f640082051b5549a20030880d03c2d0740d40440008a03000b540200300d4818180265880c80c01d00c10721142071a0030440c1c02500032424030f000141d00d0343c0040d00b2a0709490340320156071021010b80c0d10407240f035040024220280100303580d124030480390030800541814a2541c01191156445d04003e08108181c4804006103006108144200c0e4020800d0300c00c0d50550000002c950381c41c4000507041070b03001e030320080042c5960302103c0f4800152100810075180b440d030701441042010b12510110341d144400103069180580b82 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 303588516 1250 303587266 303587279
    0x20c060609040609140a03080f060108073009060b040209090c07020a0e16020705041b030504150905150606070c1806051003020d0b060a090b0f16060605130b0a 70
    0x51960000c3c040c890001d0000416a1894191409034403079803100c0e8044281001010707440034500340d00c4132420401041c141041030010302003c030040d00714003e0041049106603003a0a40d203508500b41e907401440d01c581602c64440100810054006441080c1010301d4943c0c030b07081900807143d440303101402025040e030744d403581b0711025005080226071107003100c90002881d12190b00118050200900e04140001120750064030300031840d800180507a050036404c0f0f042c0743c100100b00400d0b0895040c04617083c1d0300c514102d401d8a02c18089140198078058184091000005120080c20003107130400200e40c031600c1c200f255a01451324002e10135245245c05001c41e250b004044000c3c2a1684c0020a426481d0720000c0e002024941c882c00c0040d0303012801e500769034103a01a1000840055070120301e8600625030007050f4000c0741c0140746131541c0005102401108090485121a0b60001a881d0442e00c030701d0501c026100500c251845510340058242045240f40b0800300801c000400207007000d442e010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 303589766 1250 303588516 303588529
    0xa0c050c3003030108031b0c090403030c0e0409020105250f1202070801062603130b09040f020405130b0a03051c030c02010506011e090f29030f06040504080f0a0e0a060201020c0606 79
    0x4091f04160b00551341c0134121612281a01c501039440b80d1400302c1c0c1d5080c1024010078200d0904584c40c0700b0b80c2800e03807190250340c010040f034020b01000c0ba0220b000148130b031005420300020703680050010780c03001081c8040c440b14a40c2c031009040e081d400d8a1625940300115402d8034801d009002211045e200602d011803080605440c004842c002601d041070314140c04060329141c0d680c410a01c801001032030300d06070714083c4264400760b05180b108604242c14403010804883e020b080045500d6503d403408842036580c81040001141e20100703e034a4103c203100d2162421a5480904020a003486610040b960060041510030401030356102d4080105895a1041c0300c260340500d424054400c9001c00c0c0c3e00320034010b27400a05402d0000260350301f09050040002d8078001c0c448107071080140706214514651000b115000382048030049229121410800894030a2010071a1107500c0005c0000345103811400d40350809008850901e4070954a50060f400c0c1d204a40d50074155801210000707100b80341c00c5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 303591016 1250 303589766 303589807
    0xa0219060e03160204060623160b070c050705010903050a030c1704060e090609130b0402030c10030e0708210d0906090b09010c03110a0c050c300303010803 68
    0x4034000705100810803066801c692288081000c034502d851000030950802e406500010011803a28a000c2c09401481a13a842c81e050301a00e001400001c1c000c1501d01c100810802003070700880c40c2c02071820540405071808040500c1151b0301e02810030009095030098031450112604440508800c021550b41201c0c0360302040400c07169030307a00c90003512022003000051300c00780c107164480e1700e000205142042418000100210711605070041080a0711204030b4854501c0e540c068001e0840703460320710019040801040003207400620740044181c0c0150715403c211443c0100500344c8544c01d0301d90308250780b0b40e10b203030b40c1c46103d04060392841d000c0742110344000e00c880f0b60702010020340200702d5600c1c08243e4010b90001d440d02c00041080c440c0d2050300307228007002d5000760b04007000101ccc1c150074482803d0142000c4502404040d50ba1003052110500c40024003c2c07008007455426081091914aa4180e00804240b101c2d100d40c0c41110915002040740d068130b88040c010350600321401000901046030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 303592266 1250 303591016 303591023
    0x417010906022b050121210f021e190602070503161a07050f0a0c020a0305060f0906090c010f032004081b031b010504030807110f011b020103020904060519030501050702030a0219 78
    0x1d203c2c003e08908401c9001002d50b81c2196500c1141e000030b25140341511700004419100c03000ac0280744001840b8020290760f2004200e90800758100710000f8016944003900900001a00e9072840fa140f03c14000320b10f10036007206c038070741c100349c00450f0000d0000c03200310b000316108000c03019050316840013615030581e035407401b000d818010340e000c280301904075402120740d039000c0c90501501d1001c18507890b40c04441a002000c01e807070042034a5980748100000d00303051000d54800d080b074151090304400c4001c10100900c04d21500191160701c40c6034001e00c6103e4442c002c0707001101416280c0c054035a412080140200200c1400b480c41c0403d41c0100e288040c1445020440000091040c001130103846000d1201c4003140840300051140018020b00038034100311134040ba110082845210720f654a40c1c080c0317001a200c0070780c01c01041c000c10040d008580d2041001e5112111149804600c41c20340344074000074441d6858403030050380c2c3d81c05a0380c0ca84000d40c1016090078039243c049403401881c40d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 303593516 1250 303592266 303592283
    0xc031003060f02280c020114090d05071406040509160201060e0c0a0807080613050703021308012705030d050604020d0504051e0708030417010906022b050121 69
    0x94a03a41d00040b82d50036540405195004a0074a03d420402410301309401001c14142d01a80849000100712107100e580080c1401803210040c0c09100c202030946040d460701911003006216076044c02c41d5964043c0c81079130031220b118a807072882420076030151800c59001a014500e1340e190143d40180b824540300030401159a03407100003c11580740c2e88168010071032000c3c1143c0d28030150b00c0c009e014000080010050044003400c1c01070b1600d640c51022140b001c041e10000700360f212403001310064030030b1418184088611590200e0100c1c0c041d807110b5040c4080d00c0c00300c00c0344191120b01c80032008806c80090525001841480000701c0035400c140e621a0740180010300c2c14441c040d0302000c4617000c0e202601c85a01c6103c80041c0540345500603e49003106200521485180421447e0b1b00c2c481c1c1e024080b5404d404541c0c0f100c0460094004641c55a0700ca41e00703540712030269000135003010001800e20483e2140d1a4952001403d0b131141c14103030307042c411094424a492031501c001c0c0c1603401b0710849640c0c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 303594766 1250 303593516 303593519
    0x20d020d0519050c0109060c03031508060721050405031215040f02120609150d0213060b0324030a0807021201060303030204050111031215060409020a0503100b120c0310 74
    0x300280450030b411865001071908026035410101e2a0090013295581801502c2d5004d0110030b0b0050503e04c5415450315012654000703e00e400200022681e0080f1340621424003802149a080440c2141818280ea141d6106246a5100d0400d0701c0058402a11030f070401c000b005200d242010b0881d07400860019022081c2c0c0e50714000c2400c9900d088170041e601940818003200d02504101c000c1e80003842200e800b0f00301e08001ca24600c2c015068030f05248a001d0f10b51080045460b04d9500c0901d42e11810400c00c0304603903400700d100f000d520854a41800c50900d00000400440b6590243e5400001800400010503160b56220499020f6402071341d1103648030400c0ba5110300c0900401029501c280c6e000350301d8901e058000742800c01c10300109c0585030014481e550323600402d440550751100720920302c094042804804104c940c8541d41040d48064000100c8248607500400214084c2c0e203a00414652155200714654079801070b5141e07a0314a40c100030100d00d074910081c01468206003100072055250303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 303596016 1250 303594766 303594773
    0x20300402240307050a0801060305070e040519020c0307030207050d032a051f1d1c030b0603010311240318070902040e040b0f06060301170c090711010606020c030307020d020d 76
    0xb5081214a0000070300001510108950300c00f80490040480e4141404982003060000d0600802306003124061540d490000b00f50031000d03514540081c210490843d5603084504049440380d1004105401600c02d0980c00950b50410381044001d140d010350b00c8202621180c81c064103200d682c030301d40d83c05c003101046550001c00c406202020700d400c0321507001c25902040c0462801030b00c8a292042030b104081141c103101d030380000b10b203072000c241440c10031550720109200709800a0500c8400709401882c080000300c02c00080880c0c102c10a00112010300f030f50105260304620032004035002c81503880090000c100d540003424007410821072200217460103103440300c1c450b900b01d030819807003061006102805e0005010500820a400c01c001100c03c0300c0a00e040710100c2d40501c018442c4108610707002d2004c103030780c42050002c8840c3c014000c11016013410f0002004001007100b0029010384d510300280002c68500014107945240c40144c090340c00c00143d6000c00885591202c2c0586e04140d1210030303407000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 303597122 1106 303596016 303596089
    0xa0b0a1b030b031603080c120a05071e06050c130b070525030807030c11010c021c02190b0301030c0b210a20300402 51
    0xc41200b10210380340c0394514892202c0c0b580c01e002c0200420900c403008082c005140021034061580303802503001c0074450398000c4808504100214000035810030081400300c01401441c00962400752120800e548080b03880b94400b600c0081d9884840101c2c20310364003c1c1043c80ea82d01c2c223041c01da5848a0351100029a0f4031070b81507a01130001c290426415075a40034680c4800c005445001360302c0c020b4401c424140040310b03440c0803011200c0c0194819100c1c01440707134008011078515100c40300c04142104601c0c500383d03001045c1d008900001c140803104070000740640d0b0401662585141003d51048546401040000c4c2041000c00740c010480400c0c09603c00c0b0200b8101000e4441d504282d006011224400c80c0700b01607500080035a1025030041c1984030800124485140c6035807415081c1c88110744154500d02d817245000c2009424941070452203d44649003034502c440b80856001d52 = true := by decide +kernel

theorem cover : BRFrame.Cov 303417266 303597122 := by
  have h0 := BRFrame.cov_init 303417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 303417266 ≤ n) (h2 : n < 303597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
