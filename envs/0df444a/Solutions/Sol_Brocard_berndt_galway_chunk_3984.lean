-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3984
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:14:29.875537+00:00
-- url     : https://prove2.me/submissions/e10dc0fd-5fdc-4099-a943-88c83a8bf23c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 716366906 ≤ n < 716546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 716368156 1250 716366906 716366939
    0x9010f091a0f10090b01170408030402131e09030c05100204080c190501051c0f051b1317030405090a14010f06081b0d020a0e1e22060b040906 62
    0x42c0000700d1414400000903507201c1005448007000001001c00304240140e6a00300a8503910600100711001c2005200c10100510301c128000d0f9a020341240d1003c4c6010110354000030b00c0c1a2401c045c0c414540c030408136a1044511030705c81e04003002051901c0c0c5a0b980b82561401703a40c00d0442e00010f091080e64018000504200003d03a00480c1402e01103003006c0312001c03a801150704118010520701c0c015521a242040b07101d801c46000c101d00c7c0020304070100505421104c08421764540304030682521084021610001c001c2e0402c0040c00e420001c01b91040c0302c007051245030340d100034030001c2a2651040c0e80305000d2540f501c00040c2c40340012442040800d0140d01030070140001c903030200092600200150b42c0900b0314840c0c0c6882503609a4520014011001d640c8401c0b840802e0034104c0c00c0e084a00308407880000c0700e13411403503c034440f0744010351002d410015410000403003001c1310f4442c00b401c401d1420102c028001c01c0080e02c580b210079940d0400e610800e401030700c0382d000304801d0030507420014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 716369406 1250 716368156 716368171
    0x1e1002010b030a0609050715090801060e0f060d0201110d0903020307050919020c010207080d1e180f050a05032101060f09060c05010902060a050a120204050102070e09010f091a 77
    0x41c0c0d00c40103001070340f1121180000b0700415251144081040340601c0001c01914860310960390884425400400402d010302403146150310300171010031440d420030229842070344007441c000d138150744103028081400c0c0380701801c9040c07201c00c08032042041400d0140c04440200c941d510884d0382e16600405180945692101c2d01490160080c4191000628142c114854109a016980300c0510034564028400d007040600100c02c0410b05a40d0a00305400661055a10590740403250040c0c101080441d44c407603601c400e1009011540720002403c02d1020b1500391b01803010795484e490103480e91810360344034101c24440d10384014a8001150010104039024002501c0c1020a0004d40d460141c02d58019004076410721650b581480c013040004d420242d17200741e0182c08582c48203060400581150042030300080071504503030005090078007074400da0342100c074160300400e51207103001040301711208098030300462552601160b0fa8a5040e5028031501203125400400b0003c0901c81c2110400d0390150415 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 716370656 1250 716369406 716369411
    0x103420501050f0a35060108061e010c300309020603061c050d0e01140705031206060c0a031e02030a0806090903131e060809031c0b1e100201 62
    0x901040e6840003c0e1060310f081100115910382e100d24042e01c80303010441c4071400341d048070060001504800040440c44021011034001d4946404005441950046070f4a0b900600b003081c0658269102c44041201400c1c18180308001140300d0b116a900b41c030b401240031001285400c3e003150000f4001e1040c0346448441d00d420407003101b003540065411311000d070002d4458140f00385100511203000d0054016650b10004654191182080c080e00c0880e241d08406d0103c0c4079020100000d031030f00803c681140d0b03440400b0350714020203070f00c40001d4440060b01c0e941c0c00010a01c01c3d02e00005042000b520300342d010341c59103000c2c03544c0381541056480f43c3d103024a046420034403404e0343e00c9401698450708003a040320018034035034800b0111891801018550106041d94040000345504041803100141c959100b040c0d24490302d45100383e0303400400b41c848220b29842000068000310b40c800c24104880e0381c0101c08540c600038040012910070007201190b14040241928060620b400b03407400c1c001c085d543c0000d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 716371906 1250 716370656 716370659
    0x1020d0c0f03030b030a0b1501020c030601030b0c0f13030b0a020f12060f0a0e0627010603020c030417010507031a030d0e0a0e01080a061104180b010342 67
    0x10040c0684000041c07070015040c0030034040600a8002500d03400e009070440e0341044041c10003212955003910340980700344122400000951000c1100000100c02800911040e46190760ba4101d0300001000300c01981c42c103001c0c0d4584011180d008280e4882651051240d40e800e44c200355074061005050613030310b540b040288081507076121086c2d9241288005505c03082e41c1e61040840c450350005446250701000302e002c00320f41603041c1840f250051105840003040e0701c842c61000f2030b4540c0007002a800e50311150004000d050321030740007010f84040c5001a24140303a80d4028002201510380c00070001e594584c2d08002c25541e051141c00001c400c40710029950f160f22a000c0b030f44980000486004015040c0414045a158410b60301d000f40340000300881951f075615980d40c0c641c5c84c0003074111101d41c102040340740d00500020688050360b07003018802d4030040805140000400350301303080d10305044d21030f000704800796604400c900c0c40c2501d8050b4034001c5000b420000080c01c1d000900b01240c003032901c10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 716373156 1250 716371906 716371933
    0x303040b0a1a220204090f060b0a0e1005130e0a050a2a0c0f030305011703190c03020a060c0906030c020102030f01090b031e101a090a0c05040806240102 67
    0x40102c03900c200365032401e0200c60081050620200d003a00b048149030002500140b0f40505902003511101900d50130440140c07210107165442c4118044203000840301e4860303070011715205c208448140220b0501c1c0749401c5c0d1640e00d0090301955035102c12401e4444104014440d089805010f0384a0718a0303504204640d0880815644032104890f00d5043d0303000700252216440c014079040b8881a00261070600c0e08501d8600100030713010902801c0405200c5c00700320400b100000056a424200d203140c04e04002660000458481d40380c5c1d1000d900b141f04010500002c80d09910031340d03441c0d94841c0c2d1040381c10350a010340076095401c800c01d8542168410001c0000c0c9108400b42d0a054802c0701c3c0c00401e00c1c0700c3c01000079180c40c240308258409940717062891961090009400080009001810b000145086507011000b4038801013031600156100001107003458103610101030b0305180e0402c0c50400ea03c1d00d0041d85090002c031400ca464020000c00200e01c0a082007a40b48000001d2005111013800c149 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 716374406 1250 716373156 716373191
    0x11a011b031404080a081306090b090d150903111212150d021503010e0109140601080a0e0d0e3309060702040203070e040b0f06090d06060e090303040b0a 67
    0x600c081d040148611920903541442000c0f14000c0c40300b401110b086500e20700380010f2540c0303c401e001403011181100007038203034068025441102da801304228101103004052155422208078121254502c0515501c050300a030b208800203079000c1c0c2d80b4110700f800c0d503d1009103000c172440802d400c0d0741010300104003c0120a03841a0b4010302e40900c0894041c018008190384407134104c0003d500c42e14443d030341440c0c08154405141210351012510700307103981e911049011141001300782452f01d10b61780d0000d00154080d05045400c12030081001988401800345241455050a41d690014400c50040c400c286070861085422800501001c0c4900031620f02079441e0b0f40e00d14901140445003ca8400c0081c0d541e04c06841d94290090400d40d524038040000402104449007a944502d1a00094800740d04106120821800e03000d00068034100b00c00080011f29024020101d40030dd0710381001080103002c03502c00358040d2103090001c0d81c07a420236140c00e600900008040c1d541035031030b00610782840704004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 716375656 1250 716374406 716374457
    0x8060a090b032d010609060302010f03090201120f020403030e03030a0c240606050306031b06030601030213090204031b170a0609050c1f1409060301091e0e011a01 71
    0x12000081020640300402d08000d81e412862076182412568444a10003d105408844a503480200041c5ea110680c1d8000c440481c040640010300503000280014002d901900d0003500504011002580c0004c1880950307250001c400302e81500460204105034004644001d1014110b002d1400c000b04040018003115510f4805404104441d9000f6140b004030200c80300c42400c000c406000040d268980a031071a03006841aa02a10a03a10010340104006a0840c09028001c10483c9175407217444c011806904a980b490304007503805c0d0b00000f44201a40f000b0402035220318402c1c021039600000aa42c44000c0d41d00441c40c0707454003824503510301400710b01d03a13423100d40c04003001500d0300e0341e0b0800360720700320003403c0703c42d0000d1b0b5034a66047c0003900c00c10440200552680d8103000b00480090340041405840c407810b4001009100500c1010032131782003030701c2c000032048044584141d90345184040e10141820220300307942d60044032451481c04450032040980a00708018007030103601180e861404035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 716376906 1250 716375656 716375669
    0x507032d1227030b01140d050c0103051005090f0717010305070b3004050706020102040605030a09030c05030a082202030616140408030c070806100b13032103050708060a 74
    0x8a140100503441c000c041ca41000e00c414001c46842d51640f0700982811400c0c0280f1140c20301b03100c0f1201c114a48448502000366221000c0c14030701004200540c0580400392800f104600c00b80d402040d507841d00039140340316031b556215190050a040310041c00c022000c501000208102c00014408a68001407900440d00880c1d6039035a5400c80c0840e01d014105018401000c294202d25041c2c0d9a22100d04207501540c058400d0311500c5070b5504041e800c0348514420800807480900000c1c1c00300071141e2103951400e002e8140700d40a00402e03a200c0d0305690241e1099000f00781054188000c0200a1000303004659280070b042803040c40c6030700001c0c1d58040007000711100d9961024100e0907544a0900040c0c0702c00d403190807503101c6455114480c0c80e50840c1d29400213074803985d040000c81940019071540104590120100f255050070400f030000d510444118003100c0c0900780000008040ca4510301e0a070f00d805030504211340c4000401015541c01030141000c1080b10000d0200e20ba69012016044410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 716378156 1250 716376906 716376917
    0xe0114100608010b0d090807120807030c0f0e03030c070b03100807030c0306051008030d020919050a030803040c0e19050a050720100504080702010f02030f040b0f070507032d12 77
    0x2440c01c900c4021b400101c0d00101001c4001c03441c40104401851a2404001941c0305e81055554840341101140c580201c50400902081c0403510010b001e160700484900002c0d0940703180c15090780070140b0703050340b0307230300003003510400201304180c041c03c141c0084003800b51100038180442c9036490703a03109004d0302c3c040903003119a81d00114101001c20107207100106582c005403070f106e49072030905030001e411402079030b4050a00d01282c003005550391003a10051ba1401001090035600b55211416250401001207480a08041001c00d180c159200211301c601d00885d14103803040d140d40242410b5800280035240c02c0d50622003444134460300302d00c2d000e5064030152804441c030010038024902d00307035006080b000c00500d0a400d000038404c00d00000c008c098001c0e00c0e0f009250701c3c00035003240e0702e11580d144c294601e00d0030311043c410032102e85c0040581158001041b42088003d4030ba007405c000301e40d0300071103e00114260340d000d55580c281d6116010b001003131220382c29800d50380ba000d03000304002032000200003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 716379406 1250 716378156 716378167
    0x60b040626040b060f0607050a060e100510030218090a11061309320c0901110f060906010920071b030b060a15051803100e0114100608010b 61
    0x21160305000007101451100484030381800c0c1003007801d9050581d60140110900f480713005160804038107c0b010194420010089000180c40e410002c010159818038140904000c0111480070342c016640107941e8110300141040c554810815151804a00701654426040400c03100003808646070383c9103038002d8039100250a821000500c40c1c401c03844d094080700c0c403040000c24403520079405100403040000d09a080072a074100740d1903115000c496034510260000d4006034640c01a40041c2c01c900c0e6040c1400c000c11400962114140020080b070b580b5141c0c000401c00c1602c94080002900414800e207040101031082a0400751003004185481403443c4000307000c0c010070003401c480042c0480f10b1910516a5501d030302d07003902e48036002d42c2d00c00d02c00c20726100041a1000b8402e80200803030b25a444052a005d02401c280000c00b075226049075242c018403c1c80f45131111680600076800c42e0600000609030900b0340c0d03907444110060034803410702ca00108180600f0340c2000b000c50554061070b4a007030b181c9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 716380656 1250 716379406 716379437
    0x1506021c050c07170d080c042c0403020607020106050f030a0807140303040f0606090c09140102010f0e0f011b02150c0408100c030f0e0606010e19240201060b0406 71
    0x2e00c580c00140e40c482c450000c00103040405089070811410000301a1164100c00c4c80c2d0890380c070402515414055071041100b0003900c9040c000c81c8000e21084015020740d104482c9140f0880c510444094025030480380801801c5c03942031282c1c0c0d001d0031040310240090ba0207407020a0b035581401100411540c00000d401003400300151840005190300c8044135646c0c502850316803d40c00344070301c044030b0080c03c0042c042489009801404000b43c526550b4407141c5141c02134100070504607020041c150356948404003c5e40502e0702070905020881c0001300f00b940441c40e442821a1078030010703550000005001c1031801035020030440e5a800c107003100350f400d980740e40799141c50b80e100d554001c0307503203200301c0c200341e2020200f0360044802103949450400041da40c0c2c0307001ca001c0e01c1c00941844c5c503030703000603001400c107600401c851804024082c10070041c242d84540c030402c1c100079503003001032003d80c4000d6941e00d00c0e14103c2441f031443c0052009200b024900344030400742c0d02441c01100103010420411ba41403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 716381906 1250 716380656 716380667
    0x3f02011b051e06060f010309110a030305030105100207080a02010503100f060938030901060911030402100f020303070c1a1503070807081b0103060302031c031506021c 73
    0x101a900000c15842200e8a403450360303546210080d810521100208080384000071440034426000504010742d04205000110000c0caa4000e04503900041c0c0031401a0f10b0700c820013150041c51194586591b40e50602081064090024080f40115404040c0900000e140411400001942800c00326142d840300401e0b001d414406400c130420320100c01000294081d44012030008a4007143c2c0c1e450b0660000d00d1454081040002c0150060305048c2c0d03544c0c150300900d9004503440900100005070f259110000f00042d0b0340300041510407030201005001c00d6180c50b0042554500c002c3c01c1c502d0b10116221030183d100d0000030480014090003986002c02e1001c0510481049805004070603044e10302002034264201e05641140d0107072040542c0401d0000d00042d08000f078510001c01040800348204e908070601142c11190781c10540c94400c0080103890810401000400c050301c04080156030841c001d0403036400e14900400e0451520080007203603004624480d50003045041001407100da4001500c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 716383156 1250 716381906 716381927
    0xa0f0204060812070201091d041b171c0302070b040b040302070e0c0703030606090b0d02030a0b1804060b01080f0403050c0a0b0702071d010b160f12093f0201 69
    0x18902804600a404059000c000c12504d40301b6220385501d161601100701e141d035128030740c1c565594469008580440c40c80f140c1c802682000d4401c00e21f0003a00d510044c4811444000810b80380d82c40307a03050007803000c03112440080360320261070f01310701740415034a620301d10401c041d001030000000800400d060502c28400b01010705040440902c2a003441403221742154000b680603400a440e00d4400b02d0000c2c4510f2640c01211070a10055044c4203240702d0507402548040c00e1030f019503595203079456142c0c4451000d03040d100001c000e8481d841c40d20382400d01c19101a0004181044107100400c0001c0200c442259002a014901140c49185000c0524944182204090a013040c50010484025400a8180150346601100040d4040c61144d6164822428010200e04e0300041c00b40744001820300c0120401503008800a24480d46291950f111121400300101c00090304010184070260102c5142d142c42c051101c40c0c65003c090404141d09408101038003002c80170061108082960b115607034064 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 716384406 1250 716383156 716383169
    0x152a0304120501090c17010b0301050f160e03062508010f150c14060106030605010201092a030f051506010c03080105060d0906050f150a03050601120c03060c0804060b03010b030a0f020406 82
    0xd0905488110821440d901c00c0180342c441d6090030808c54141c1010300070980515071141e400300207601d070b01c151401e01550249140d0b08006010000b04203035641000301c0c034064100198040f0316902c0c01c02c01400500801034503035041c0a102130040000d00013400207041220142c0806100a030701c868411a0000e081040190078000c029680044590004c2501f034100d5900b5201004029074030001a82602c0100c0005890170701d1900d09034600007070103880e0f82a14075000b14110380c00d81c0c480d1346100d5890310755081034429512000c02040b03902c034240b03403244e0844000d007071000e6141e6440d54002d2443d5014060035004501c00f0401101080c4250401221a40d200405018605d0312420a020f500c00c00c60301c545c0c4182480024180d5400c00f9101d01060b2038002001e04180d0382400c6d0242090028a2402c4800440c10000040844c0d4248030b80301c4010b1090b03550459600b8070f401c213441070b030f104902180d00c81d9151407010042c47e5000030b003e090030b5a01102c1100803101078000100104207030380c00308 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 716385656 1250 716384406 716384423
    0x307031505032a0409110621190510030b0a11190513090e03070b27062e0905090c0306090a06050a050f0402040e0c152a030412050109 59
    0x1820643e0300070482e000710000800e5818a079030400070400c02a01d81c110405801d4220304004248030b410200000c1526040160014051542c020480704025400705c40042602c07010a40705548900369004064209658403d10304005003162650307a1540f03009000c14405580d5a40c1010402808070309480d951445d6240d241103a4124a40c00b4104c2e6100c4442c00c6003c800c44c54010031122841d10402405221110080d8140300055444500500d4094241030030f001201c030310282c1d800368501c820f41c11072005c58007419076805c0c1400d107800d403884021206078623010000584a241c00e0580555001c9580c8442c0c0403c81d901c84038080c50a10700104855901030003034004101c00b42c80000f612543c228414181041507989491141048860540b43c0e1007504041d580030a000d498550408900e40f80e500090300c05984003600040d05c3c5440c00150384044a07004500d004160343c0d15848502c0c10128441c3c1d0000900d14594503036268403507070158800c131091b0340040c2810301100f54816260710f684a90203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 716386906 1250 716385656 716385673
    0x418080a0906030f06030c05060705120409020d0e010c0f140903240703020703050702090402010516061e060f1e080d18170607080a0905011e0b090c030703150503 71
    0x7400c4001e5405001c000ca414248a0100f82d8110722811040702e40141c044150030b400c103000c05c4a2a071160b042910644075900300c18003107202100040c801032480900050795034901c800000d069401c5800d8500c10b0b640f400711034100690300043d0500300704110340740c4195081100700134611640074641d001d41d014030078010035241e04030b001c0882c501e208440c11001030999607414401c030181d100d1408000c00088040c014900181032405205421510505007141016003484044620400c0d801003a5036440e100c80c2d006560307180c11800c40c10001038980007440b0f50381c18281440e00a5a180c86107a030400d0f500c0c040d681c0075914501d0420083c203003000139207001100e402d02c0141101100f030466648101107002c009502e41402c803180e4222106400908450b66032001e00b52030010000340f03250205030b1111002c6000640a2084640c1e210815010340380500034880d9420481d52a2210b0074010501d40701445481010340080c0e96000c00c1500d008200003000d00324885024660741c3c091605407044855 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 716388156 1250 716386906 716386927
    0xc0f0f013e010b0a3204090f1212022502060f04080106060905090f160909230606070305070f031b08091e0d152004031202120306041808 60
    0x104410341d0343c040390b060b011341c0d0300d650550490381c040c01c00d002550f000f5045145a24020386400c0140d40d07000034000615100b45840785801c0445107031040752408855805055800e81101c0703180c0c0c0d0310003170190450a0200e070201114500c401000c903801544d0003404031000319501d2a0440f000e00c60440078481e140c0d562120100d010340607030300422000c03401c00c080c0480c09003440340710180300700914419111151203005802e500c0c1f22940d141c01040007400c44011030304681c40d00500c1e4039200040304d004102d100c00c0341c1203510090054045881008100540c44c00300e68440191685035400044c10300310116030307107400c7e02c40c01b480c2d440782c2d5030307201d2000c5c10740301481210009000d8003601620300b140107100e10040450b0394010001110791014a148400001c111030200307460031500c843c03170009566074215802d0b2189044d00a44bc2040050001d814001c00c80071409070002c0198900040044040c02038103000c0b18080100800e003e2555a440d00802000010b4105c40e0644c0220056945413001da4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 716389406 1250 716388156 716388161
    0x62f100509031b0d1b03050313030e04020406050c190506040b13060c050c010516022806150303020d020706080406111e18011d0105030c040e01080c0f0f013e01 70
    0x200141c0100c5c481d101d02c4d21205080b190306011196140d910107140d9658911190382112000000b034040102c00700315881d0684130ba10082c0003074102c3e52280e5032101582207106103000308843d0081542e06045d009030b4001900051050703007055000380c0d400d040340d5541007100030f100902400a4646814024117402050308030000f09a04241c00c0c000703014a90324008003030103041d0b84a00160059020302004803000300a41e01c03410041c07183c0a100003100001c0e88920040d180b012410400c8035000e950b0070020150100001107018400340007915000b8075014000d0000f031002440685015242c03459245401c1c092811112460540064050114031030901200a034100c038161071005030100100491960080c020301da035220601060100091041300111255080034100452540052001044624408440314042c0204070002c08000c00f02c18200004e00c01100d80c0e950103600c40da00c11145e40d91707008041414003a0054901c000d50074260059103031241800d000c42c514002140d003c01103022064 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 716390656 1250 716389406 716389423
    0xc070e0a0506121e01180b09070815010e0c0d020a030c0806030f07030f0206191205011706060111030c031c060f1809050c0a062f100509031b 62
    0xd020420090303031000e050103100f180e4001d040000ba13100b8030680c03400301c01c400c1881e014000c070080081000800d5603480204e880070b80204039208001d10013000f804050030071000e002000010003e01006504c0340746034601c010306010704d1541e1400304001800b240500d0f011552840600c2000715903585c01064020020403040300e646001680280104e14240740000f01c2260500240001d41030192070340e039403584c0b50358800c2d00c100c2c0c10a4041c01250100750428040101c90320f040d4407047d140746103a240d024100c0302e05800890b00c03c1c80b2601103110b6001c002034115030250080c02e0030003150745076001e41461350080302e560510500c0002032940700d841003600f202503c1c609035602400099201c14070307004a41d1a600034015000b00d882605202e40b54039400080c2124054400d4440c2210b54202051500445410450104a03441003603c03c110110b402001070041070103a0180008541c0d405645a01080c01002c560544600105800040a00445001201030042d6085014004400e1906c2c1d1006 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 716391906 1250 716390656 716390671
    0xc1e030206060a0b0c07090b12010e100e280213020f0901120b032e06090903120504030e1002010e1b120109020105091309320705060304030f02030c070e 67
    0x8191001070218440130650319000c441d040544005401d05004000800610040d568040300440c0980f41240003803143d000c545841201a15201030030f01c00c04010703180c010b080c60001d54890b81e074030321000000041ea444c007440854840c2900722103500000d021440c0c1c26180c000d966100080c0910541d1890000304083c807020780b154010400020010400c8851840c5119090b422051201a40600041d60b6100740754002001407583c810b002001005ca410703941009400561700e645100c10315030080d2311965050580d442c14482441c0654008044410352500c240c01405c024010801c1103000303401c954507191059040310b01e0b070b040c182d140c0e940740074aa4080c640602e540100400325201d0600034080d40d07a8042c2c592510b00300d80d8405200c068125961300e9502300b540d46220a00203851012400104141d580307064081c03112008040203000d86030300440d40e16a00125080159803a503030280c0b540142c041c00c120b005240014800e0b4214072407410112014043c101c804691b109a031000240a40301 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 716393156 1250 716391906 716391919
    0x1e0c0f0112052706160f1107091e15030b060d020409290906150d0510050f0c07030e040b0f060a110705040b0105120901061701290a060c1e03020606 65
    0x5511070707080d110740c0261500049031206039011711100d40610500c040b0300c801840c0555058508110f21030602610382c100b801015141c201c54150007065410903207500142010400410348032511074180b401d21448020f00400700309000400c25540c00e2034800301190081c8c03080c040c0c0c0015283c04c406400b500c20f810203a81415140c8000b100d548070580718498900d82000700040d0321444800b0b0020312402440d1a4080101291100049c1c0f0500c0300e90071000c000c01e004101410314a03414100c40308001d1004907551404d20000c400310b070340b000c801c41c1101c50a6070006100381210b03000c5460010840903d0344c102000203400d982e5160712140b91000800340300282da03001901c3c0d0081009480041406034001032041c0702c002c209400d90801c194110b0701210000494554456815850340c4c0140c1041c1c06995682c05440f41220541600381110003000100503040e002401c0001c0c81600c55000c0d44003040411110700c0104500c0e903a050f80c0404500e041d80f86402c289190003541c484045800700d00849 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 716394406 1250 716393156 716393221
    0x312030f0901020301060906140409111314060702040f06080a0f12090b0301090f0e061003031101020a08041722093b010b1c02031e0c0f011205 63
    0x20018804c0d42c5c10795010b40d580340300c51850080c04941400d4060070041c81c900040000151a00d034501c00c1c4003944180310765403901e580748020003200c1018203500034104900f141610000f0f540e10341c011aa46035504031000181c101924003404020103054219000e6403094002d00c070300b80501c108005079100c2c03081c4010314a101d9495001c1383d03145400d10403052018000d000500c501403164200280c1d480c0b40200010707100d41d42c2c490b080c2ca0500d040c0c4014244003400041032052581c440c07000700d03610400344003d40c5000240d140003801c014000744003901c03020700243c44441002859040700c00001d00340c0380b070f604e0412900b00d45090b1802c2031300c104180741d0305d0174804040e402064040c0f6144041c407a50700700d5809284041c00c088080201e490084155601c80945945035503651369940300d41007400302c1400d80d0003a88181031416583c122001e020280014052041031400268151046410f03074001d00c40c80d0000d00107a645401810401802034200410400300e00da51011a54880441e4140e080841c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 716395656 1250 716394406 716394421
    0x2030f10030c0b0f0919080d1803080a050c060a14010e0610050903070f1e060c051b1503090a2303120709050910091a030c0405060f0312030f 62
    0x2000380c1d1100030300d448049a020401c190203540940340f9205070f81003051614810000241c030524030030a0b00f490401c28020203124134402045500035075002421b181450200030090f41402140354800101100c1c0700207081c442c00303442482600c20700503070401110384074106011408042c100000d000344804450000009100d08840140b500401001d050029403200040085030642e100028644c1c051065000002da0310b050406c128004000c81c3c01d00d00c0382280c0d440101180003410f64001c4003080000c114034404900e0104140c0000e15901e04103840545400b0049040445c141181c8820030601000f00500d611002c119041501d1060400d1071900c0c0900d08080c804640b201e503c5240d40d80b0912072060604003003144140c220b407171800e1581d204c2d03544500080255401b261240e507850b0400a0401503400c42d0300a14a075481e40360300d400200810140441d41c0c6060301d08002c0d110f1900d80c808103044d501d070034083c0c14801101806407000d0303c29041d442c40d4240d0080d00c080100d44160380008222 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 716396906 1250 716395656 716395681
    0x2100c15050411012105060a0b070609050c0d17210c0a171509090a0f050d0e0a121b05040f0c200d08220c050111010c02120c03071502030f 61
    0x18020280459a00985d41154000080c0300c010040342c0c000740310a03004515003080c80c0c042c1820502c01c00c3c0208a1003c1403420724180303106501118058841c0c030102c2000140b540d1100ca08500c1c14110039a02c8404c1140110200c00c0d0746a01c0420202004080c4082c07142848010404200180c4441c080084040174035114602c045130100e103001002042d00301e2500c0c01d8070303c1d2600300d840802100d1541046032540c8408030158070049605520426040c2c0d080b0f9008180000500c1040310502e007030515061242210009005000b0b2030240c1180b000c82c0150b00d01002c001c090903014200f00150502c044002000300394060f560700220b50041081d107060f022118000c6166450400541250140c42c001550003000c0544184200e40c003903005411680c5141003002052030084c0d4000114030310300b00015060300f805400c1700b00c0c80d07414401c41028081d00040c2c1c00c404020940e4200e5030b505410325010b81540036440000f03003109130320305402040034040c1d0040d50081003002501d45090725849000d401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 716398156 1250 716396906 716396927
    0x10f080106140f040506130f0801090302030d18050708011d011503021005070807060207060c0813021002101a030606180a0203070e0d0506090c0105070f02100c1505041101 75
    0x2d008500b40c1c02d4203a0010020f840d2040748800c0440c20306071204c0024250f070700111248102d104842c0010090008044800c0000346513802c020045040b01e6100203440c1d01c9130000d90481607841d10281400001c1e40d0f5130700700701389411900780c42c07405494880550103001182703c185050390440030f20614100042c031905002040845c0b000c44102d145909110303501c07844040b0003003800b82c24814031010a01e003000070b0003114840c00e40141c3e1003143c3e10f0030b8021036031034041d50010420344004214841441800031052a50111000c03040001000c404234035010541c11a810490304043d108c00006c8240038401107465400c6041e030b00180c0d1180300340500701d40c008541030f0340e8950700f00115904004a5005681000c040d203000301c40f0020800100d20840d100d05000c0f030340c0b40c0c070070003c0180306031051050060300f903800d280c01850074100b0b4039001c0d21020034410203481000c044110464450140c44400410303a4460141000c019a0603490002071004a6040d141c03094041480c0020750b01c118803059 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 716399406 1250 716398156 716398169
    0x10501050f06040e091905030c1009030c0f0c0932070c060c050d02040314010609050c1b1e0d11031e0304020d021e0f0402030403050307050d0b0405070e010f0801 71
    0x3801d080c90300b01c1013801c0f01000b901000c45800350041c0354069440d8942581c0c00240283c00940d0f844032200e914501e4010f0303581001e0070441c5041c0341c40740001d510810440c106500b010542e4040c00b980d00340184441e03407135401100074600d001390210396000c2c442c1d44da01024840340446004684ca01081501241045880380300040e041028400015040c2d030210b6400240c520301541081c10003c0600201e1b440b40d0004ea52500b02c40c411040c03111001d001c1c0b4000b41071f0f414801c0c0704600f0060b035002098043e040800e640c0e00c00c525283c4803034010400c060060500000e042e1085003810707a04031500d0740e41c031b0001c4500141410010070182a800401c90700034000c02910006440880c00c0842d01d030b41c2002d00126804411040300c240565100e1282040000d8180c00c0c4044e41020030041240302100c0c42d060f04c0c080c600510400001c25017081c00e0301c0d0b020006060290344c0b0488161704100604600b2082d5034411300d010700340003c4960200c0d14504400d4285c81d202c0d00d0040c10034060303591601c00d10517034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 716400656 1250 716399406 716399419
    0x30c04140c13030f030903060b010f0909090302030d111b060609061e030105040605010504060f03081e0d020a02060402100320090d1a06040b010c1a040c05061605010501050f 76
    0x241d0325a40035401050342d103030030051010003262030380c0d03900403058076800c4180c0000b64902c40500600250380709481041c2424204040e0700c08081e0070140040c10184146c42c005c40d55080f90006042c02401158141e19061004100d00884000c44990035000240303581202d600202e0301c500c40481c0003481a00503500100820300b143e56040070044070301c2d01894070903529144002080d101d6100ad0140d03a018510442000c00d00d58145810302c4104d640c0303170f4042c202611000904102007144a421a07051110410030303489003400207601e6200c1d910400742412803061000410640240c0d000c50f4040c00342c2c0c404c8641e0110b20010500c12415a4110118005032075050755983c10804100d90040240b410094920f441041483d2030f0001403c44010600741100f40308020401a07141c0303407056003c09942402c00b5102d00380281c0b24528481c4064250741d4280300040041014007030110184030082000801c1c03543c2d552410610407914a1070300b40211001e40c2071a0005c82c60f442c2c07852100702c6911014121 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 716401906 1250 716400656 716400661
    0xe0303010303090e15030609071502031e0307020a020604030501020a1b050c0f04111201210b16020a0602030405032109030f0702190f0f0902040513020904110a030b030c0414 76
    0x100c00c0450000b0b4003a840500710032a044480d52030038890184234198050107007010510740541d07170f0f002c00340194081c0c0c2190410042c22020410801044400022954a030794807599607500c00c0c2d14090074510040d500400100d40013041050540040102c0b00043d65040d40c0c2003072a0b0080c00750700200440052007604950395125140c1010200258031082c0140045800e50188803402d0b420762085104011a80c01301d0010300c4561a000500e28054034100703a100000b50b01a1110b00c2c0b80c01029111062003004ea181c2c602e1524400c100c0302c8540c0b40c00480c110350740c1c100703407410325501d03400440c142c3c03001002182d4256000301c800e00100d1081881101940c40c01c448044050302a601076042264003c8480740c180301c811048142c200040d1240344440c1c2032a40c100301d003418401400b03034000480c541c01000203004a0720350b06659000c0000c41800940c50f5840f0500103400780c02c0d2680444400c00340402d401c0b00d41075060700240000e80058040d2240c1800e09070902c8181c4e101c60460f6035800b50107102 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 716403156 1250 716401906 716401919
    0x2c030601030b07110a0309051e040f060509091204052101110a0807090e0c210a020403021e0a1502010227040c020102040506070209040c03050d02061923100e0901020403060e030301030309 82
    0x22740d24a44810000d0845c0304c01c0e40d000142c02c40701010504108660354500c180440e0400607081a001092607005010600603003054420a1065000b4203000e002d2080c01c002801a82c24040c0c00650907101c000d200780c05800aa0350020380100c2024000a00b03044007040903103000c0c015503001c1d2459182101a1543c400881e8003159024503004034020151070404000300c04010180c0740240300c01d0341c003d81c0e102d195004004803003030042018210141e843d16600419901e04c0100d0f4100e408040da8081c05940a4000b64028002c2145100c3ea0100101c0c0c4010b82102c8100001c036808000c4608202c45070440e24103d00301c0c001c501489070840001c000c5a070151814100f41940035118200980d000340d01c07035440a080c40c40030248030026131310a4007070102240140301031084a00440d8010064a10301d910f40c448440c405c1c02c450201800c003100841c11055540d80208081d19500c0c1440c0518180702810700d000351710a00c02034820514000100040540100850f812030350180d440c15103c900340030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 716404406 1250 716403156 716403169
    0x40605060a050a090608010c1701140d02040f0618021e0904020c0703050c010305160804121803080d06080106150f0c0f03180b0a2c030601030b07110a030905 69
    0x4189030341c0840300000c00549a40d946003000042c00446401046251a08a401b82541d4a080c121418010f1030071001c0c103074a00d41005141124400d40c140320102580c5808a89412a841000781d001400d14003900b1048e480c98009100715080c0c440c648401c0841520000101e000301543c03401c20708162031041200072040400307410104401000145045042800c40e880e20096a00450340307900032103451192036801d44181e80c1e020907440021b402c04680f00000030503001c0000c200501d040340c90350240a85d1841541e4030764000360304d01703081d0607035503202d00346000c0300e13001b0410300303112203040c071001140706401070043c10308031682131905090300540c2000c292030a4144500315020000001e0082010540f0510301c1e0300d0090203030b1103440300075914610524a1804a8003e90264202081482c095640c07111181d4910011610441e44261844540803082100880d58503850b1217400004030500000400c518083d1f52161540802040b09403407a9480b80381101014004c1411600b0070443e038204075 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 716405656 1250 716404406 716404411
    0xf0603060d301215030209010e07030b1002070314070303080601121401090b0f03010621020409080a030e0f0a050717100f060914101e03080c0a030801140306040605 72
    0x410000c03441c080031100c03000070a0110b04020300080d0000f800400500032440782e489581c012200034600c081c1107030003040450406118601c80303219000300140701c0078801e621030744004074010020711100c801c0f0b810007540c94949010a9900e10014103490304420790009450040341e900d503c6403140c0d651000019101c544501c0021800152540d900960311445522031030701a0800c0100001d01c1e440344824401c1030b400c20f000c19806030380340c00d20030310500c041c400c00c142d4170100b400f41c40c003484280c0c0d20105000e0201100000c00c0d0020100d0388001103601a00203410504010b012a5000d0304004929541c0b0f01c010344019009420200d41031217010000c482c2c80200010403012115030b5150900100111090703c0001c02c0b481c1c0d036940c828805100c240c06250090582e032130183c40c003401c2141e940360f1500e0b02807081e0560f8000d80a400c500b032000440c0c0d0b03000210f17000115140c80b048050400764440841490132400161403400210300e010303510b044214440750103001841c195945541d200e0081201 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 716406906 1250 716405656 716405693
    0x10050418061404120c03020c0f0402040e0c04141905040b0d0f03110d0e01050405060d090f0804030506071d010c06060b07060e060c03040305070f1118060f0603060d 72
    0x204010301010480d54010049610070412416906280c1402d190000400725010602080040e440b4100400e500140c00d4182c200115064080c41d03404ca80014000d205542c400c15407900210200103141f2141000740040740e00032413289207002c84007020000a92041004100032090220b070500c5981881e82c4280030001e409000007804804c81e489130144000a2002100040c0006145008818092190401080e21410034040c01200d410000c2d04900442c050203010361008116a0901d000e5604035906280c1c20241c2c40305402c0190520840d507502c10301041e03caa2240c50085000244203081e415200b4010b0b010041045200304011900c25503031100940340207803603c60200303620300303614001c004640c4621400154200411510390078240d00610a0384004030900410000c07940010490311502d50200d004949410103240114912300018001c0d82c10075201c00640b80b80c0200118031600406040314900c100740c10303620810420b03101c102d9a480d00940c5000c2c6001c00552224800f103807442e130 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 716408156 1250 716406906 716406941
    0x101d0408030402180a022814091824030c0112090f0c141206060319051c09080f070612090312050709061d0a03030e030c04091401060509100504 63
    0xb488070300e94005600030340314218466170008090266091040038843c032140b580482c1214010301f01006000086041e50124541000042070343d110350b1011003030420312039210f0550700700c2d04101080c0c05800358552a5a0f48008810845120900d0002800100c04005030f40f4140602c1d03015140d800502142c0300c0c2100c41d1031790745200702c0004840040d0748018120700009550550442000c00a580c0c000d1503403034089411a4042c00182d171800f00e2245407d0b00e00c4240c0074606030040ca070007403500941054202e1100d0026180c0000d1036802508002150241c07811249400c0301c20441a803604c03020300c289400704410301000c60010030560071000d81c00b4001d0a03e6104840646022400d40d50100c40e420000b5402000074400345400811540000c0701280f10302000f2440c2002107080361480b4000542400400f1004410640d802c00600c00c407039070007900c140710707402141c906084940403a003007062855003054070109036405c06030f029600c03440b00078180c0c80d41249050b061200500c170314490a03c0140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 716409406 1250 716408156 716408179
    0x10050c0a05091f080a1503150207020105120106050a140a0f14070203121e0301081f0621060c05090f060702030114090303040303051501021509030408010903020105101d0408030402 79
    0x40303d0004101070074415488104441c58030074031800450303d141620132503445056030144046690b0440ca40d00c1282e20050040e86c0f0901d40c0016107250142c07010039040c4050000020803082e81c880c024203104615901c91510841421403034680701e000f07211861002038681c49502801900c40e0303415482c01c940401c140d03440c0c114144c02003410300e41d5940c2c03e40d540e000d00052104401140c410314400030704c2c1e200d00c0c40303055504200600d40c1306c07051071318550400c201d50700d403604014149a00440090245009200004661400c0740041c00008441921000e16024600100074000d8088a03680e02d00181807400381000d000030804103411075202a609996101144081c000b202040c19009000410065440e450145802000d40e42c0040542200d52001d600918490360001403101d05040d001c0407038076441c2e4501c0540c610358011544002c0c00d541c2801c54040034590194012405500c070800d0950140e80c480d03062522421080269441c0c610801c80040d0104a462010f160041e100401d014a801c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 716410656 1250 716409406 716409439
    0x30b04020d030306081b15070b010905040503120a0b0f010801050a030326090307050f010603151d0316111008070f0e04020a09140a05030309270a0501060210050c0a0509 74
    0x103a00d00210880d009001300d102c4c2d11b03483d15180c0920015a010003a9240c554540c2d210184020b0603c542c41100e91590003141c10000309105498200001d10b502c400c4600c1d190900718042e010788100f01d0f0141d00c88900401d540d510840e42c0380d0507501c000d010100c0440c0b82d9501207640d0f45928421400100003081090101c1039203034091405031b0721441c0290303284c1821341000b40c18081d1403080960aa890100300b00005030329018205ca0100006100041512440342ca40348500006000000640000204002d10300e03104101070070900e015950b0104400780400c144030a41d08421441804a0094400252804c1c440d024010100e60640f40c183c103021881300c0030405a800a00105010400520b0180580e8031404421104050308448007443d451519000c01d0f207a100d06038185005180d02e120082c54450816029a564071440040842514041c103042c0000c007402e000d40401805844144100d00320346015440c080d004d625110f5241986120055550fa030203d1811508241c002c005d41c3d480 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 716411906 1250 716410656 716410663
    0xd0609050c10030e0c0d02120a03031d0303091207052415030a0f030809070b130603060b0c03300405010606030513050a08030403050c060103050d03110301030b04020d03030608 77
    0x219841440200041040c1804001c00200c580c026201003501d4400c000c00444400034660f5070384002036442003094501400407600c0880c1c0000101d0680c4114604402016450740c441f80d40c001d50580c001c41400300480304c05449201c15a41007040b40e200d0062034545061000040002500c514211040c1802005000c0301e01040e01000441c041011010411141c0d040c8005a000c618203c1c050714080c0000c2e510045103010550001e4208240100020407071a820003000740a07204141e100c54a484580c6c4008500803503038000c040002c0c2c105000000c400c814030f819900400869406541010410f00445803149a8061049608100c0790061001c030b02d01400c146001d14081c03400851003d0905001801b81d51024284401194040c048500840c20108002001a034401241c0e0303902d885d141002c82c0d940c0110303805112240585c00000007007040002c1c402c0d21031000e035181488005100340410056010034400a0040b08801c0c00040c0180b628022444459120741000248a9200c08a0f10700d03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 716413156 1250 716411906 716411921
    0x3020306240a17070e090d110f01110c0106050f150a09050d0311010b01050406020706080a021b030a08010b030c120a0e0601080d090b040f06180b0a0c11040c050a0e0d06 74
    0x200b0700f100c2001e031901d030f0810700034403014080c2e00e51007202c2810105c05c101d5070f400c105a040800c03c18420051064400c040c04609100120b43c8005e01446034007441c0745902c0c0c0c0c02403161103250742c86c2170000242030070107043c40305100000400c20503000741101c000c1d440a60290514800700320360814017242135a500c0e12040c200500998501d03a0b0000350140702e40c2107819800290341407001c28401003000c95400549141558054900301040740c46a5100c140a405841d441100142c0103200340b8001003400005030016181031741d540c0880740d03038441d10700f81c051205940201c4103101c10402c03c0c12046051601540150344010b00023412038490b41c1031410b090081e00314001a41002048002c440e9001c846200a0102c8801061409250402c0c180340040f42d0f229850900c007041c0b0b4041042d00321001654018040c04990540e01d060a400045c00102020300844140b4807503080c001c01810a0f08ca0003a403403000d501c0e07440c601072822409484100007000e060f40e01c1140e000d5481d00050180c042c068 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 716414406 1250 716413156 716413169
    0x100f020c09010b090f09150d060603080403030206100b0a0e01050906090409060209040b180a0509190c051e0102070b1b19030e0139080c101503020306240a 68
    0x2a26144842c003001301601c00380c00c0103803282001b4400d000001da0f040301c00116180c4115450500c0c04441d25050015010a60004d81001400f0900205150f00424180d108406200d5140c0307006840d0904c40b5124061500400002240c0368682c4015500410081070101e0b0b008007154144a010b100041c15281c100340c04403001c03500070030054280c0c105401140f0640000701c50501c10310b0032617229095092001070990094940780c0c8007203a034010060000b03000a210b100314014a10059042640d0040076500c6024010382100d40020018440c84e1840c68032424140e016000c01851f0024203011a003211040710906c11294480040c09001040520048006441900307055406420040c00200030155104d0504c8000c80009608654081d6070045101d5611102c28220640c44101e140ca026490b10003024000300050040c54400009045c2d07190784140300b400e00503010703010000300c1c0c0c92003d480000e4040c1c0c4040c010504072007041755204068200da45201e014090440300103203108910380d0150 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 716415656 1250 716414406 716414429
    0x703170714030a1206050f0f13020c0d030e0c2706130f0f0f181202030909150f1002150402120105010b0a03050c0f04120c050909031b0c100f020c0901 66
    0x4d520fa1400c6004040c0181401c80e200c1c40c203c01c3c0b050100b604024a4031404c2c1c810000b203442c40c82c802546038107a84030890200100c42d8200c2d89140c010f00100442d450242d0207100e69860a05181382c115120762980b14458448102c121144c61490300306d1001034800b6900040110440700d40e91071510500e400665075440c0030421511a11010f0210b0303001e29008001c0d50b003408002224000d181c400f41c042e8a0b80010840b58a00524408070b055002c0d01040a5206c50090103211100604048100108200b2255183d040c9040810016080104101c4001507003005030340c58500032000640270303402030002c0d10a0311200c0c2c00c401010700b121402d0300322207825030001c903040f51015031512880d03500045d440b28032442c0802c103074090100e0740110703c56125a00d07400b83e400020052103498030002010090082800c50070003040c4140c03079030800070741d061040203500c402043c12200080c24150b41c0102030090b05602c240a00100c0d07010400108403000c0d44904800511141c807010425402400700d60b1a1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 716416906 1250 716415656 716415677
    0x6090d0f18031704090f0204030503070219050d060f0f0c0813050a050303040b070912110607020f09090c131a06030714030f01060306090504031d0d0b01080d080105030703170714030a 80
    0x328400c1700c9121b032201e0300041c030503c424000914008201c0c1c4019030121a2040148a040714112090200d6000103800000a610302070802840360040c0414180401044c024a50410306040480e01c0d0b0084800c0015001c40c081105003400302d0562400038010b40c01c1d50164101510392a1443c0e106480407900c415500041101c8a40c0c070500c20809030142030000040c1010540383c61100c0040113585178440c10001032100119940c1985410f00380601510900d110310300710704940c0d2030705504464180580c18500c0c0c0d0610800d614800d017208245200f00c41c142203468802400440d4000801e943c082c00a40d0480c0c2a003c030048028601c5286503690400c840e41c140000201a80d075540d2141030350504140500c000aa04400c0a40c1c805c9025081b00c510b000c807800000d080f8021016020784410400c000120b55404007003030341e0b64044a65201d044013640c0e501e00340350f038030845880003401d441c5168070b041640d440c00390020103469010b03c4900c484c58041d800749a086500c864000400304058240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 716418156 1250 716416906 716416919
    0x606010e0603090d050f0714010e01050a18060c0c0f050109212c1201050f06120d030b0f0a060c06050106020106080d14070611040806090d0f18031704 66
    0x210003164190780003415801e10051031541d0b0811100b800d000d010b008101d6203c9907806200f601c1d0840d401013088000b2650307103a5454001c010a0401c41215421708000a15030762042c020f051201444a044400189a031b444003001000440b001004209515031054041407200d540e404560b07009400001d040121b038030300610199140d42032241074600c0a8030311307003080e40c0102104640020b0300851102c0040100500e401c01803c0d1080e15510003060303400140c0703c850540c0f186100d2a14010800030a46400301001369003800c0070241d402d5079000c0500d1a000310b00c2134000000c00702c40a441142d10621480021f04001403903000040002c0c2a4804041408203074021280103010a0000300f02a03402c00c044603071602e000e11801803e005104641c070f5005100d240c11030700d4954008008100b003c040b8007089007103600612841c041e40c8200b0011954501021a10085100c49500c1c0c41005282e559000d0301c900c100c00507100d000086000340040407035403901051520000170a46036599906090 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 716419406 1250 716418156 716418167
    0x906041a040e13030503070e010c1b090e16030210090503030325080f060105070212061003050d0206011206051815190b06090d0c0f1d01091802040b01050405030f060601 74
    0x10f12542140400b100d0300000709411030201ca40051b01450500c074039201003401642c2c1c1e801703040401001138480440c076940f0030610482d501300f51250351500748103160900d10701640d200c26010342403040d0341101c10304100500d460f4015002c0103001d4148031002507500d90020341941c1040300c2640f000050300d1401c000950764202c442d010420075003058000f50424894000b210b14000740b1a41c10300c100040e241e401d542c3c50030a000919074030385084035018608006558144145c4e440100e42e10f1007105600440c00d03001003001030681e181204104c22715106511032001a000203000c1c082001d411a422814202044c080ca0303411520407588100282040001200c003e140440c071100707200e01e040003603403a554444003158050541100c0a184c0340702030303080c42c2c1492500340c1c0c440c0300f0900c20890700054038003411200c020f90107250611007000713aa889000390140c0c1c00c0d03a0340c07144c80980d00521074001440c140c0c0c4a80d010300340600d00f09042a40b1800400e14100f000000300c16582c0c000d40800805680c402e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 716420656 1250 716419406 716419411
    0x606060c02010e120d0302030a0f05010306061418071d191806050603011e1203020a03120c02031606020c1b040b180c07050c0607080c01110a0c0204020906041a040e 72
    0x16580f40a074500100b52045c4c45903c2c5801c040c00305a0000007080e401c8820f908040c014007440c1d030041282d540e51f1f160180c001d188c02c0c0301c3e25816aa1022030b60415140514410a031040c400300b41c00b602c6e903202101102c4061000c4030b20100501e803004071310501d848800d40c40320f0349103501c3c00c00d8007940d050040492200304521440042d80f4201001403115031079030010f5a044500092a80d90fa12498144012502d02ca5801c00c2d0750440c0c03003580030407d1580c001403000ca0280a5100c400541c11a0720125055810307030806680540d000f001205100989100d508410a011340c00050601c0401001c250400d05821041110b01e40c91002400c040c1c40c080c851000317002d8044503102c65030480501004038018009000408200c00815410300b800707005e200b141c0e400d22005010710b503118001e00d41080c2d1a00080e503180d44661802c0b054034036002c000d1049426030402504c2c0c89440b05040e90800c4041e50003804400d400480c14000080c01460214000011050581209445506100110701d000400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 716421906 1250 716420656 716420659
    0x5060a050303040603320417160f1b090c090503071d090102070203030423030114310c0303080a050c0301050f0d0f08130f08030d020a0c0606060c02010e 67
    0x10501088203540000c02c480454245017008100c031079007200c42440b428000c10490360442d5a0084100c00055410f52a521543c42190101040744a0201202840c000c107860b42d41c0c3c00303c820320040e0220740b0750f1040c1d45d640c612542030302c1008503680714001d800c00300907440014174688500104a9450304a0180c0b006488241d0040403818580300c401d01802c0400c0b100a4905490f0308042940b4603029011203e5944c1c01808680d540c654440342d8005d0b0341074010316612710b032446541050072440c060180c403009181c80e00601e22a61514002030900004105164495201c00d2045000340b0502c0b240c441e40c203e025500520202d4590704019000c1c0c503004204806083c9000200040030b030060b42500d054580580f00200b07140f400c0e0003c80d070f042840d5a006491443c4c0340c41075104102108000380f6800698106a01800c0d9841c01d52045001060041c1491a0003d000090b01d0145541c003501d0a80b41a00d042c066030f40b0710340c86040444035286c1180c4002160003000c441956004003404a00100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 716423156 1250 716421906 716421919
    0x170708030c0303070302070203070f0807050f091005011d04060f0608010819060c090914090f0f03030606070606030f1b050a0b070303200d05010807050603101e180c030506 75
    0x1116242c0b42e1200410700005d040c3d011543c8010754408010103070181030481c00411100380c640c0c0301030380c4e200b10310301c5550311070012a000041d01c1d003080c1e81a5401038a61400078602c0600740401560204403000401440c40c00b03c3c0e0b02d009182e03649009600061500303421040380c10f42426001000c8a50582203901958030104002c0001c802440c8260081c0d600100000f480202c1c508048401d42d907581c0c05184a18180540d107103844104410b010700a034614811681c0b500791a001c119111024944070240300e40044c400900700307007444002030443d41e210300700c0003882ea07440303a40b840d500003030440c800e6864006681d00c3da24501d20142043d000b401044500c0040e40c0d00e064800406407064140080c105912211a40c03070b032400d42c00f14442c0e4010150040e41e140c0404821010045c08240305201280c4030b040e00004290800504480c09000c8031003141e40c0e43c0f41080c1c0513081c1c0340902d00020a500e1911600050b252000d243c25000941e03401c4d90204040300601d80c0103007511005170901d4421003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 716424406 1250 716423156 716423167
    0x6050a0c0c0506011712030c0c0f010e07030206090301090212030d29060a0306170d1407020108040f11030a03051809010f09110d0c05030702120403080a05030c0d0617070803 76
    0x1c42c0041c8143c1150213004541c00e510060980c05414641100300f24049a403000c41405892904c6001030200002c07100219941c0072a40d002540c01e88030340c04025a45c40d004514144003504211008202520000d0f00100e019500c0b80d0100f03078079032010030845602d60000324181075803040301c0c014540c102640c0d05501c41440071344071442c00d810383e11000d028480c4030002f4502d40d002d030103504a800106402034400c980759841d18011626001180380010009010018803002200d04a09680040307806948504440e919961768007840010340d4400e4a0030182c0ba0490242a030342001241d51052095a51a03103a40398046e507070101d01600d00ba21071281e0810380c0140700c50740f170301045d00d0212111803001080070601c5101104092143c1ca414428603400c044548800c550407100441c0a124950708842903400d64800540381030080d400018180241080802c495510a030040d40e08250b04220f014542001d041401d812240d040e0b1081d00d189401ca0340b11010100140146001000114080e500c1e15 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 716425656 1250 716424406 716424413
    0x90a1a10050103050a18030e13020c0d05071401180c1203020d1b150e060f16050901050421050105090a03050d0513120207050907031a0108041502040306050a0c0c 71
    0x41500d8014581050b540350000385407544a6000032501403a900940a01d80b4201d09000f0100514403428078060000803800070342241c0b8030310071140c0e1600b41c20050119294980c100702d81c00d6000755016280800c6007007c1414124081c445d0760341e2303108091503501317030b50034240380180002856500c8400b0420f030a04070400840c2c0c0108901040510340d1810000c2070700c1902d58800c24000700303003000d02a10078000b020950049280d0000003a5482103003103840e1551107030401003102200b155491007a01c1c0c200030325000e0134080c001400701c0c2101410414102074a0b80141e00540100380810811070090044080c01c0c00b5003031103281e0304054010b0180400d074030345880c090041e210b41200e102e02c0c181d441340000c411141e412070302040a5030110541c0d40c44000400000d68406c2207019061081c001040401d08070f0b40070707204a1100700d00c90312580320445420301c01581c0c40000104166400910f0b5041401041235a00c01880513520800d40010b0318108452074100302c80300348400000b44018194030300b010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 716426906 1250 716425656 716425681
    0x30b0402031e0a0f0e0307051b030a060e010b04020f070c080106060e12030c190c050307050a180605040e0d0905060705060c0d0906020412110928020909090a1a 70
    0x481c5060102c02d4040e03103860307801000a010070300c0c0d188001d03454203408125059021008220480c0030310101c0b12851041c0000006001c00c000c030480c1d0650060347c1ca50000746080d0029410310010100010b502c0784003401040c01e0741e001c07512805601400080e084200b106c0d1015001c080c107a43d100800c440350034080c000d00000785100c3d405105092400c60822500c0c01001202c00c80080082612401c02d0140d0102d400005805401c880701e052090021540d0708001030188103c41c0003c2c01c03030903440c0c1707844145030100041c0c12402d003c05450b00004034483d00c40e8001c509900841800914081c80c00c2c00005291580e00e4128a00c80c803001c0000d0f40100310000391558006025228860343c50208021310790080021844c01003500f4004640007070021040410440600e0062401000c084048030410006135800c484180c01c03401e40400445c10f00d500f0454450b40740e801c0e0f480061030304410800003240210100c0e07000c061075221142400800200d858241c9031919000910407007410300c11840b804 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 716428156 1250 716426906 716426941
    0xb0901140108030a0c05010b060a050408070614030403032f03070e040605060702040e0a061113150801140105040305030304120f0221070309050603071d030c01080c07031e020a03030b040203 83
    0x17004038080c50001441000e500a40c00781900400541d501e61003004090101e8109102d0f140c0d883c0950640003401d1390081a00565030549a44405e20b56036455130141d0080503041c3c2500e0304803028042411004000c1270300c400c01d10041c84069622881c110500428001b140a0341a01681c1054001c001985614054507851a0704840114144407284605807810341c0703566000d01301904049814840303084100050051026040706843c8913501c55038840030000d0403a074040700140110004012f0b80a09016002c0840e4051601514190740c94a4041c5590000e54007960b5509050022554880e0400801c0d180c192041c0040c0c01c1d45408007808610f4044441d44a0711607c6000440104240c4681c2000d8090180100b1030745e164200500c001b02034605040c4000301c02c1003200c1d404601440c0003d02c410356040c050f0b40d085440e40e1340c03880042c6150441d810482c2070116090400c41d86611008901c41d119016078014051141a410018103440146159034010761041040c40b1005004405141 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 716429406 1250 716428156 716428177
    0xa0212010e0616031103070f030c0f080610050418020c0c030d05040608060a05150723120c0a061b0e150a113c0d08060d1406040b090114010803 63
    0x50f1041d007054019400341c1a000640c9045200003c00c0000f0f03660000e81a21194071035540400a110042100b80e07a40c902e0009104089024440001e600d8901b400b10000020820301d0281c1c203069540c42d02c4043c216070802c0b45208070750041103408000e00100701030071559204400900001b007900b1000b8001348914004c000c01c11102030300207041a1a035070301030001410f0140644c0518031803c14403000d2138200070401c50740381200301803e020607884210400d0b8292a100d0141500014589a0328810740c045003c0b07400e54069462044041103080c070035000102c803408081240d400200400400f28045d03112405d11404100c210310000131204000e540080c06942441005440d07000061894030241d88402c0805031041e0fa81c044881c1348000b08a4484c03843c84896540542f10200c40984400e41500001e0000b00030100103180f03498040e800d8a000c034062074000741d030040030003402800d0040c00c98094130410810402d2000c90030f800d11484043c504800300c3c003485541001c0030540c4a204044070034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 716430656 1250 716429406 716429431
    0x1903081303090506030112031b0c05010c03030b0a03051606020607050d0b0111070902190e1e12070902190206280f020327030c0703030c11030f0a0212010e06 69
    0x140400d03000b0002d0801421008001c941c8940c0d4031404145e00200a00044000a25040344007941e81c0d038141110000c65440020303600150304000c01100c513820711000960400d52244a00089501c440c0c0b5503a004e1401180a801c0c064131145080d10409504c0c1c2c07007181190301c00001c100321150702000307460411181200105050101d800100e5003c1341e03c0c80c10500300d0007501c0c0f000031010f0007580140030704000c1050f054408074601d00143c800e60102c4030301c641c012803052a0110440d038210b11a070403048004101e118110310008000d8078100071070300074012103540044c9007000d0000784200e03034003002041e20042c0704d1071170100c072100e0a4021030101d01c1910141511000c0300c0101c02d0b044000b449484210854582c80d001c03460005000812450701c0841d070031406c4125032004044110780e205001c0400411605245640071a030480396a8000d40da50880c2c018507031801d0f40c0070300082d1340c1205240014203041d030050041185170003241046580c2d03a0716205003646d40e4100868815407212408000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 716431906 1250 716430656 716430691
    0x3090302040c170f040b10080a08030a2004180209030a0308220b010312080c0301170c06070807021503012132010e031303200a090b03190308 62
    0x50343ca024240000c01409503016080201040d02102d6a0388568060004194181c403000b40340c2414400901078025190003800c801008180203c0066401c0040d00300300040c07030083c6006081d0314940c402091034515270001010860401480448220421051421403605000c140000e03510540050010180982800081e040c41d0704e0700c081c5000721407840403094107820700d80781051107104240001ca034040031403240540800d00c07035500d8510950340440a5841c59007840c01d21410030b200c5c07480b82d079850f20624501a400f0f4036020040c00c0340c14490301030030b82c0300c449507c10014040100b420301030030803005000400130035542020213842d5130540800001e0b4404a420130214281c0c4446082c0b180c1c0c54400140d40003081d03286900c00c1036190710070003080341007a0b9402564492040b00c000f003000d03c1c4441024008a80e83c1080600c844034244404054042c4500214800c101c081e417001e51040d65583e40a1001d040a00018101405c003041413807000721141d601070b00440c0c014100c8010030001d4001d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 716433156 1250 716431906 716431931
    0x10b0f09070207090e0709060801020a021e030c0a030801080f0d0207090b040209040c09081504120806030115180b0d021503041a130c09050f06101b15050f040309030204 74
    0x76140a0101d44c402407005041d03504031560741c0c06070b03442144111450100000b5114030103200740c41001c54031307074060090400401090304120240400c05055070108101011102d842040085410362190701d840d07440d5850514542e0a2a61802d060300040c1c004916160743c8650204506066400c1d40c50002001451040450001e004c0c02c1c030704039013041c81c040000e111a504042c030503080b10307110400c07602c0c1c40c90995002c8040c0c8c0c0090303d008010401d4501526070103800b80e0503441d4010006800000d0007415401441281c01150b80000158000f850b48040424a1340c010402c01400c20b64045e508018203074041201480c1c0c0030241a0100e90100100d0208915515518400303921080d010700541480104400101101c0720700711080e1030305900019184020707000781c0d4403030240009004d601d552040c0600940c4810050303254204003800d28400604010f42c030340300e14035a02415044105902c206481c0c0d00301c1d80c014040c44003210040302044002503009a0150640c1d50607034001c503006982e440c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 716434406 1250 716433156 716433163
    0x71b030f110106051314100e0121020612010512070f09050414060408040914040510050a0b030f0c1302040510030e01060f0e0f0c0c030703081312050a11010b0f090702 73
    0xb04005d80c8041050b44280c030103241c9400c14080e02072a014150403640b503002c0f10f90301d11106ca02c40c0070201034514004001461000c0c890b14110851a0064885100c480d07001982c1940151006001851014010301441c24420f010a2001e15844000d00b007036030070700340e4854050380c5c80c2c8580002d4a0701d81000070100101001d1000508100c901106c42509003840c003001c1a030010302513000500d141c80302c1046100103034090140a43d03000000b92103800503000411340a400010324102e216502c3c0d0b40c554605440400030210200d03030a401a00c108003140080042c202140d0b90a84c452500600043c05550f07104103500ca010400f504000032001080141c05000d850305078089a0492001900003a0800e600b0110030b101d50b0f031410025603165030704044100c4a015160300c1c0510b0358014030000000900a55880340c2042822847e4100506c0907070302c51b10702e480d03c50b200e0000110b0100e0744914050f081000900098030060090000483c00b50111318154000e01e0710600c140440e0001c12000d074001d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 716435656 1250 716434406 716434409
    0xf0405150403121205060103020403030e06092e080a140c13150804052509111204050c0a1401020307030c0813082103010e040b0402130212071b030f110106 68
    0x4502c165103d1294072000d81000080c030710b0b141c192802d00b000140d59621078800ca42c20390b940760311500301c140c02e94002d11501d0741143c2680b642200703070b0f007003c80f1100c003c0c3da4404810710402d1111058100e11500018600c0710058031389800d603420048007005001e041d890032a03100c99507a0400d921038400c2001036820359807a6000503080710719000800e141c1340c0d00100040c8110300803003c0f00c104500030860344a40b01d4034150003681d42d000c1c03044140410b02003a0405030540080c05811400c01c241c2a0340f0110702881a04d044034148d1100340320340702c0c2e414001e5070f1a00070101c58180346004d51003440041d45a20558030001c0030860100080400c0115441c1680e86214045292240180d02c58400541d030b80a00c81c268003450b1202ca0b10341040c28030040450341600c0c030749168600c01c0c0d211035440c0324010074081d0040380c0c0501d000700320042c10318403403014007203513100002840d8083c10b0014024203520500001c500d0480e40354038007640805e4019682101080c120b01d0b00300c0380c694034400c010340101846d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 716436906 1250 716435656 716435663
    0x180a080a11030a08070f0b25030c030e160302041521020604080a0b010806160909090606080a0602040510052802120a03020c060c040f15050d0509030705010506060f0405150403 77
    0x708041040c04881d50903602d581d4851f2182203050703100e46008650040503450b0a21891820040843c05180310381c0021001c2142d600380415100240c43c009800c0a40c000c504c17150700d4014040800662400c1d0044020144003010854459400e141810003100c98a1400c8500028500940011902c41d0002c03500106114020385403a90302901d01034402143c01e11480649115950220361402c10080401000220760b07101c000e00c040c5809900c1c0054007020405640184c2d6410000401070424001c501c2450301c074410069841d400e00b420400300c404244860010040c00703010818154200349200641c00d0030b12801d00307184140d2103604030f10700300082020103a02c14011070799401454154016201410444080c0c40d500d039200080381015004500c030f02c0a5000001400300b000080090322107008104e140340c241d1522204035441002e0300d200b0303516600c555000246000500034284211600500121500c51800121141d07041d1140580c1c010688101d80084020720209014822140115031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 716438156 1250 716436906 716436923
    0x8070503041511120c03090c0f0d0b0718151b17040b090a120305340807060c020c130e01060315141e180a0c0b180a080a11030a 56
    0x440c030500d00c21600a601072401a011013030105d854101801d080d6842070b10480c0c01802141c840f0400c021032200c0d036000c00c40d00882208400004214000d2129228922031344804091500c05550307000003428540c80003c03420500d08051406503403011002182d40300500c1c00c04d04ca06010b0400302e05003944481e641507054000940003038002000700141c5181c2e003040b65141200c0d0794401401e96100d1701450700400194080080c88280c101c4c0c00901e5100d031b0200c5240004101034450740e02c507500c1c2c1420040e030340d051000c1200810080c26004218600c181c610162109000400214603190103540c907594030305494000b6450908400d500c01d100450708000c5141c0c0801c00c0703a00c22002002504130340c1c030ba46e002070400a081e0f45041004040702218080302130819a4481004141071240c03c840c44d8580e020350f6030b000000c6082c00e0701b0703203028203801c60445030348100222104001c10300c400705090082000080401c0f0740440810003849071900250800d03444050700d000203007069145c0000400d800c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 716439406 1250 716438156 716438171
    0x50607110c030a030801050f03070b12090f150109060b120601140d1811060304170d0b091008010e0c011d0d1509031d060306010c0c05030f16090b01080705030415 71
    0x11750000c2c034203040320710544540c004180208140350701c6a0890007101158070302000000b4036642d00241003544101c0c80001d8907403081c1401c20142c209000743d01a40303403003095040103000d0980d142c8100001450303a400c3d95460819041c03c04910707000020a01e506000744414481d603d80285000c03079031080c0c2c0c001c6e0104802c1c0c138404111040d03841d00c040b090700c002c50714100711106802c0c50801c1764002c2ea041400040c44903109450031049a229410b030f2030794286c0743c20070981152148000903000fa026000300100306c605203d000340c02c454040c0707464000d580c13005084220607604445002100e0003090642d01d188215103010640c50010154024007203503480d01c04543d55036184d030040c03402601c01d9440151040c1e041c09500c80d140d004030b021a900c02d038100003040566000e010f0802020f441000025a403d5446c00080e05207400300545c080944c001515840c0080d541c0e4411401403c0380d404108014454000001e000050013001d030030034800004080740c28005000fa040b25941d08000e8184500e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 716440656 1250 716439406 716439413
    0x1e01090b0d0e010b0f0303042c070309050c150a0503100f06050d06050901051507030309050303130515040c031704091a010f030e0c040b1c05010b0a12050607110c030a 73
    0x306004a00c1c103038a5464007413141443d00d4185020145014024010341c105401d09440300c0c807008a030841c9442c025904540d072403840340c02c203001d944241c545450000b906400c41c10702500b030000c22142603100b0625600c40b0090102d06030180d5100d0400c81c40c000761a69240d41c142e80450031107400c4000340140464000443c664020010488a0492003045c031000d5a00c4003444003a583c28000d055003d014610740380000d007449005401402d00070b181c003083e00311040c0c0f1280c1c01c0d40e0040d91b10050158032004004140082040500040d0b40009012403062030721341c0310a4032001aa0200408440011140c05005640c000c145c0f0060403204800300040044001c40c49460b0303216900c083d020485001844042c40c0c080d100d4071720440101c0001c2e181c8282d49408000040c10661141a413158544260340b600c4c040500340f10030700a03c10000085d4608440d0304000310b50609034007400c0810403014800c03002900c042881d54103e00a0b0902c006840c00c002e0841c2d0038001011503064041c80782864642c00e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 716441906 1250 716440656 716440661
    0x80c07081606030509030403120215070503011e080a141c172211061e03061809030904050c09041b030b0307030308040803040c1d0a0c0903021e01090b0d 67
    0x10780350a0031510309940d40340c0c01070701030342d600b01c2c0c3c4a8903c0d0001d1001300081044c00900c43c400b202c0130702c166101102c3d01e03000c40c10109000c1e250100090b00100041c0000b4000005007081c200c1c03224400c00c0c02514000c8419a240d00510000300b407035094407081c6030a003804108581104842c0c83c0707910016040c1d800e0090820702c50540c204d207041c2c22400461410070b000441025013101240000850040c1a1900c8008a500207003081c1c00440c10050301c94201001d65030a50007011400e00740d90780c1c0c01c0042c1000400d1494501d40e10704240001e0a00031036050001c2119090102900c02144603525a01c06240c64010142d07060f0b001800c1201c03103030301c100e20301407010850a999202041300500e240305055848900d400001d01050306031010401050032040503691107403140ea0341c4d81c40546c584c980041c01103804816403140c908600244070105240740654400c070611860000403c81c995000242c0c0d0b02c10711490216003ca01c00c1c8051201c4e44620681c0004d008500308a81d92048407a031003200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 716443156 1250 716441906 716441923
    0x50a0909050c122a0406030311070b03060a090f2009120607020d031104120b1603090b01050402030603010902041a01020f070b09010525080703081003080a0507080c0708 74
    0x1414041d40c00034040e0b900d00f0800c064041004070001301540c9641008400c0802619100044056103614110846a44601480c0e001e0340c420360307450040402e8488102c0c500b95680d04003104110040c030400c00c6035190040c00d1002c403181820f0108110f07007411511b8000300100c401241c560810b00c0511482c04000c000100b503050000d40b00741000c01514a800c0e43c58920030b450000c0160082d803000b040141c4a5040000054040d98001e0b1920381da0381c082c400740081e40a0111020313420201049030703524092108408003501414144640e5501d640c40c50700541c014040c0c0c5d031203039a020000c03c007191001d6000ca41100d1703014208014032030265840002d400100b0005600603c01d01164110401010502d04202c0303424102d06801c01100000545098106a04822480e46210282001010141f100ea0b04013801010510358512107410014a8118002c00001194030201c00400001d03003200100d40103002c0a1a1540d02d550f072a2400e03000b03d01c583c0a00702000d1043c1000071960440128000e80f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 716444406 1250 716443156 716443163
    0x40305011514010207210c081603051506060d0f14040503040503010c1133070509041b080c0d1119081f060f090801020307081021110a050a0909 63
    0x1c1c21a206001217940e11001c0c02150395040c507804003100d10080450794103908900c84c0c2d20040341540c40701d40907860126021001d02c6d080904250070401c3c800c00784640141801000b03600f0740075160140106550307205040e91404580d58890551761460b055500c11500c00c52050403950803420035007003003541c0750058040c2521039482c01c0d00f01e8180c41c0c050406150b040d40000090150454406911852141241e4004600d1b415202c40c0440e0100810074181c40f40240b51101a1100c0c048018001222003800c03501448040c034032080e01c20a50849582035200390303288a05960b40300342c44508800303001003140100d1466004502c680f0700340642c41c2c2d040390f2080c03245e0358807141c0d950f0920644a000010400310360750403000002404010f100381400d0081210505004034000e688050060880c2d004440480001d1400310500c82e0500601068030000e099180e01c49110161200c1b420503084001c0000070101605506200600d490300c000b190001c0400400c0010015954401040646100c11085 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 716445656 1250 716444406 716444429
    0xd24030b0c0d020706150801060e012112181a1b070801110903150f0f0a0b0a060309141204050904060605100507381f0f090e0d02120f0403050115 64
    0xc079501c101480380270100d51150740c0c00c4040c0d9280013003105501c100701d12004440e440400b0800b000c107240e44210102c00340603a80754013800b1000d0308410001d20031a041036036041415840000306440707103020303211240c172400000806a4426040c0918180f1140c7c0401c0c025420241c4040c21034040502038180640160180d42d01d0344400040080100022030303805402d00f030b40c0004905010303981d84580f5881f1040c1000000c0c3c0d00301c0c090003c0c056500b10b9222000003a00c17150045c04002e4040030110282000390010002682007000080440c09103001d4039000d17244020000b001e000540e00104000c00c0040c002d00b981c000c00000041050303008840980d034010017007005000071207140c0d106451003c803040c003100340a401c8201840003c200907241e910440c00c00c10101c00309450011045004200901015070aa45414010000d591340e01b0448503454201183c11110103401046403842c001005443c41ea40700c08106c00c4040c14059600050081d610388a06000d000d410b01c000302003a2610001ea8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 716446906 1250 716445656 716445659
    0xf10050406020f0d0f0f1b29150d0203030702120d0809210306010e040c030c110a0b0105010807020f0d03060512030c0c010e0a05060f0d24030b0c0d02070615 69
    0x816131359496661034400050f041408815000d403192980c1810841c1d68a4400d004c0e041555030300c2c2ca001241130081e541d001010a10820100e0f5114001191400000d400c40321490229440c41403098035180c01c5000e00e02c401c0840045580620450f602075600034180c1d10102c1800301495618200b120140b004111041d0124085000005800044c00f2010030b5206101a0b0301c4000c07121600040e081c1410700c2511075178000680c2d6580030750324140b80c099400180c60507a038040180461500d07900c121b01a044031120380040b0320150100350641e402820002020340710f9003801c03071400d00c0b4822011803502554100c061501d0f40740e00b001084407000c076042c16422040010051700c91043c1e00328407100c0d900019801c14075500031081d03032008400c001c01e2007444030b644901003541c80e40700121240d10702031f001549000f000a0f52168030450304600107800350041c0d41c81011001601507006c040c012a804200040c0104000070440b8080c00580d4410f5407a401140b03040b0000e003202d0a00c04055a01c0d5100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 716448156 1250 716446906 716446933
    0x1110301090b01051905160f05150721020705030c060106020f070e0919081c0b090c03011206090f0609120215160311040308040f18050f150f1005040602 67
    0xda40d02840421860411800c51760402c2c0c6441e0b00000a865604850341c0d04a00850000b1544104142c0139002511010111801d6550b518400a140000344038024140190000084003440500c2d10ba4500040c0d4901944c10803d1031406410340c04d480c0da1041c51b0011a90030390124004d10340c4c1c2c2c3c4000807a01041d486903002200c80400303c9024159a010031401c801d8080b0a0040c000d04c82d010f0340070035242605802e5429152501e1992145503151070300da9440b0981040880140d000700082d0b052415941880d41e80c03171002e401c5600c00f03442c1540300c8102c0c506010200088000140e8801c804020200c1c403441c04900000340190140b0250058038403017085080d0401e90188241c1c00903e0108130b507000c502054000705141c4000e1100d04500740000f03c0000c4100004001405103846240c03030b10380c42d103280c00150b00110b1038003102250801d010700c0402d00074100344580292481c1314000c5130228141c017041d40741000c50300180d40889590702c0030180540201c000c00994285509aa150300c42202 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 716449406 1250 716448156 716448167
    0x2090916090b06030402010305100306290f18070912060506101e0f0201020f1209122a010b0904060f0c02070f0905100b0a031b02060609160c020301110301090b01 71
    0x7002c1036008a010000100103611940c40107a029210540350b607000da880b0344034001121040d05c00c003007844074580134031039202c142e082407020200320072035614406e1400f000104205400032070300c9508281000010074403440c002d03072551015002000103101603950034107000300038000589455000d00d4000c5080a2120310880c9403c507a84041e29111810f00c40e0408120348143c001c0201d002155820b0007603544550300b041c02400c403ca2500300c1c440450070102030b0b560034651000915401c600c401c1025515141103405896201c104058040f1a001101a00d0764003525844010980c0301200f2001c00c000c01600394400d601352100310300200304165440206036602c0199014103900a121070008020604181e040164088681018201a0755880d0060802504a5a9910007003034441c24240c0d00f8114080140340d58004910041080c1d041800c00702c0e01040c000f402903115150030b00b2001101ca4041d207007600320268090f000300721202c1400c0b40302c42d10790801c0c0200c021490911071811615031254 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 716450656 1250 716449406 716449421
    0xf070f0902070507060e1914010801080304031511041503051b1602042a080f1e04030e03190c0302040b040603030512040318091d0d0f1101090209091609 67
    0xf000800d1540d091900540300c0301072100a0644c8000b4240c94540180c0d1850f0104008008104104401c3d51207400094405001601b01c096690307c10301041002c11020f001202c051241d88200140d801003104260b52144501d41151082085401c1100400380d450b43c0418402d40d80200607001b407600c0034204413400d2180000440c0788400e421a00405490240c2c007c0e00402d0740c0c0d8032440c411680c2c8131078018880b41c2d41d200e001c02241141c0d0030011840800412a540010502140811050320000d0b06004090242c80036003005010705c071200da2520100321307030720340d1005c010140000c0c4040f61400030104406070100b00d001c2c41c24000d0720b681e941024000c6100b40c0e07a264507014240507614003040340c1400d0040041d402c001c5c800c0a81e000025030440008054190f0b0320012458200c0b100100045002406a21441d0f600c41c10718220707001ea0000d10b101c1e80704440e151651749080002202c13409001d039200040c0d4000301160601050310b0f0002400c511200d00710300c005209540d100b24840854120 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 716451906 1250 716450656 716450663
    0xf20060f0405130e06040804080d0e1c1704090b0f0303160f08070b01060f1d0123120915131502091c0809031e0d0315080f070f090207 59
    0x9000a00080ca0318046241c240c00c0d01e44000030341003002940c1300d03290082c142ca064452500000d010f000b00b18051054050304103241c1040c4111292060108004072140b820074010141c110f5500d400f003080d182010000c0d65640030700ca5485a4440f13540d1401001d0020010380320302c4400550019a05001c4191080580e801015100d4142151640101900031040840c0d410030100107010014181e444983e000e4842581c07002400d074103140c0d014225002011301e98030710070005030080700c150786e00150100002c815001c11403000342515084420038002e61080e50b8075413045008114800d01e002800c0d510f03560100030300310790640702d0011075114010172000113016024845c0c914940e05060341c00500b012710016203200c400d4040108002010402c1c2842101c2010001991380900c0c03408000d45045030701003e000e11010004400003d03070740e4204481100505440380d04560605030280c003d0341c02440754400307a40c03d002c40325000940b608100d008006042c14032050109840000f40b003a551003c1e070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 716453156 1250 716451906 716451937
    0x702061e011d041707050303150d0b061002071d04051614100903061a04050c04050d12020c10030203072c0108091204080a0204060504020c0304210f2006 67
    0x2a004600c5030b101401082560001c0600084424841d090070050030740360b003c1c6001d5516400c01d0700045800d2032200c400d1510410841c1484004141c1c520701c5550403d40032a000c14107240000000d80c20f0600c1580500e801b1400344090007a514000440301e40b08612880c04d588200d0030180c0001c2e00c2c280103010710649045116086205800c061445100c90710307860a01c0c040d07142c0e413991690150380410040c0c0d80303051102450849a070501c0c2c051107401600d10309806003054144000b244c070002100501070502034400c181c2d242c1e894001d0145c501011800390140c4800842c00c040600a58810340741d16001566254003030070002080700140303109001034802c200200161600440c1c01903030107004080c00380a8000401040807001004000402d8100064800000d8a00421003152070a5201c9802180100710070307804110048201c50981e80742d95948408910604459902c25a8100e0001c0072103001c201c0c124140400305000140c00701d010b0102d4511341c144d0b00c05004c206c0c056040941102103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 716454406 1250 716453156 716453189
    0x40b01020102131403070f080c03011b05070305030a020906370504060c05010f0e0109020103180309030f03020c1903061802091b070f12091d0c0a0c0b0702061e01 71
    0x15034412512000290003806c0f50300407600c0340004199111154081e07442e5906c41902e01e1311608080c00746500d010008125800750780340140c8094454410907000908201c000400501422016810307501c442c900a0500c0380c844040c440e03034030482680b0070066000500112841d1083d44111144080c01110b9035581d2402c00345004400e98403007601217021102d6540350000b402064141e403003481c41915030800003241d8030ba21800098100c0300004d040ac18031030502d6201c1004690090402001c40b540b0841c5555031400504040741400c2030040c007203501c1031510003a091000d20200f42901503074094a0104007c0b0001403c2894904098800942003c00d40700041c119242a01c00508004000ba41d00342c607003c0640d13291643d10039520340c115004100402154410355204011a014282c5000011102c4402c80100000540018040d1007000400074001850340e200c0c480c81001c89900c01444480f07800c1014011b5220042100d459131810a2074111103c407507100b0050038101c4032740c11b143d80c034040c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 716455656 1250 716454406 716454419
    0x1b0f2401060e130209030f0610060201050615070309031e021005070506071808030d050f010f2304060902030a380f0f060d020c0d090b090409030318060902040b0102010213 75
    0xc9030300f000102000c0da401e2100e5407254a062007240d0f525514500503281614118103409410011500310303404580c500400c10501c3d40755400100c07051810512115101c0c00b0300d00e4201c40c055415000104107840b40000c5140301d9140360301c1c0c200e482c0e100700e404000d00d40c40c0410031a4107000e942c1c8094401e600c0b03003011074117260154101e10741c017059440340a004a80c0360715601d071960b80407007a070744180c0e962002003040100141210602400c1c01c40610401070389040c030004040311680801c0011001c0302101e030541c80d62a50f00c07007030091800c010203645030300d003941c41500200240c0041044854000b020340805803401c411854001c85000e00c421109581c0c241400300603082c800903150001c0180c02030260a0740d4a0000d85549280e450016988580090225081074403091046041c031601c80c5082c410b18500c0f03425a21413060035a0700055415107414200e02071318201d011100000ea4840c5030380103010054210034274050003682c092000b4503014004900301d1154101e845090140c8910600c1003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 716456906 1250 716455656 716455669
    0x120a0203041d0f1f05120a0b1005031e031306030b0f030c0a1a0d02030f0115170406020d110a1215270902030d0f0f11030406051b0f2401060e 62
    0x1ca0f1305890310820140c1c41d180420004c0140955090716540f24050940804c83c1070328100340d0203661004510312107807408000c02e41c0e8100f401e002c258061b01d00d4142201d0b0741010003e8a125060000c18840704658920001e0010b2203100896800b81254075070200c281c1c18001951110000060100b00c406450701d80c902252000c402c0c1c0b52441c41004105601c42240d46002440c010301c8030031452072441d4544442410040843e9840c0414868046030803c0045214241d140e40300c2d41002000d40e07118041043e15000f4114610240304500307001c0b0f02c1d000000e13403081d0070a0f02c07450403100800c80c0316507001d100c540509180c82100c00c03004140d032250f19681c1d280303006180404544c45002c10030300c04980c002800c146000c2c1d41d880001e0415141c40d5000d50740009104103021403800d080303081440048034151603120724010001400400151504155a9031000341985105041500d5181c00b140064070303142c0d00660341800700c42010906c90300100da820002c26040303410031780f5040400c06610040c0f014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 716458156 1250 716456906 716456941
    0x3405060315010201060305030301031109010602120a0804060b0306091e16091112040602070204050f0402011e0512011401020c01090e04030f0c0819020615011709120a0203041d0f 78
    0x45548176080040010020405180a18810b209440240c0b00715000d101c441c081c141d102004651240c40f040d541800b0034011a01c1c0b40e03940e4a00001d0300d0380c4078140240548114502c0a030035100d800704020350840c0c0800d003c41080034820418a0b40700c40710080c141d803190f20001e03500d0b58240c80c030010004a0b113954404440300c403840c241c40703050250041c0c507044020412201520050340000350076003145000d11a182d804003100c1c20b03461048c1010b4000805190040300d07040c030754200030300c0d04544480c060010f40f40725000789151400c407507850b18007820701c500d080d2602d40d003d4403070700012425a42c000e04080b8213031070b1070101140c15595161821540b00c0d814035908403d0001035281200480c05d528002d00c4000000c003909180e56045c0388009240c844c1c001c0c12840c1c83c1c00080f10b9601d0790ba0b440295003107162000ca101005035242e0300d1401e418079613142038650300294002004514280c010014108451040c2d510b2400f00702025a0070451441c12203042006d403105400056100111845d60913 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 716459406 1250 716458156 716458159
    0x20f0d02190303110315090a0501030b150a05210c0f01051e0f0c0607020c01050f16141903090905040c06050715060b04030b010902040503070611010e3405060315 71
    0x40c04c1004059103441d6a0b006803440c400141100403249032078201016220b40041e14408200304640c0346490704800382a001c2d003465001c0402c2c007040d06442c3d6035500000d0142c440100b40ca4810300580030403004084000b0700c0703400c9500404400344070a01c0d00e441e40d24501001030b1113440c40c08524018030b0011218114404c282c8150900c0f29818002d1031801800c80161200b00a0500381400072020b4031309030301081c0300740c1040310400507459445240015030f4894640c8640039a051840d62a08400410145c003201d681e078410494000444040c400c0c40122450083d2103641000d0b03144e50f844c40503a14219400341a59034502401c00c0b08031f01c2000244510380c09400311071610000c0c00c02100c259031031383d4001c04824801080a20510140c070211030b004281c521811450b151400340408c2d111806849110140220180c01e8414043c080d040503005084036019500b194142c0c03441959120340e6041200004002c4448c0500150142c11305403090f6407000b0b052034112b0342c1d11101c640b1544407155619 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 716460656 1250 716459406 716459411
    0x9050103030c0831091d0d05071511070311060610110309040f0b0a08010e0c0907140a050a0e040513080901110115031b0b090f06091201050601020f0d02190303 70
    0x142040403139940f41c12004aa0f43c546100840d1420100205407182d144051504020400080c00705840024080e10b80d0003150400d19102c29890400151140c0b0102146294038140100c89850350b1407600200001d5200c0c1e11800d5003d5000a405583c0304001c84100d074004c103080c8041c1d9040341c0510143c180003002da00c122881c100084020038160360454800d40451600c900307120409140040c4000d0107040ea803402040020803040000703a0b2920703142003550150380e40f64003180d0310521540b925241c102e40b0102441d80d8607120840145160312111142d40041c1503036010741c125140c01d004c0c00e4003490504103c6498245640c0b1402510742c0061540d5060000302070106002a50078054401d5500c020340c05c0e0f0200b94554180306402d400c041040001c00380044005100030400070703040e40d4140d482500c0f154443c101100204000d88034280e030084c1d00c0152110041c0c0164015040244646001c0c0e0035603902c09400703071200350b480c80700303881100241c0c11154074140c01740381416a00c00024000e1130017 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 716461906 1250 716460656 716460697
    0x16081617041509030f08090a0206030411030c1c120809030a03270b010e070305090319030204091103100509060d0b0c0d140f0708012714070c0b0109050103030c08 71
    0x80b04440380380d41c0450104000c03074081c03101650000c240c140e0100e202d9000d03019100240e40007456502c0000c0004000b00c400256405c0076031410800f00caa071400c007401e00d241138000359070a81010100400c0460f1040301e102c6117442e1300c038070a914881c040d0140800850404070401802ea0140840b140003492017142c8542c521081551401c1c0f440c0900e010b103a00c91859414944200e4072040000c141701c0605040006002c4c13014000000c0391080001c40b070b03001450844a0368220b001e8841c3e0707840025a80c1c06c0170b0341e2382d460300f890324001c5004005a1035600c9155940e0030078441c00c00001c60303500e03a101d0b20341200440031445148038180d00c030b8009103825240a400b0a500e404417a201060007060720180010480701240302c1c2002500140b82d800d100e0380561500e6081c03000809400200070310450899900c0418540740e4114403842200490003c20b20700d001840104440d08000b02958801d11f5400005014407191059505030b80e0103039201e03482d02500d40c954012551185034002e9072400103006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 716463156 1250 716461906 716461943
    0x105190c08040902130e0702031b150406141305070506091207080604030f02030c060601050c0a0b1807060302090f151308010c0f0e0a15050903061608161704 69
    0x80c4050f0078202c400588542114240d8a8000541d4006803200c84130b0400340308200b80c0000507a1682038001c4900020505420044c1d81407400e480c0e0400100b40105090004101540c0c00001c601d01d654800c1c107080c2c0c0e60f103110074000d40c4120380300601a60400101031190781400302c02004092000b4019614180035544040d01d000400d0f80b2010b00f9070008414402090350003102c03183c501003d0702c011810610324200785502c0703078006009181031080006414020380024403542040303c1e0070810000251800328505940000c40da8070100b02801034000105070b41c0c0c0a8802d4a4849001408828127414000c007401100080c000100d00303c02801d01214407110706010392080940040f40010859031200c0001421107441c0c0c40d0702d0800c5c40216010501c25499045100342141c9010500c224490740200d0207075442d2192407801d03030301030042c5800c0140c5940b00122380c00e000d038110741d0307103125a590303681c9161055480c18405100280000c1c0da422200903140f410079030043c0c0a07a0a05c0003003007aa80 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 716464406 1250 716463156 716463173
    0x1a2503020a02011d0f07050d08030a18060212062d042310050f0a060c02010305040c090903270501140c03131d01080d0c080d09020d080403060c030207020105190c 71
    0x41d2001c0c00d903c0f117040d01e03012410500130240108401e403101c2c13241c028140d0301e0f99424000140010b0140c0e655949400700203903d03041000600f50082e000b15960002800180850082101d20f94012565414110344000e031000c2850f94040c916145440240b004601300000f8207910300b010705000150480300c00706c0c0c2c0300c0c80620034003a045592081407550b2900302803058400c10881440e03c9161485010055190020003058240740d091030001780c69039031480c04401c60305243c0c01c0180010700c1e00f00c0c1101010f8000d410303400510074009410000d100d9130381208140c0540c1d03000e881d00043ea03a40c0c10584280140019106420250007502c0c10845020700e46202104180d003d00160300d4040c0406000c944541000e03800340a100d00030301040b01c00c1c0b18028026228481009242c1d4400188250320091984c2c011255142e005000004010300303824042c085412900094601070f2802da03004501500a108603010390341d06859190425540d030341810398811074000f00c034042c0403500381000c00166080307 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 716465656 1250 716464406 716464451
    0x9091d010509030a0905010309020108010303031503080f040801050a06030c030b0406140a0c0e01300912031b0c05070b070303020904090309081207080f091c1a2503020a0201 76
    0x80003c40c2c542204a00041220000d80d00c81ca0505244c2042100540d9104a105055176054100807c140b01007000d40f50500c24650700107029084081903940314504c2c188010011100100028041c644415a111040b2400c071710004110b9032040800304000303400903222030b1340b19008003000603440c0b10718544007400350821901c00c0081990f075041c003002a030b04810131901c0484203107071800c4a412000c0c020651149880303070341548040d40031005e0307460780116000306048603407000f841c524004280e100038003d09080544888100300300116407100c0ea1080f410400707510b0300b000051203460700e08120070010b41d0242005404264003040401c0c195111030107102c403641e01c281d80d6945040d20389011076013072200b419003485142d8410040e100c0414400c0040e101001d50704418559541511400141040715941070780d0301800402c41c0007005c0c001c160b000460b0300301c0c28001400b8a6501d00d11410003510400d81c00140c02035540440c811030078866800b801081d1200d000000b514140114800b008071540b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 716466906 1250 716465656 716465671
    0x307031b0507030801050108061c08090a120503090112060503011d0d0f05030a1a0d060506040f140f0a061e0f0803030c070f02060f0301090902150a09091d0105 70
    0x54030a604150a0010303484096401640340103820034206030b81c01840792206128590400ca24075010605513550b500a20219440707064500811084900c2d04c50150340042c24031900c101d1044000003000f4000c07441c8a483c603548a0095443d08506200540e00c00180d20f0806140070790340c14000c10b040c0c800340b240c66010441c00500409110404901038034000c440c001882c100310400e401d0628a9410001396500003d045001144440e800000527049400c0d00549503030006040400300309001c44c075884140107280544050110180780c1c0e40d0181903815407402e0380000d410042c00202c04d02c0c2c245466641005005801242d07441d60b401981d1800742001d50b82d80708191103240104101840e551081d4024040c00c4043c50a6103011014500c0c203004448000d018035941c0760b00b074001c42d81c0311011191f07088250a012516543c4440010001b4070314444224040d070710030143d610415151f84141d400312421035480001d4241007102c0c103006450104040b0140084100c07448024050030302a15100d0f040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 716468156 1250 716466906 716466911
    0x110403050c10091401321c180809042c07050a0305120f04090603120806010305040b0118060315021201060c080301091805070b0405010207091104060c17030703 70
    0x1100c070200810140038080180901100b000c081000c0030f01c101049248002c2401c0814440541101508010001c903171841464241c10411190b44405e00b40944602984486880d0302c8040305005081120390802030500a41d264102076030015607168010181c980300900046030032520681c03e0301118114012840c1c050703200c214242c0500104000039001031104a0381c0c4801107140d6182e03591030320400f0b1540c00382e0050024264508290600480b4000c01c0000030420002e40d490808840000b258101c00000809210108203298802d000e2280940d0704003412070056464444040034074101d0810380030b1042d40321580000407074807410001c4c0035800090320160740e8080104454241c80b40c141c2094080c4035545c141c400108100d139044d00d040d101481000140580340380c3e07110348200809100141a40b240042c00314801c1d806801920845a083c0c007220521030311201c00300305541c072818240c00e05540a1104003c500d1040c540d0305442409141c1d454102d01c0303a9494001507901c120342c0b460200381c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 716469406 1250 716468156 716468173
    0x150210092307090b0411040510020a12021f1b0315180515030f030702210303040c0e010501030c02120a091205010605090c0304020904021905030a060f06080d120c0311040305 76
    0x482d4054030a9003081100c0800c19035021140c402d00c40c1c02a0702405003e1181201c272442a035000308003101e005500a0031000c448000d008000303642d5142d9810050001102d100c1d48603907a0500e000305d1108090100b0156046052108120002d10900d001e00e15400000b2900151040c2a110f9002c1030140b0404042140d00e8503000407141803041c400201d000f40c1c4019540428014044150340705694122084011340c41800d0580c900340300500891461030000006100800415110400c2200e01100034920745a03a60401901100c080840c8400580c01400a40c40006804d000078440009070b82000360702651525203200c43d104100e442200c4582d5a100c041c40145425070340141e009018542c4c1c1c0f0b19600c0d05602141c07600c000500000d008150603d041c50551008000c510301a090103002c41700c07000200c3c14800081c161180e5010102480d251001c82c080c0c0000c180c1c00c88c1643c0c40e0320f8041c0b044440c03151410040903240401c008040c0e880400341e5403042034500070002940a00010031811 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 716470656 1250 716469406 716469419
    0x10f1d13021b3703050d060b03011d2d0c040e04050f0709060605180d060c0c0309080d0228150b10210c0c08030403020d09150210092307 60
    0x5400c0e401d2050104030f070342421840000b0400d60100d400340c0d4940303410754a0f000100d680d040a801c00c1e800000301c003880440007144d907038448540d0312200c465109d42a013068841501105002c0220210342e060000340c6041c800f1740082d1010141e0700044080003c40c03600b0741d00d00e007401c4551400e0310b040307445800041c00002d0000b4200100d80c0035008a14080020724506003001d400e5105281a01c0550100114000340d1039944042c21110160050300038001c020a488000b005659102000c0b004600c00e803030013060701c042c0012a00d1607018660028180c2c000045250b8500f00100010f4038180707a00144154001003070319000303580b0715010341340204600a10034100441181801d00a901b0071182c5607091420002c0403604650b05028010005612612031000316109c4411950242114000100303100400d0b030300040e02440400d56607645814035864901003421086407002d0fa900580c04101d00341900807050344601851407080a8010601c1d454840c2034803081e9010340c410015130803113101082203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 716471906 1250 716470656 716470693
    0x120b1003330503061f120602160b271513050f010204060305061009031205070c0e0711030a08070f050c0a05100e01090816020f0603090606010f1d13021b 67
    0x1014801c3d0f50340390b072042e440c0d0f20030984241b0030760090b8140c20306014240f11941d81101e01450200154902c0b5401c6414801840f40068903030014441c40501c104401e04040c0101c04003580240300507001c01180010b100c5820840a00021420307091075060800050b401c0040502e003105c980c00142c2c5440ca0000090110b0394010102d41c0950a5025100d10240c1e000c1e540b101500e03402102c2c903603c8944810211031500a040000300100b080c4000426080303d00c00c1d9552242403140d80310124010750400403a01c9016a01c0100b01142d05400420504c41c020070000c0904035280c0f0b03090f41400d016803051403906900401c1654160021185408041024011400750280030b000a00c91045c2690f560310780b5116050403183d49859141310b0340115580c06002c40090b640084c0303440d84a090010703115440352400e494290101c0d07c88042040228052004011500880c400c100c5510410340b0602040c0700c00305da11035071a03603801c01c14016000c00d908420290350320f00400400e07503a4000c100c046007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 716473156 1250 716471906 716471911
    0x20c150f060916050d0f0b0d05100f021204140a080d0e120301061709010605040905060106180f090e1c0c0b0c0301080d051b1c120b100333050306 64
    0x80724403c0d01c00035084542080894108285408002644250266104008110500c056503003c0c602c15840010b000d0000342c00d10002012010401215000b401c81c007080784200103150741c0901c1e0701030001e804a02d005d0800c1415525a2081d992107a9090344c4400701030344a21000c1d5200c641e54201c03441810310410030603a803010041d0005155504120f0003412803003844010440344d8800e80300080c1071413001c4d004500141009407042c4140021445d20503140d140034050140000c000f032020340c01c81c0c09010024012143e800c40039842c1141401752100290080c01d82d0010603209155944101400c61009001c151296a683c0300700784190703192101214801611000e11a0010302c0180715240780400c070036074491150f040043c0e45440c403100001890b1440d40488025014010680007004109035000400c4015a40e4200001c03075031034542c2c400c90b560310304410f400442c3c025240803140e00a81c070410b02070703842105040c2080081c02066034503090002d071320410f0141e2840d04000f2800d0410140c0d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 716474406 1250 716473156 716473171
    0x1e080712060e270f060a0b030f06040311160b300109020408070603090b01060e120d180b1224060301080a030305060d0b0f040609080a020c0307120213020c150f0609 72
    0x136510000a03601d5645a00c041d000d4030000703950700f600c8006550100145044240c00030140c5106e4a824100600b6080c0074555940d00d900600944203590421800080c081d52030900884e82440d00300c403803c152019079103810782020a02002c845801d4150b03240b0031030003060f00440150380d903800c00c0c0c0980c2c20a515a4000403c1c0341c240b001140002d2034170426641541c1d10782c82c1c61950f0824210006106003c1c50a03034480a0189440ca2052554803400510911300b016038082c1b0140d698805401130751045018082d950410180411619000d01000320b1041c080b01c0b04544540c1ca28000090b071591003a4020302c0682e01c100311240403d9018040c0e0703035100d80111505403009903136481c0c141340080300504405524019070001820000e044d800348403415044060740b503c2c0c25003150701940c1e9054401d81c42c0d101e0300c01c61000003031100c0107001030015541d0141010902044068030f0310041c1d081221042540e0041c001280000e0f0b03401a02140b240c88230b034080d8070311418100e06003c1108400351090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 716475656 1250 716474406 716474413
    0x70f05010e030a090b030a022a061003150507050919030515010807060e221d031305040905030d0e0604030e0613061d040c0c031e080712060e27 63
    0x2030740381c54100754440c007101c6003030803600d691f5554200e254000b4454a9107103010840c0207912840460a42c180440705258400115041501d4542250394043c525102c01003214040c41001111822140c110340d4100e03810341459401c006041d400241c03000030a50440a641200d804100144101080160f45941e41c10729121015410600000d8035246140101c5043c0034814101c407080d0744504c100e103042445c410080014585c020800035024107201400074007a0800d8403050041c1d14404011699411150b403c808620303403602080c4009007060b500b0950740d600041c455102150303c540900f690304844400500341c9494a4600a0900305410040034020b1506024503500740070341c444080107484060130450b1a00e032840201c20142801c06429035000b07410801102e905a40000130952950300c251285c0400c19100050480c0b950349501010000807030600200c1d0f091030061800090201d41100302003500e40d102c640d0141c064005031040d0201401130b0580a034901084100142003420442c0034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 716476906 1250 716475656 716475667
    0x915020f16030804060807050904060e06030d0825170a051f05130b040207050709020a0201110702031b12010c0903030e0906032508100b09100e0406090314070f05010e03 74
    0x4514113030040303008520502a400020480c9203008501f9074441010040c01400920740310254000e0305881528018080e209001b90b403100180180c20301d03441140f0480e09041c0540740d802c040108040034814100034030030154440e180d40c030340340c40c02144103000e004c2010541c0d08007981502603d010000b29502c92030401007080c0460340c6c030100f020203c41043c15000c0303200209000010002c0c41105030050140c07040b1200041c2c0b0582d07a130058041c040282e0002c00145503844a0034600d032260010013540b542211031120040304040300c1e130b5801c00b54050300c030303040418036500c01c1421998060b5460303010074000c91080041560085985002c1a404d030345561443c00d1101c00309580c4e00302c079800000c0703400704440e00a0a60250440b4000109544d808441e503000150310000b0090078849406030103071505d0000924080c10f05100d5034200c880342010059155907a4490302d00404000004400b001005c074003100903401d00c2c40140140c40d004089407500e0740110b20b01b00c1d08480b01041c1ca5007860b01309010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 716478156 1250 716476906 716476913
    0x31207031403250201090201120207081c090b2401090315050703110a0512060910170a0c060f080a060506090d170a080a060909020d0204020a0915020f1603 68
    0x922035204148106402e403030380c070742410484038040d09103a00d2008091001c403d1980684c15003000d08918002c4e281c5000100c140c45914051740700c0c00c080902400820041200d41608a401c4101c0c9080c05900020b0302d00a0340c0c0c2c412089940640304201c8006802e542c020034509001006a801202420042c0c0d4640c6969102000c2c842d00d01160413049a0ba0400900f41c1802504800b141d00709400d080c69036480c103080e001c1c010360000b8015542201200000a40d5420329402590044090108a04d605450800311040c085243c1c641c040440c001d0340c4802001641350781e9484042e100546581205c009014001003005a0042c2034006a43c2403103030400054a40b0000c45000c014291100700c17507100e440c201140285203408500341e2400380000c0f03d24600d43c1c000c0b00c05000399801e450a21120756211045402c0e640340000103540181c0c14203c803401450300794020419081103040410002d9500c0404401d00001d2500840c09a081130000281d00e8000348829444211400b0310303020703000d04546 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 716479406 1250 716478156 716478167
    0x7080d0215040b100e1602071707030b041103030a03050a0e1b10090f09020306030f06060109050f0f0406030b090106080604080a140f0d09020f010c0b0c0328090203120703 75
    0x3000544040d158002144130010300c44003000c09401c0c901c801142c01d091102d00c1d0180c0c070483e00011001402071040110703c1c3c5e00c2040348010340c51421001040981d007191120031000602a00031569203503804814105600d050014140400054400045501e049400f9034161101c2d0766180d180c40d00510351440b110802c08103161440701c01901c03041111000c800d010b5800000c2d0b034000003c0c2c2c4449041c0000c0035885500154480c98003a02658028040c0b05039580d6140410740d48203011503003101040c003c1e403e00034003131180864020301c602400e8188401181c11039002c1e802c00c2e40c1c0007025404012500d0024003a507002408064010706043c40c1030b0721944921f01501c2490700401088503001125280d1600540f40150741052040c1c3c0ea4242c55a04c990041071400c00490140c2402002461158000e000110400d03400040030101a0759000d0301e070240340d200400e207421010819011541c1c0000709050b00d04000094a000600510140105460003843c4820403030600010000800041d6005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 716480656 1250 716479406 716479411
    0xc030f11091e040b0d060506121506090a06030204022d0c0a0f05160b03041704080607031d0d0305010801110f1602030733082404020403020a030507080d0215 69
    0x10b50031502c108080c00041c01411412502c03aa1084035070300d8207814007642d0f9000318004c407000c48800c00340100d401d458648501c0403248040850b0806400203096040451034598001d40002000a680781c40e90b0000c1c0890700081d4000c51144021003103141e0702c400c4e0080c02c121035400b200c80f45040c5280c1104407552000e4003080140030300020040f000811a0030442d181d10140d520f0075403281c60f526680c541505400071181910090b0851041400c6003600000710380545000c1d4018000720743d1542015030107412511550800003807544c0305080d03041d0040c407441d1882a059500030506501d000d60781425155400e002480d41c2e40208010b00c0b010f83d11408442c244c40701841c2e24450b00b00309000081c2000c0c000e0340b05480765280c0306505504c4070819854801c2c0e08010030320008003d201703c03c00f2a101541200c2c024080302032203101000c02104170000500b440d50060000d80b4082e2254080751014420b5481101e0541c03222000780b1001c00140590b1080e40c6c01403009080d601d456411654104502 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 716481906 1250 716480656 716480689
    0x50603120c1908120108030c010c1b03080618070309060b041a120f0601061e030603020a092c0312070f1407050a0605101a040f26010c030f1109 63
    0x40c20b00b8a4204401d40d0142d0780c00e078903800c0502886681d00e0b040607881c0e612002e0614950351070113a044102500174240c0b411081600b1580c00c0008146a0301a5030000c8040c11040c2c0c01007581e42e03c1074104901d858580d100b640d0560300441c0064051400e4400d0b25200801d03140300f80e040103120003507034480410b110003c000440307880b018140000c140342e00b440c01d96600f03164031307006030b000202d0380a400c101600045a41447e002c540040c2d02c0ca4118121005400000d6100d402d01c0400c010020440d0042d11406103000042070b11400003140907511042c000d05a0b105581003c141120070104020946030700c080c940c2842e00c0c056130030a0300100f0900304003441111540c008a044018480100001148180e00800030400c038140780c0000c03030b030800d0a40704914418020007800010520740000741c0381110383c070344041c0044a052030345001e0b44400ba5480e1039000e084180c904421003500340541e040f006a03640340001c0b6005201c400c40c5c155855a07540e0440c0040c204a80c016035241c8440c0100407466 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 716483156 1250 716481906 716481943
    0x606090b190e120729121803040509040b01031a0f1b0c15010f080c030a02130e1c08010b270415080606031015031e0f06050603120c 58
    0x390000007a00341c803603e04480d1540c828440d012500c20401401000d4040240b50354004a40b80090006214414000d0f100b4124000001182e0081403050040c00c107500d19030b05503400c007502e0b5030118003450340450301a11201130003c0100240a0f072561079019141c1d0240300c032036081c0341c1060342081c0458090300703080c43c80181b2451030380e01010000542d188151544252290703a020f8000b182e14042007805280402e1284400c009040c3c20300191008042c1e03006009410070385100d80801266a10345258840640d80341d00c0c640a19503401c0c0400d60071030a40c01030a038400e80042e20020200342c8140c02901045600700b00d410603e44031400c0340f03070703a440c090b61100c3e103c2c007900c0020038060001000e001000701000e03180840e030010046000d43c8201c9042d81112440d210b080d4034881504e920303e046c0c14080600741400d201242d0340110414004030714202824a612032036a030303201c058942080598059a55000b4801240381c140600030700e002c1340002050a2250038140d0a45800da0608071200700c01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 716484406 1250 716483156 716483177
    0xe010b030613020a030e0d0503100509060612010803071202120301050409060f1802040b0901030809100324031a040525080115060906030e0601120f0f03030606090b19 73
    0x640790300800c41d4a0240000c10b64030b8204d4458041e01620b00f030403900c146d901499050392140c51040041e00e1045032500f070b80050300303890030040c4030802c00047d100c103400c07060030080c560390f41c0c80c10803800d4001c260740401103a80e180c25040000d480c0b418182400704540040540c20780c65011001540e055030300840c0c00184584031803908400034040600074800c15400c10722240e45608c1c5801d8000016402980c0c00c0c0036840014040001910702400014034018080c01110401d05100c1e8800400d0619070400281450ba01d1035001c2d240c03145050b1000c0441500d850500c03c220036004901c0c00148184020340c0d890800344e5070365445025845420084c1903074942182e52100c0000b51800041c4011030003004004131001c2451500d28060143d0030208a9107030000079000d01c6482000310b00d03010074001d49500d034201055031080f1030001e0f00c161031a11085c0c8881d40440c03555206403d440741711f500d001550038500000584400c4d40c0303a103d5403000b2030501822a03406070780700000000003003d00d802e07201003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 716485656 1250 716484406 716484409
    0xa17150f030a02120607090801110d090302031303081e090d06020d0b12030403060608070b07031251050909150403230703020c010327060f050a060e010b0306 69
    0x14007082000e54410802404182c03981340204070306004140035a42ca1425649841c180307402c2e290021404c0305d0510080048030a05241c5521640e0040d01c030b88162441c11013000080fa100386419002035680e50000200c0c0d6901d00d840041c007400442c0c01405540c01c0c00380100c00101c000541c068050181d039000180c2c09520358581e4002c958000c0300030a2040025100c0161a44d6074129000440d03085d03143c808049844c0500160400444a0005100d840d00500fa038084503829036140700c0b4513401c3d4880c002c0c010700075481e0b0226240302f00000d01c980602e20008c802c0608074003608100340c80000c0f84041d01c0d03030780e400c00046070f0040e0340d0284c540c075806c0d8a8421449181c00038075520400711207228000e01c0101540701c5200c40800780244600c401005003c0000b00359445080b10060140e805013010340102d502a8106c0703016860102c1c0500354401891411f00d560040351401118610b40d142d070400e144094501c6000e42182e1240000c100f1142090380b803408401060041038500c0e40c0110009503103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 716486906 1250 716485656 716485663
    0x120509060711010f18020a050405161404051002030705121c09050a02121c0e10082505120f0606070209190c09050f010c032c09010b0a17150f03 63
    0x10001307044200054044110a40f64a4035001c0003248a03c00703844000550b03203403030300443c0d0040c5000305072083e01c020180019164001c4140000e400e0b0301c010710000401da5107041080e4a80e2070b19401071640c81501d0318000342004071400a15441c650103104014001e81001440c407840d803406040014480581d081481c5011402d0500070b40c041c1c0d610304086a102d0001c01c0c0f0301101c1c045180d45d410385140740ea506841158018407a150020411051240c0c1c0764410840b494110102020890400440c4424001c0051800b0602400f05a0004040a41c1c103031031001c02d0b82c17007400b400d03401100c1d007481000105d2910400902034890400301c0c0114000c035544401415031f02d02010b00411018482000251840c6030600c1507a11800090585100341e502810710f00307001d6541551030000c00401e0102044440031004400c1c0c0742d04000860241c0d0302d490707130b0820328040c080d03008d80f081e251101804000d00c01c8011a1514610141690034860040740342c7c03860380c002c00c404840c0101c2c0841b41e00c000c40e15 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 716488156 1250 716486906 716486921
    0x1090506030c19020c010e09062403150f06071113020c07090b040b030c09150d080c06060102193801090b1014070203070f0e0712050906071101 63
    0xd116000106002400c0c104074020700d4401008202d104950002c010b00340e80390300718035074001e0100e0390202c00c08005240c006005540080d005044941c08a41515030844c80a107111254014520020030302c121a82d448078030140000040b20303041e4482504201280150044810080c000c08511488503500d6031400c0003485403ca00c1d81007191101d4882c100165101c1191043c12402c9240090301c41440c14540503020321914094020901c14502505002000000500240080b59219200901a540d1075048000a402800015107541e0b10b4003016040680150605040d0b50100c0c5c04614554020608200b00d9604000000202040a80e4140212104200d400341004c407002011000d9444035030014180c0d20b4800e410000c001e80c000600240044031640d12000c50180c00c003050350303a076601000b005154400b6060b6600e29984001450103001542c0011038a88a11344c204408264007022082c0c1d800c2d0005014801801e02d0300069440b0305019081004000b090740300a20242000d401401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 716489406 1250 716488156 716488159
    0x70b0a05090d0302010204030c0b03041a04030905031501030c0509090d050a120f0e01050c03090a0807080d0e06010e06100e0105031b03090d11071a0d060317031e010b0f09010905 78
    0x70100d0100c3c54028000d6000780421910740441601c00300348400c00c0c9007500d01c150360080049050b42651128920342480c0203208130100710310700101007034945050106180d62080107280001a50540c900340c0340810361904080d000309100003c0110041d80000e84800a509606200341da5200304c4904882803071400010b261f606042c41d00541e0840d249504c03d01c1402d036800700070400340e214004111800c1c0700640e505c14840c0d200e0580e220105415500506039244900c104601d80344012400105039100c441c0a8001a0840b800401107001c20185155101504803110400d481100740080c15074180520098100038000c0002540304020b018610b000e048400c00e22922072074100f0850380c1c0d0300028222480083c0340314851300c1c1030f054001122400d0324244003c1c480c812050420a0069801c203001c04805240c80f00b80000210306000e500042c80c1c1f01c02c0d40782958a190540b0780d0403401440d841c5840c410750302480108850300c618020740d0310154075007051680c0c800c240801292984031540015 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 716490656 1250 716489406 716489419
    0xd08040f030e0910081005150f01020304030b09030703090b070b270105090f0705010504150807170906012c0103021c08040b0a1b030912080c011b03060f03020102070b0a0509 76
    0x6404c00f10a004881100c0d001030844903202c08901100007071368000c2c0c4044200c1a943c446540300740c035000340701c88100503040c0f040302d003040c1c3d40e41c5460303140c2642030320a1040d40c0c1000030481d0500d980403041300040e046110a4914020403a6203846040e400201030f9100280303904401d221441808181305003251400c00203000074142400b1480d00d640c0c40c3d850707200c25403044070000125540070390240c03400c89407084600c7c0c0006013075590540b03050000401072410030010715010003054180d005014020100751000302107540c10101521600749144c64a420341550089403010300f008114110b03419258103542c040c01d52505240c0204982885003070080680c000402c000c203220300c4100c00b070b242d03024142e40c914051030310f0741c0256104910400c00180000b50400400d0052544030782d00c00060501c540c801c503107080e0209412500b102c04844224103007da040082c107030f0041c2d150240c0d4004d0040d89903082c0389030380b079680003075500d0301248185402441d000c1004080d590107201a10100240030300076 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 716491906 1250 716490656 716490661
    0x6060b03040309080712030210180f030f080a02120420040207051c2303070e090f060a05100f03092d03080a06050d11030f030f0d06080d08040f030e09 66
    0x58080c01e0107021301c8441d881040400250031200030504141981c041d0013912484001080042c05400d40c0b038020700342d0400340700360480000c44ca41c0e00001b00e0b90207540c40e006111075a520003010014040c1101403030318018001400c1d41055140b40640159200080301c0040d215820041912940410340c00d500c0b91022429030b040c002e000c500714034a0603140352060404c0140a1090359445011a5880c03549118410001d090112540c000d54205815050030b00368131190000081e00c001c0100d40c050b08565840d406c5c04030508003450301d88090001100e503010441c103a150010440c0801016040426807203401a409000000a8503145000c40c1d1811031880e00040c0e03a008070000041100710009656034001452140c0203101d001c0507118000c1a10311000515100c90101c0c09500c840194540a60900f011012104000401080000746441d6448040c01c009c08130886a041d8002c0d81b1395001007280307074440c95010150326030017903000614003041c0b000c134141100d003280c00721800780e00020f0038401e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 716493156 1250 716491906 716491913
    0x5040f300306050f130b040501180513031709100f02040801200306100e0613030209090d0e0108060612010e1501110604080f0706180b0601020d02060a050c0c01090f020307050a0e0c0706060b0304 85
    0x40c81602264012b500388111340744c4030b0301a4211404a0380c06400a1003102c2e9032050701c00b1440c900c0781c01c100c22a0444030105001d0391484212490305004078829580041d0400c2040d80c2070240440070f9230240c20408140340f8441c83d520b0a403000404443c031903400d41400e040c1c814004e80a42038005000f8050f00e41300c8040754101c42e0000c4072030006912513501040042e221031000500c5071304502c515a240da90001035040190744030320f005403450780e1280301030248401c1d1159000e4164020090380992007100d0030905266860740c0710500720141041042408d17194005000035001d50850752146406035503818068092086006440004010a080c0000c42091408200301086c44601a1051047c55210040166039030220092800c2c007607000000050072010103503000b00e80c0807080640c1c841c0741c92600c003100e50860740c520300c04480010f4040398200030342c10200295405000162545000700d42043d0380d081040ca0028844050b031903001503200f04208142d00414014896035040700d403079042c01d18 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 716494406 1250 716493156 716493179
    0x311070f060507091212091a0d0b01051c0c1107030c1401020102040b07030504061218061104050a1205060c04060c062307120506010e010c0605040f300306050f130b040501 75
    0x80e90480000d1031400c0201c0d0b031194415003488588c4400c1c450b40e1514503e074a000001c1e014511685041c885d09004002c11209100b00d12004441030700800a4003100c0e400001d0140158104201d250b030340080404c0c00010b894100d0401962007007000c08480c001c010004038064819900261001d01303000c036200f02016003250150054a4250711001c42900c80d5949a10850740b80201100c120082c050006021661551117000a0800d500c52503180c6501c503c040390b104d041c1d80d0f1081982c242070b2840d40c4282725084c002a50000300c00c44e1402e14203858034000402800f0842c00c090721841d41c03802e0b05a041c03016183c0e04d485015002403090600d143c900e0004d44006159024142e0f040d060400088a0750310811035100d49080584400e440c46056441e801c0003004c1c01042168102c002c01d00d6140804c1c50402c19111400c941d004000303081003521105240d1030480502d20045c03508005040c041c0365201c100e164030800c01078422841e044640d041000107840102072490300b0910b804c0003c200c0c09101d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 716495656 1250 716494406 716494433
    0x1050d0e070f060801140409150236130204050f010516120807180620150103060c02100621061508010b031b090609040309080d020a030311070f0605070912 68
    0x1001b1454040e100702c001e100a580300c44400400840e0f401c0d48a49036149184d0240c40c00c0181034042e64916034040c202c0d040070b0440c40464000903414070160030680d03d0030303041084c484404001c0940c149442c0c4004162034404052071941844030220300b00032000560350190610540091003d02000c1c190200580105410359400001070003040c0012101c0e00284452421691180e9952070010801c1c155140d0345032020201140d1405029010f261511000d484c86000c2c0d80688800a4401c01400303000e45003800b0072194001c4282403110400c544c0305120b4001001000250000246420707074230345a0f004040c1001090f112400650011659200560021a2011040d811580300b0002805407a15001a2006040d0311600c2e01000604a0501d0200550420311904001e03d2568980803002d040c0f01ca0980b01c4001a8000c071111428564140280501c2202540751245040221f0315002050301461307002030170302074494021502c418828224034004000d0a03032301011000c02c80c606040c883c2c240 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 716496906 1250 716495656 716495669
    0x41a0106171f151101020706050a05090a1101140d0e06060102010e010213120f080d140105101b030e0d0b0a0f0c090303032003040f0309090b01050d0e070f060801 71
    0x25000001c0c4140452001c42030034100d16003050a0745490049040c5030300c0303601c0380c0d02c0007080b0342c0c0c0f505500001300034009040554410705e40426203240c4804d5480c101c2d2030081082c8090f501c82484d081c0810406200709030f0004013840c148400200c080c0d81c41001e403090010780b00310349107071285108492101248203406200240e00038000c000812041ca8280d0081d030380c00341c3c000341c0b0240007000b92020b95481100385c14403d80035600c019125440f061140e0b0400485120a1922456540102c1042a00c101d015000031130304d1f10101d901e6040002e02c62280c1107a81c00e071072040301c240300c814140603800115421100400105041c81a0b142001c0000c4c0107686540036241040b42c0203000140e01c1c01201000c0341c0d075584a049071495610105c0182003e96402140f158231221418103d1400c500194441c5000d465100746248492400906040142d0701c282c69a5103045445c613038580c5d1080441301e01e4008807202051940c00f41042c603092014903480421141c0c18100c0003d0f0198004101c24101c802c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 716498156 1250 716496906 716496947
    0x30906070207060e060c010e0102131d070807120f0f090b0108010908030615090613180515061b0609010b120606100503070201020910022802031203041a0106 69
    0x40e4000c0c141d80e030308010302403c0085601222503003400d0514034050726201a10100200e02d4030000404c0c41c5c00c90740601c84881141d10016001c1c403172419580244070003180c10105100fa5441c1070280141800c0015081404208541091201c440d000f60003c20100d5800402004800d03103c030100310043c40c000d94211848000a0000200301c0410f22070320412907000b882040c90350342d8075010000606e00c6080d108d00007200600450540f03494503c00740c40e40c020600030b0580524103103131040707a0804940308003840383c60800c001c01260305441118811044401e0f01c55036111f07100e040010b0300701310711000686024418101000802c40741504440b110180541e00d4034000000040b500d42c450300300700c4405400003484542008254400c03001990702106610005040034441d04c0090302c003014403128000181d10400c0c90f0040b00a1010900d462810440350f0302c031980b9a540c0c0441d80303d080c4001010030703159001c80010b09211201e0700704c0826145045c0e03202021340c3c4515014100b640100c00003901e044 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 716499406 1250 716498156 716498161
    0x1c051e1902030d0e1501090203060a1505070308090c030d0e060408060a02030124050a05091f110106090b0319030309020a0314060c090d02041e0207080c0c0409080a05030a060515030906 81
    0x941c08110305d440d070426100201c516a00788002c8030041d5101421981d000f095840c80011022007a2414070105038195549949d52000341c10001c1402101915100d06904145181b400740ea0300000e030410004124280300c0700f50100300000641900075584004094050a010007051040f0399000750305032102040c0540696034511148805000484900804584100300c01c40c091401030001d40000940100340d03c00c52070980d141416914840034440000c580b2005604c101c100c801c1c014040a086107803401c1044240480010340d40e0724141c2c411402660000b101d041c18544203402091816402401c441000c0f80d0300d10f0b15190060b08011403a045010b1800802d40c0c0c00442011130f0300140d402030811003552000d4080000030203034000e40000040f4221420f15159840f1f0011740101406180440e446910740054079040005000949110311316140b62000015004415199004200d26000c2e03201c1e980d41e03607610000c18441d000154488144114480e07840000401140f00388088029212140c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 716500656 1250 716499406 716499431
    0x100f0905240a09050907150f0e04110403080730110a020a090506122a090c0a050d090f0b0a0f110405121c08010501021c051e1902030d 59
    0x4000a07803105a1003501103100708100340640d00895005180d8a040d81c02035a901c404d50011031503160a02c0000c2610120040080c0da0458400c07009035100391001c0c0b201c6260005140030500c900d0100615400c00464100203008a903401c441d8140010011207052442c1c6c016070100c0780e002e800200c00001c0300000b9104d410f01c2c000c640408025400341140e80610b0402103030401070702e401803003d5000000078180004034242000400c00d40c440c000c00118403020b0010090886030b00542c0c0d62402000c03040b06000c42d007030008080b034503c50041c2c64020344584842e4407401c060854404064107068005c030000d030510010240d59030140703068410404c2864044c2c0b0340c1c101030300c110342010410078100780010000c600342109028103185140054079031000141021500f1201c0c0c1400000029800030010311203943c0410003601c4440c050842d01741008102003000b0403e05c107650034000004242c0d110420501016000c0d519400c0f403c400184140c1c110020080d945e0304403080400702d0904001002100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 716501906 1250 716500656 716500711
    0x40c0f15080a020f09030109140c0904110103050601020f0a05071701090309062313140303070c05010e060708030901150501030e300304060f110a0f08100f0905 70
    0xc602140c4400500780c0e6140d11030002500084d1074030a512604005d44102d41e40c2c2071140b10240f0344200c07002e5038030700200d20f51249000c441c4041d9a00610b20b036014403022070003100050808160034030300881c0303d40d6000c004034144801c2482c0380c0701920401480c0000c005010070000184c3c0c3c0f55288038000d019a180f41709080e40c24241015000c101003100c2440205e208078490b141e2a44080e0711100201540001c03042d01e948098400140703c54081414010248a0310320240f2001d4100c0096044c031805d41c4030b40c1d442e62480d2060b40d040c02030001e200001d0740c03502000c0d04c1c212070300b0060311601c0c0c0c90311500302d070b018100d00c400981c2c1d2000700d12004109076019220700e00201c034407030005000b00c0d07004001e0001c07542c1d02c05150011390115040300602d005640303801540b0440c8609004190803010452010540e114031f04002e40c055814401812026444685401054030030b03d003080c9541c640480070014810160400c0248018020300410f50306135540080b400b400c000d88030404844800a0003610 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 716503156 1250 716501906 716501939
    0xc090403050d2a09051c02280e090a11032116020a08030c010606090b0d02090d05071d0108030406080c1321060b0405070912080c06040c0f 61
    0x429402d00c14594240c1c42c981c030800d00c0d40031600250442d110301c40d8a02140d4020fa441c038800061001c0310174030490074100240c00c1034031072801080c076001d000c660000e520030754688031244c10f0621070000140c0104803420302d03000510b11240c3d0903a01c0e08000030007540701c1c00c0140080c3c5c0c0301d11261045290a003000245030701809428484158050344101c800c507000d500c88104900000719400c1004050399032801d00c00000d020004c0159590400c06e11500d0170340305594400020301901920800c400301c2c901d4121a580035400d040103036038022844c002482421106c602038030034803880d030002c1154109490342049486940c80514010ba80e0f43c441250750b8882e5020307900001d06144085440100914040c2402117100b6884001064403466106001c2d0051420b0848003c10b122658007442410b11920320f128000340c8080c884d81c54642405065031800d0301c00c83c0f04007410348210406001c018000d0701c0c41043c0141c1940d0072820300d0704140030310600324018651000813038100000c007480030a20004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 716504406 1250 716503156 716503163
    0x3070503060c1b060a05310b130c03140114130308040201090812040509060105190f031d03041d1302060d1127010c0c260a0605090c0904 60
    0x85a0b82e01401108990020052007154400c030540c0c420845400307020f5540b154055400001e22480c12142c00e42111f07404910391203411a488041d10318041103030210101d119004041c100305034641d06241002c51303403115030161541b0302e500d41c08804c002144644461440ca60b400a101682d07a186162044030000d0711504550000004584000390044124603072142c0141052440269070300712803420003824114460f03071800d00080a000a1a003088420781040080c60242c1c148544031485202c21003182c1182c005005901c24200c4907240b094010139200d0203d1900c000078074115801c1d0581d84d802a006101d0340100c0c840742221140c010106035441110f9180c170201c065940c80e002e0001320790010304003540c082e8680724046c245070350303c0c401456070040c080c00301c0444030502400b48400a0254504504002d0940c003c100031070904002c0c2020f440c81a0320b00742c2c88d8100d400303c114000400070719001d000e00038070f0082002e2004650005114400c02010b0315441c2d486113040000300f00c0b081b0fa006 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 716505656 1250 716504406 716504413
    0x10207060f0c020405060d08070807061a210319050711120607030b0103021b0604020f030105090c04150e09061009021201170c1908070b0f092e030609050603070503 72
    0x9001d4601600001c0c0c001b00c000d060b45401c0e9103a9151710701d003035010403420340b141540005c8440421040d8440d0f03000040c940410700030160f5044000580c65280751030300d040040c041c20f140c09600c01c003d200302d03912044881c11204071000310250140c11074122110580c1c0162800200c1965810008220300301140300c400600701542d1030b44002e400514043d282141055402d00c44504094004d07189a000058031000425407480c0520404c00b170348001c160178034002c0c0d04010034000007001c002581c0001c91021240403512400302c2412180b071201903413011404648d0070b0244070107503402080302da00400c40041a422115190010300b000d07403049840d8400c0c548161001000a00328440c8480e00d81c42e204015244450800d000040c1d005030800d480003a0a40128420019400200320032030041202259950908a10254211160207142c500c00d00030310303505400240404510b028109148520705090442840140f001802490103005204c0e04c6482c0001040e840e280c0001c01004659005004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 716506906 1250 716505656 716505677
    0xf030b06091302120316060506100c0209070c1506090204050307080c060a030203070c0c031202100b030c090601020a1502030a0b012c120a080918010f0302190b0d0902010207060f 78
    0xb03103e040030a444e0402c0f824041030001c081d0f8001c10144940f5801e0245030301181e81d00b850010400308604040065050218403402e540050300c885590503400f22103401c00403480305690901c0f04500c081084003803200ca19040c00814910215400703030065071401e50888603030039107031703503807141da840310150340541c4080c050020402144c0b00380c00540d0f00c030841d880c24500b54032302a80c0c4d4000f1401a604101c40c210207044540024540c100020a4040d0b0b180b0b505110200415012036141d400070407816000340400d000103503d0340d00820502e811550700c113094072061140c0c1d0fa038420003074200751060300341035040841000c080c0d03100c0e43c1082c1179094040030b05510f020003030f84003802e00c00c14000003680020200d0300f04061242e007403280e078040fa07000790503582d91400e50030104003010100c03501d41c440f1400044010b05c06404680381c818280d9605491f002104071001600800000030b0381d100c4448183c00040710b012041194000041c3e440c404c1c0c00301c0d403541c0c1d155502940d0011400c0020303000501035206 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 716508156 1250 716506906 716506909
    0xc08040b03061c03112e02030403110a0b09060c03041e1e0308041704030507090507020304121505010807140607020d1e1403030402090a0509160f030b06091302 70
    0x442d0480c80003480248524042c0142c00d600340c12402003640441c840100d2040e00d034106001030100100c4e034110744500040c003103488600c00d01e09000c0b03407103625902200060030503000c5d8290003854803052088071005003d42c90082c00b403840407280030480703001d5080420741410102c2c099038003542d40003005440d1a8501440f03404180081d003410b642440c0d20055045480740a0303a24490014001d5030348902038501400c02da003003c00710140ca410309401c1080f041021580101d4407006861035211701280c5525030b20000c030324500031500030400c02400e51085904000000c501146a81c0d0100310a2040743c1e0303521f4507240c5030f09180c401c000305100c4440c2100c0a62401c00c0081600a1000b000000001d0702500c0e01c108925418030b1141d118400049004213112114085210213198080107501d10701c0d0513400305081800280c03102c0206911380e4041004004280218240d011940b003c8442e410340d1260081058100c900c41900c1e90038a05c0086910342c140a84218410308a10251000301070b420360 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 716509406 1250 716508156 716508179
    0x15010303270603020919050303042c0703060512061b0c010f0c0c02130614090402030f01110306040605090c040b1b100f05150109090c110f0303160c0804 67
    0x2070528604048000c036004000511500d203102420159800507240c10800c4c1c140807410001300c030341c1401840201000c21040d500003045400381c80705003000724190300c201400b03140040840580240c6202828080104840e030690095046072002c413503203190040203483e901e88902c0f00740e40700c03a12002c059400300c000c801064010840e8102e018000608041703c0e1300c100301119400540180001d100c80c0a142c19071600c00c441d012103e85c2843c0c100a0316141040d940131444220040601907004000054155a8244004690300c61564001e206030203200819600b0750380100c40561060740303049404078880c00c103110228070402030700d03583c5850542000104031142e00005440d881d5500c880d45846076001c402d00c071120a003903590780b022030000034031121402650801412900d500042003400501c4d40c2e4440314607811540410380014001e01c51030421900f59a00e501c0e00b103250b1040d080e0748035540c1c00000045206101c01e08069400540000d4219080c1010900203801d09030300b403006200510090 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 716510656 1250 716509406 716509427
    0x2040506120114090d0807090e0709031a010501030e010207110d0615120204060b0f0a0f1823040b09040b1003140f1204081f0f0207081b15010303 64
    0x148014040c0072066000c6003940c107103810700a2442d08000900400200c00c01554070a000c20f4100b07511240740c4041c2c010a002c0f054400c000943c42d0480c0030452080c015000600030790303040081c090201024008003106080203200313080c006032404c07400010078071040c4280c41c400b96120810019249900c0108104070141310307000e641c200c1c1d8856188415410808008004011018400c01c1d0148140100821107045511124244c20704102404800306104220782144801e03040041c101500c2000490304040840310301190541d0000b4040f405d1702c801e401c0c006203d20644052041c0444d0f9009100c15680d0142035141c1010448010600280f8a500035a90110025506100b8280d881d10354454480c00c080c0b0b00101604156106210740e02c013481070100444c4001000c900d054a04000c040e50750344440c0003c0c0b405d080070303190700f4520300a42d0842d48520322170400c155281d120340e0811040c150300c184400f40103c0c0c45004084510080415003102c0700100c07421803901340c2e1a41d1001e07203198241 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 716511906 1250 716510656 716510659
    0xa05190b0d0f11100801030b071806111510230d14120a030c1b0302101a060f2706180f030d050c071202240c010c0c0213050f0402040506 60
    0x460203400f6aa2a901d1510544110540e5161100d500d1814402d00040014100008029200f404096204201d021420454001e4030300390303a52240380b02642d03040c00c9041c6800c0c2c1701d0190795820711040d00c00300707075842054400c1c42140c1500c7c0444032101900c01c081c2055456000707441c007595100890410b0b0841e1a242c4180c0e803d942e0310401d510300070003540d4405484c88c00841c2d070b1850038003030392540301c2c006640c1103c011640b6845039090f40c8008c2c4d660b81001141e01182603c6820110301401c0750780d51b01b002c003c0d0141103142c441004102500c0c2d2a04140c00700612580300007580030003c1d1030b803500c6a0041d88081c00a600d459180005800d2147d5902ca005802850452845000b524100a42055100c2c030b0b82e01c031a06d4140302078440d801c11030207a200030465203c103c410000350b940c40001645a101c1c40c0b85002c01d2003030a040c0c0300f81c5802001e05601c0d0552030540c1401c203482c0c01030000d10703115100f22005840c0109002c0d85404440040c1c0d21100580485000100141400d61010740c201c0130 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 716513156 1250 716511906 716511923
    0x70b03041a010602030a0305090f120d06030605011d2410030e100b040b0109050112150f030308010602060a020f0712050f0c030d05061203031501050904050a05190b0d0f 74
    0x74840c800c140114003a0710410042c0d10001d0120f44031030f03240c410b0303641200140000e0207030103014015090b9200002905248011400601590300440c1076000708000c41e0b00145c14823296965542c00c441c41c4c104031640c030a140304200e000074901c50091544111010501001098050039101446628a00d100b146810b05d641c840080c8044c40d402c011800780040c1c8a04007140280c04c02c4140020744c0c145001c00750501005400502c040da030083d080c0002c1c841d4081000880c54400220b440100c1140d60000e80780381c112000110030316a00c10001c2e41641da058085424a4a60003540b400300d22603400d4221003a18103000c02c40000f07505103c0d0010558103440c1c014101001d02c038450010b68040f0840003025800054061611209400b5180d807000d02202c04541c1159551540c580381c2c8801004070004d04130080722039041c0e84c052801c0c0c42d011a03020f002048a498049011802803005a810100703504105442da03c00e000c45c0e000b004100c12000d0b0821001c1410380c0d4176003540c800c000c171040755a100c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 716514406 1250 716513156 716513183
    0x702060c030a1d010e012406030504020420030907050306010303090618050307080304050f0409030905090c0f0f04030302010b0a061e11030a0206040308130812040f0209010e01140d05070b0304 84
    0x6500143c0009003100360000240c00e0500080c0c0303030850b2240c0c1d182d140500b003d0026001032045912001007100e285050103e0a0b0796070f0b1002900403c1c41201204484400d120100408904000554401c640100072100e40b2500e0341c0c105956010240b100400044184005008062080e50400b858144500c207119155481e0000242010444d4008180a030f10200d020001032030450301d407903060a01a90108400d1009072001030044040f405403602035014500810100292501280c1520340704588140c0c4900f030b40c0400c00e01c00d078082c0c0301c158010340c20090928400e00d003c0031040b04480c110b480740700c0a07202240031040d00b141544681801c1c010400300140f171400040c0010036102c20207601400242c60a468007030900113024200c0c455140580070500c3c000390b012421518000b0700020700c503080d03036500c1c0b51443d80315000c49002900b19900c03e0000526880502c101816242051800070703c0314104810311041907035018000d0078943c0b1805040112000609c02540c1140c0101030007120354 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 716515656 1250 716514406 716514431
    0x40903120501060221030c07110d05030706060f08010209130e010917070606061b060203040f150501051203070506160207050a060504060e0105090f01120e0109140105070203030702060c030a 83
    0xa5000340d00070310158121842c04036052840805d84410000140111030860030415192a400d004650f801060445a8580400750b5a114640404140da001040b00c1e80d425440c0b81c8070024015621a0b03a503075131105407000c00c040d481030003903072459040600441c01c110b200c005c42e0b07170180010705803642079556182404408181100e076a003d82d42c0204d49025514401d030b252080071944a603010ac030401403122402c030140c034840750b00d10401f41d4200b4800768494a030390920000c0341c00d140100421440d10300114103011000c2e6004241224070845140c021050004101a164401c2d03a900519540001c0300280c40e55036a8074995400f656103104a42401d921140031494580407500302001103030005c40c08008466204468192402081c0303003190038180d02c400800c20b00320060807080e040c05107100280902c0300503644046440403482c0024800c00550b810b0541040104140a151950902001540b10f0b800002101d0140c0517907802401c4a96034114040c1c01074001074031a2454a03110341001000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 716516906 1250 716515656 716515661
    0x4032306130213090b1603051b0703020102121906060e010c20040c0c120f080a0b12070f08010b0a03020f13020c061611010606120903020c03010203040c0e0c041404090312 75
    0x40510407034170b00c03c00303042624106900e0825803c580040504040401500c41d0550709180e44091900019680310b400f10310f416400380c0203200e0440b4808101c001006540d00d800c070315109003180da60004228441c4c4505c03048941d844010443d6011400010103140041c0c1d07088a080c06210710202084140314921000030140e50004151000040740f11508009100c484021205c44510310304001901c140b01b0750340500012001807600c00901c1d52441658200d03115028484151910303102941d4000ea00e032100000692010300900c0025840e1241d440080d060800d80710b010b9940080050b0b40e1034120008200c00207010f50000711001d5024491500c23152401c00000e070041401c9040e8407510f1002c0c0400820059100c004115681c0c14003404019842e040740e218500c180349000040788001c2c0c41c2c20245e207890b1000d10829015840003041100303214900c0010801d403020076002020b1034442c9000c014041c00fa0303029442c000e0609084504003450150310100146110342000616840c6401e108004c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 716518156 1250 716516906 716516921
    0x130603020c0f0c010c0605131401061806050d020d05071a09040f0c0c0204230a05160903030203030f0a0b0d03030c020c010219080f0c06090304032306130213 69
    0x200360007240d9200504000c1c80455154002c100c000c0424915800c0003c00003151004040c0c0300507566000720700007003000024540074580003001035135036001c69920f1900a115520490145409243d450601181c1e01d0141004a500042003a0406a280e808010035016440c02c00c45075441180c1c2e00003081200d400c0d10846603071003000e030a5140c80f5804103100c191032880050340c3e44281b401d601134021581002080c00d415406850000e00504442c000351180210802000005520380042100407060358000511074485210111541800610180d13025501c5010040c003580060001646120803004141da018061806c0410101c1c14040840c525424a1030142c0c0000d07120010f03012031036010003c00345000402c0c401441060003000c0708161481203403038010004040050006907070301002007a00d030f501c0380c03000a039040743c00d040c040c036540c0c2e178070600c03003102c040e000b00d4220021001549140c107460180a000f51401f682d500d5883c0454104e81201281c0c8900480903a2022841c944207001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 716519406 1250 716518156 716518169
    0x150a06170c1005040324111b07080a050a03080601020c0d0b0603160506040b0702030f1e06010e07050a05032509030201031a0105091026010e0711070506090102010213 73
    0x40503141c00c18082d0000121a0b55401d10008020810020300e07010014540b81000039584200c10000404840241803402c2c2e40c103c0c2c07204c0c04a40e800310302c2d0000fa0040005603000080307071111030740c4081c1261a680426400703841500100c00a00109000f030301c00c541d201c08140705507184d2000b00000924200180c100030b862603201d000411049040400c802c8034a40b481200204a1034981800241c540c812402400403e11003c10080f045460800c401c9907003200180c207076401c8200180c0c00030650040000e012801348510400001c08864400c6468091152540c8003480e20710840ba0946580d80b026114200000b11070100a15030201c0a800c00079602d10340e510180400d1442c0001070554090400218002108640994240c0c0e00102114041d031025142c40840d86201c100c00da43e2501000850b090f80034494114811880d80080390328144c80b00180701c00c40c00d80340c0100031650761000004601c001c1d40142018807541c41c00d100908525501480098544205103444200c0080b1560000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 716520656 1250 716519406 716519413
    0x807151506111506030c12010204180b031b011d010512010801050106090803131217190f0305060901140d050102130602121c050a06030f0b070801050d0203150a0617 72
    0xd2400010030f01011076144296003903c0c805040c0a000640c44460380000039204044a0709851104802074068400402e031640c1401e858110118000c0060055855224824091010240b07048003086070801e055100c180d440c01040010030003201e0000b500811283d05010050100000c60b545d401052400317171043c8000481d00303502d0000c01a1003254250032820090300280304a400c034100250a913011119440740080c4100c0b19030900101030030320800301c52201d41c40003950b14019142e01480c05e24204080c0d481408040550200b101194410b841c0190301c480d5080040003101c11680c0c00c106440c50082c204854503074030f55a0703582203900c128071413a0b40f92900b80c01045031640500810790f00d240d140140314130380b1952102200f0b0a4451103210411035039280d02040035144d03140d001c0c4d409198000805101002581010244183c007140d00e5400103849400114850400c501030440741540540108000c00c1443c102d20850700d0000d0000c02003582e140d03030004511541d07100030b1401400d582d01a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 716521906 1250 716520656 716520677
    0x40b041e1524030213050c09120a172106060c0312040b060405100b03040f14010f110c120306060d110415031e0e01111c15030807151506 60
    0x440c2d1040da80c65501c03072141209844100050f89941e40d01d138003d082c0e00c880005e85581c403c03003510380c140500c040740ba0f01700400d0103048410007800503601000754051060380c0200c4210b018560068410001407080d100030422554010781c443c800302a13040307040240040c1c01c01e03200211040c91908407016a44030f4914030424032003800f135420304458000d8800d40c0c00303210031702d0030055040340412648961001440c00100080512100b850403010322944040c0b41110b180c0300924040c00703440d81e44a40300d031107890f042c1c0ba0003030a806001141c803100c0780c01740070708280500d218608040307070002006c55410507001c20140601341c915100300d103014024048000d071200d0811120030704006203500c0100906161407840c840c8200002400150005248008149000076803290340c05012050b40c85c00d404000820780761982c15503480300043c0c8000d480400c1200350400303200c0c0e400305c444500c40036182d030707030108a504042040c03180322220280e2900c401084003c1502200c180c100b5003944100b00141440300c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 716523156 1250 716521906 716521931
    0xc061d040513140c0904030c0309030b01031a0a0911010e01170108060103170310150507200111031c050c040308160b1501170711071706010509040b041e15 68
    0x140840030300c040030081c210313101040046849003c002d8005014000540315802c10107101e214080c024543c80044e030030407543e403454003416580c4a00710f1b004078699001d0004001d51207601c113101c6840c0d08480030703001a409120040d80d0000011f418a4100f00605414210302000b150119000b05803c8008104541c0745042042026544420300c140810040083c4006510045080310698942c0d0700c0e0010b00d0388030402c09440d5449107200c0145a185080c8803043c9038a030300700555211407400e80301d0400c240843d003e0207450b4440c40c1c41c41503150b5001501040501e880b07900055001089070361007446c0c02d4580d16101c03400d41113a1114200100b02a50b100100400030350640c0d0840c80401d80c0e560004010030000e0031860017002507140390004500011416403103100e5403165004001f0a880d0110b803035404602e0301d40c1c40c181c9005902d01c15640000b03841c0c1800380c0a01c1c41140c004501200a80359a41c1d854400c2810001d4459801d0f902800e49006c19412980302c01c1001c641e4000042c1c000320a40d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 716524406 1250 716523156 716523173
    0x309182a020607050c030403033501080c010207081b061209010209130e0c09151924050421060c1e0e031209150a120608010203040c061d040513 63
    0x1800c0c0d001300801802510103c004c00025a4240d81e07041c01c1050302c0329404a1000100c3c050031441341c2440c6607d21074002150f1003103010700d040e5034650080e030340b020b01d8000059a80b5405403141850f0703680040d1a00203800c4184a0000c0c05040c005d080c10310b44146070b01c4a0344c51120030368800d05c05942c000781030314091902002e014181652400140b015103e00c29040ea11480d0030241c840c02191a40c00103000d410901d100c0303850f420001400d00070725880b00e035040c40418010740903a40c088010100c148007251104400e14501c144165601c40c0380500b40300054580c4c801c861085071200d0340d401f4001c40040c07640e014400ca58001135580306141d0002800310340095002c00c1a035000c0c0070104100e561680c5000c201c20f0b08544074a200c1c01c0ea20440034003c1140c102d00013080c90000e030004544580c60355403003502c0707a486d122500b1040c000240c5440c2e2103406c030311059030000c0414400c02c50030408940681f101c0e501c400030307400010a003841c09101060640354201c4429100c86100b000e07101c10001e200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 716525656 1250 716524406 716524411
    0x90721080313030c060203010603060314031e0717030f071701030b24090109091511030f15040608010e150f041b150c0b0c070309182a0206 61
    0x81005404000151a4000c05200103441c0d8824400310100203400c0c5402100b00080d5554055802c6581c4e6075200d4005000704128001180c5501030036640f44204000081640c0117030170792610030010701c45c0403270a00d0300b584e000007400c4512544101030307480c1d0074000c4030296114100d0403c0c8c4846600d0100d00081c03100490b85880700042741428014070100d188003000300d0f40a43c01d0a01004924240c01c02c4d0025030115080d900d503c040c1c1e04c40086404202500400a418841c01c50a0f07200580d41c4100c009880a45512459601c000e00c0040da00030881130255400007aa071115800005421001c24107650182d04804260f80d154480c8010a080800c410134918150840140300d504202501e4403c00704050000340c03800c1140e134203150406031500640001410500d210501e5000104030142010070841c40a6501c00d4004000440d4041c11000310b41e280b41d850b03945c82203d5800d005402505001c1c50440e04940c503a00c1c40285040906403202000000190200c01c00304510324800903c0c00c1d100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 716526906 1250 716525656 716525699
    0xd0914010c0206182e0b0d11090709030f050d1d0d080708040509190b0607020603071107080a06050f010501091d360c04050907090509070308030907 65
    0x500740071044403980451910381040e00480382108590011913000d26004203030816076420b4164000700560024000c0a038000c0c2083c0d01424041d070b500b502d08025448003085000f0300154524002d0145034644804484c0d171107440e41c1041514103480b0b40320b1080441140e00116541d80c40b0301c1c489050a5004590b505108015141c445c41c80d1f1502c50214400ca403580c4401485080d02141c000200304088042d50301501010740f0700c62442c9040088000100d0202410240c050700e00f031000045420001c0468103440d23009000e481c41e649a0b80c608890701c644440102565001e1f080021651b103c042c030010007103d000d5200800d4609103213111030019001a03103c603041c00035017041007203201c0d00e2000f400d030340c01ca048110740c8465075075420342000c018200500010329904040c1030b000c881180000101c881300d800d8100e5034203541e032505000c01c4507001d9941156030f07801602d080000300c0b606c1d00482da208981c803003079482284e0b5075a91020560001d840001003504190f600b4402008810592603d000f05d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 716528156 1250 716526906 716526911
    0x9121a060603010510080a020f130f3213020a020307200108040213110f122a0d0b031005010e0705090d030807030902030d0e040b180c0a0c0501020d091401 68
    0x13409000440840080d84040c007800703518800207141d44150390550780782280c0480a265100d19101e055641d110f05406100804500e00c180800c441c0c401035803480519000d6181c641d034414071140011390312002008810340c0140c1e0075080940c0401b03640058004030030507030000c5465a0040c038200680b070704c0c070149007145008000d00031041c680c0e003d441d40781c01c50b406035031807020407045419110290148003104141c001c0002100c480b81303d9030800a21107a490180002d42035120602c0385140e074600e0f46107a2442d0f2070800030342004560380c88003c142c0391000a50018824031010041f81c1441540031081c10705036034540040211a48820300c85504c40710514081d840c141c0010b00041c21088072080c081c0c2000b41c45400180203500940c0254030a03900281120f00c02c001c0b01c4001828108040e13800b9000c0c03814008001a982400c40101044a43c08207480d8140d643e6070320010102d412000a2400b0042c8902822020038801e01c010701c1c84103040f0202003503c2c651818407200090300000012550b03031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 716529406 1250 716528156 716528159
    0x103111309020a050415020a0c080c03070b1b12030a060e0108030d050a0b090f010311010906020c13140f01081c0f210c02060105030609010608070e0709121a06060301 73
    0x200311011150a64140d110010784034070803100102c44500841d0002d900944a00003003144446e00050030303402080c400d0b85800100394544900c140c448251506240e0982e2001c0c10500810441074081c1140c004125066003482d90320408951400c9082d80030030a83e29070000c14040e0482481c00341502074a001b100c450555458048960703a41e01c200300440381d20660b03510215054890356086402d1381040180f101c0c2c21400d001d008134041c110203101c202c03031001544c4000f000950280d440602120300c1ca401030b010400d010014022115050320800d44007035510103a45003034005004c02c8a0181d11401c41c00440d80d030400141c10f00d0114005051502c0d0500c507122032100356403010258118030301c5843d0007117030307640c007104640d440d000075100d4000124246003600e8081640015410304980303040382144c0c0c06454100ca114200ca0345801400c415411200060040d6a4085006600302c140d525140200c0d540da0b0202148066030f00408442603e03a488640b507860841260864000104951503031465 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 716530656 1250 716529406 716529427
    0x191211030c01051e04150305090106080111040605070503130b04090507020a110d0c0306050c090103050f0f04030f11030a0c1a01080d0c060905010203040321090506060f06070c0311010311 82
    0xa0099018080108400d104500701380ea410074181c50080c5046601c21803445c03140c2c54082d002d0101100d41c40d485600c3e00c2d80000c1c1600c814000c075641600d4092a1624083c1402c6049906034000b003010f640c07601c400c014915040014003c00e000030082c3d03800807500c035401c0000c0760382518009003a807400c5520400c010700106420580c0c036480110110f03058800c00c403107454007521245050748060415440d06042085a4940e0002444104c100f640c04210039036610040104074803041d101000344c0c140c01400100044d010312914142d20140e801c001800700d954500b2140fa55204480207000103142e403400d04100840c05402691039441c5150014007581041c1d0352035074030800805e0380010001c15442c4842400b08607881013440641145c002d642d6807405044c0685001324913040c00101940c40c0d00500d0f03d003c80340c442e980c1840d034844090f140c2500c410040100003c9100344c240d912400800c1200000b032007200c1c880e8001c41c42211980302d9800080000340882e1490b10704801110070030842501c40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 716531906 1250 716530656 716530667
    0x10203010f090209132d050103050d0c0c030c0810060803070f020603100306020c0303071106071b1103060717060a06020709090f020a080625020606010e191211030c01 73
    0x40e520008801a240da4440b000682041908070100d006685071031b19260192036103403101c8084540b10400f450006617000240006c45109110151564000d85520101c0d14441d5111020207402104007045850b100d03181d0045408455004410a91100c8100300320048140100d100400c5004080d60600a20381c69a02500c20180802031040300300000284080300010203040146401500c11525055040012607481d84140da00b140400d01901e501c20200718001101c5225801d1035441191004525075503d90551601030101c2d4150001460340d0b12903201084264443d590365607800007038031620b240d20080001c01070034080c081c00c010344040c001c154000501d0801c840250000140c20b001c0707030601d91203903801c4001c000e502542000000940d500006103050190300c4803940c103c1003c80741c006442c1d049402c4c03210580540c00c04c000042840d0700845a60b0030903000a40440740400054080401a02d0560000d0200c1c0540c550b03180c1c180448003254980901c402c1e0024242c42e944200003910 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 716533156 1250 716531906 716531909
    0xb100309050303160302191205010f050607080d1118010e120d0e04021303030c0b070801050a050637110d17041106040e0708150105040b0f071209050111010203010f 72
    0x88401c4c40d111016031140320b03504032001c0c5070400200901d40103c0c914028400c03440c41c072402003d9070519001040850001c0c0e40e1504440000300400d10702070f543ea0300d4070515003184403060012070350b031900301d41d24003032002c01400d102195813044034040741e1800025009000c107280c5c203270160780e03926001001c800700000c0c0c40f024031f0700c5420b100d49001c150710300150181c030407800780480000041c00008101900440094000b920a00514a456981c0c60086540b00c030241300c0c032076001000200400481c00d10200402c68400d44400781c45080580a40354030b824041042da495040744002c5049501c1c5034403040803410019988060102d40300c0d032180003011040305000816002c800351000c02d0800400400d10a01d4010140019072115a00c10740c11402000403600c1001145000c00010000d91103281000000c1605844603818a400d0500500d0980c1200402c40c0032180704010020124041c0f003405000039006541d0b5078005410540010817044c42c450340105141c0c018401407141c0b440340b01d50b860 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 716534406 1250 716533156 716533171
    0x10206060d0507030f05011d01151203030906050c0307143f01030c050f04020c0604080904020c07030f120c030e10031416300e01060b030a0b100309050303 68
    0x200101c01814024204411a8002040000c803582401d0030840c040d00b1582c0a203280c5d40c01154440381c444540380c01e84442466981030300107122014000c4c0207030350f4041c044042c02440c1c009800080303030b43ca070422500203980d412503480c004800c00080681c4003402c058440100c1c124103003440e041030301c02410301e4562403074000a0b0b02c65040801d03ca01c02051a00080140010041000c0d690f030b04008008600c5805403a0007011142a0186281043e0007101c40c3d0101c0180108070b1aa25901e400c0042e40040d4040d0350f0041d020020400503c03420015400510701800141c50074901c64604030007403400025a01050104001146021035045010720f5410783d01501c83c000084203c0308100c0040030071203401d421100f514001d2201540b1291161045941561a80442d48107c90320301c00740082264814a860080d911200c0300c1107009400c1a07464403040310012408036100d01007817480c0d030001c40398005410750312150480b49280240c0c508140901500342008448515140e481c2c503403100030503a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 716535656 1250 716534406 716534419
    0x1d1504020f07080d11070b18030408123a090f020a0e0709051504140d0f052803080a0e1006081501090209010203160303020f0a0305010510020c01020606 67
    0x45159485540440d491400380a0030141d50310b00d545000c0003141c00005640c100245040035450400c1011012101e0564000c440d400f00c91b511825a0080c401408100b601180402d010009800d6401c1040e240c0c03507282e5041e05034803400300306480c640085620800100c6c00388203010000b0036005211403144080305a00300401c00081e2802e054915404140b07009401032440e40000440c802600d64681c06211a0364401c103042d541c2d0800c100701490746404445095200708410451001152030086000402501c3e0b60001c0c455500c800059003c40d010a440982000c4003d08a11303401e0b01132140b0381154003418012440e101c1d10010014000100310540481d07540c940c07000c10520800060b80140d901c1e14040c00341d1030322000c040c5d480700654014040a41001000401c41414a0080d20034059041e8021400c1c000a412040307699a5107000035405c2c103900b000000130300d0207110010000649a0b8501150031b51504040c083d5a103440f182d00b00441d0003024200e9171903a404540150443c40c1103641 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 716536906 1250 716535656 716535691
    0xc071407051804020301201b0f030a0908070603020c0703030e1216080c0103052e0312092301121a03030c010b0a050108090601050103200a02010b0a1d 66
    0x41618100c6550400e691010100101c4650800d0404905104a03c01c4c0c009010425145075040c1d050038403000c0c20b005801d403d000742d000410725015050800384102d03040f9104002010a0315096511070480d540004180440030f00c6201420003103c8010122031808620307144103240669220030302c6000040401c581012100349654445100480307500381081594035105242c0022400300c001449118060300508034071601c65030003445003d1080058801070400d0b00d07080308807038814004c0b104182c010307001042070101c040b540d0502a4005c15040f40c90b44c0917a1814181c01d01000c0500101102d02001203442104559911600c02c0d809803841c044c000c11118030031000c44034080f0010300042c0d018480491103250085054100404000061b035110055540b61001120b000008903000080c0764880d02c010040c0d035100781e00c0003c0782d4208181e800c91100340c00707021b00d50320360040d10000c0050303450341200c5005d40b0780744032240000e24040881c030015029046158110460040c002005402070505 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 716538156 1250 716536906 716536943
    0x509070e1f0b0d0209100e150412020d03031e0911060a1b02040222090608010b061e13030b1608090d110c09040f0c0503011e1d06160210050c07 63
    0x6841600307400034506e10200107a600d00410510700c405200b0302c03810340701e520b004041c0d04100440e000c0d50700d0040509200d241a070280071221030400c4007201050341d15148008074484100c000321444017a014049545141800c012030801c3c00303a000d907486842c01700800a11590411001b05020000b25502034002550303000140090045528041e20196010301c14805030040962040550340182001c020300c036101c0480c5802ca8001007455500054204000001c0c0c0340420184000c1e00403071305825180100d0210359840386d480f103a00c1142c010728088280b040e084040b00001900b101c0a148c9241c6c580b4050089a94400d4110301d10020300180d04101c21414505102240902c00098210030082c106441c05000c0b01903e510180ca400e502068089060300e0180141030801224008545442d88041d006c0300003410000381e0014800d80c0c841d8140325100d41880070911585171080d086c1881d00880d50060300340710186034800c1c0110310b80403c025200c1d9104c400d81d1103464002c0c81e4021044990031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 716539406 1250 716538156 716538161
    0x409030c02151e04030c030803042d110405040c060f110f1e030301060507080d1e0f0b01030b030604080a050c0a050d171b0f07060509070e1f0b0d 64
    0x48041c1d0450326010140203198410b40043c071540300144070f071608903001840021618010750000038040c541c504802c2010400820185400c103010703000c040b0035801c254890404243c00d6010348000400075050100034000c034141d08003d4860709071400c0c4924a003584e1044100510b0b805607409000400d80001640c80c8031340b550711841d99040e01103a039020000c0e41069503800607a03104881d0100c4042d14817884402c04820f890480d000390320383c5410400e00d640e032001550000310b0141d62030f50b82d40e1442c00c082d0030b400703000d080060501070000440f24410910307030003034410b400445030502d07050210b000e00a480025a02e039205400000950302c4035103501c0116410f01c188841c0e00c45a1244150942c00c2c09408681c1c16500c1c162604e4003000da510200805000c1d400c12681480c010040c400c0280c80cae403d070440100201c80450409070701e0040e4a54a6070b0071208152031070002039011800a0080c8001c821607141c1101403084074400c4000e01811210640c41640039110000d40e0200f060f035018600d58 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 716540656 1250 716539406 716539427
    0x15080c19051803030c070e070f02030904050a020d090f020909011e0902010903050703080a0206071b0f03052109010b03011e0b03010902100302210601021005040203150c0307022406040903 82
    0x1415aa038412002115691700c0d000e07402070f80c402003518004034040324009c155010ba0300b00b1300c0d00918180400c2100b040f00a020041c01c2e21101c035020801404880c0c41e40c481c2d03a250b20f1107000b86e0708480b00d0394018001c0340403004050000680c5001100d403468012051040d042106120000c90350f0b5140e4070040354480240c0d4002080e43c41148000300402960708040c0c080c01d00e00d503007190f0855407581011035035020340105441651120002c0e000100d0350403040140141d0103800d22604e031601d48100240300800111048c00384840250234000000028051030b000709100f18002d120612500b10741418040c024009030070503075910504030703429071000e4101c07480450700181011a8400c5803640a00658006402c044040b00401a0b900c45080e100810602500c07040e401000220704901968004200141c810780c0e141c0701d007441c800b01503208002c0503407081020124540c0c49013007e950207441c024001201d480b070410b1040a031901e003500d003120309034400c3e021140411480590705060301c48040c0d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 716541906 1250 716540656 716540659
    0xf0f0a03050f15070e120109080307030f201b100908030703140f0c13080303010329040b1306020d050907080c01080f0f100f15080c190518 61
    0x2a00000000e00c0701c0440c200c1c0e40d807107100080d5420b9425100483d640c0c2681210b8600c00b04203414091035032030620800304000800345500000c0d855080352038000450304102e41d00c0e000a81c440340008200005401203980c49482c90581000040e4000c40141c00c601840c0e4929403100034005100310812820049401500c545590030400c9503280c0c00c0903d00c40d0700864401c3d005ca41040e250081348200324032a1480f501494000c58a2a100d44600204650242d1030888010032944070105100d0400c0c4000c50007036228003050302981e403000140e098603035400c0403e404410b007100100004500c0c940051603211208800c40342840300d071403404074004e004c3c4448034400c1500d8003040010600340000c10f4026982d07c14100c4d900030780080b00440c2c02030300c201d41264100321339002203a2a100c01410315500104008402c150325a06c441d50003044080a0388482405402400700c0c04a0a803c40900d42d001402200c4c1c040c50407001035400140c440003500300364100000003a02040311030150018202c807480 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 716543156 1250 716541906 716541919
    0x9020918010b0904110c0601030b070c0b0f040209010e070504090b1201090c08120c100213031b1a09030d0804060f0603060203010305010b030d0f0806191e090b0f0f0f 73
    0xc40e140d407280d140d04454400e9001d6031411105c810b07450010401d58809407400700040c82075a0840d0307a1182180400352204003442801c1c0039042c0014a1040d039203101d005130807203103041e928040c0104801c10a0603404800022401c00a12102c981c3c8942106e00780c4420010200c2e03508014008a181005018180103031395103040950b60410080c0c00c0480f0444940340101d80e2442c0010f00c20302c10300d200d4101c1c030f40c82580c0600c26040003482e16801070702d0080801d16600011f41e680e900c1c0d0741840b254481c60881e6400f6001010300c140c0207038564407180200040c040d54182040140401e940f0f400206c006001e110f030540010f410040075400c242e10200d60700d0024010703da07491038a20081c0d0002e000448041d400d000318014507003000a11010001003c1e5640710101311410f806940381207024001d250041e10078801c0c0040490031000800c01411242ea103114541c2e003e215101c03405c0056040303040058207116084000e95505045000032602c01c442d80300b40000804000303401004040342c141d40240 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 716544406 1250 716543156 716543159
    0xb041a130e3c01050a0b0303040803070f05071d100e01060e011d100f090803090a1e0510050a02010b15030a0f0603140a0b07030e03030a0e2b09050105130902091801 72
    0x10064001368017500d002d410911007481000105526401140502c0ca401e82c8180b1000010418061800d0b081c21701500079aa40e143c0c4030070001301442d06e40c06029940b0302424081c08600503000380007400608088060040a50500800502c03d10103424550b0400828001e4041c41090507039000c0b4140ea4000c2c542c0c0440b442400019040980d5040380d540414411800090010004411141e9880c001040c4906241c03c141c8482400f106100124980046900000c101d9440b00b404c0c0c60581410b54860546659030000000d003034500500165028860600348980101c109030141c03074200110f20310100c3da4408a800701c000a00c2c03a40c1c805003030072040480c12840742d5404191003d041703000c2c0c2007050312039841d0300098042d035441340b0151104c1c0e40204001001013031316a01016491151906450741d50341051500c00c49101100101803050f0302c2100d0714204142c1003100f140082200f82051800c00454103005502e10506216221a00360005141c40e1a541d40d0917002d48074212000301e100351035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 716545656 1250 716544406 716544523
    0x204050409062705030711281706090c27070e1507050c01050a0e03030f0307030c052503170a0b010207090b18130c0905010609060309240b041a130e 65
    0x80c6000e102c0c0c05518095082d080c2421040400c03070713500c10403032f0710000c0c26210050024001076101500c4d4440500744c4082c03004142c000c0250314580210040d0303076805080507621023002034920328500484013074003040100100003000450b0307905a2100c24200661100e29808003a01c058503c00407165040c04000b818805c100c00101c06180500110b540c20041506410380035100c51080d4071141c091050352440a03030f4007002c01c40f03059181c28813900e0480458903d8003003140c810a401e030f50300020280c031505040c44075641000b040f4002d180d03d40e0144204201940441c80ca0303503080307003208000028000001c0c888401d15441180caa0b070b00c40c0c040008981e485102c08020300c0c2c280142d4000030400075001030020b00c240103151080e604007240f18891964842e444107501460041c0042454458031401e031035035214446d08041003080340c8114020241c42c1d0400442d80c515400c0071002034030388944e0986103000050300c220755640b01d060850b0076009003511240149129003540c0a8200c40001d082c812 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 716546762 1106 716545656 716545729
    0x40501081c050405060304050a020315060f0f0409140f06011203140901090b04090b0a09060e061e030105160e18060103020702040204050409062705030711 68
    0x1056662000b01d0a0703031b081100e040c0c03465044180c128095080a2006a46a1840d0380c4540141d162810000e10300c00103d144240c0200f0501a141225440341c0e404a80c1003604441564480d80e1441070b426030340d041941000e00c0307d0007070b05d00004030141c4400c4400401035154843c00041e820700c10540b456a00002e070303050f042040e184000030300482c105009101134008840003241e00c40c580c4042c40010401a0701c4400c42074a412010045034210350406608828100c8500004024010541036601c0c010700d9180c1d49546007406111401b4000502e00c054082152141c2c04146030130010001c030410015011400600d101000488a41c480d81c01843c4042c4001c10060405d5100d4010504035143c0d806c003103800b03581d544544800c0751210302140101a00c0c20000c94148032941e076a01c2e489009040c03004104250720402040142e40b0b60a041c0b019510b51080d04101c1040080c2e510007 = true := by decide +kernel

theorem cover : BRFrame.Cov 716366906 716546762 := by
  have h0 := BRFrame.cov_init 716366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 716366906 ≤ n) (h2 : n < 716546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
