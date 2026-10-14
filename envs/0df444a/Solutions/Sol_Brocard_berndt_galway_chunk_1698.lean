-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1698
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:20:59.531988+00:00
-- url     : https://prove2.me/submissions/beb7434c-5eba-4bcc-8601-d8ddd5dde7ca

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 305215827 ≤ n < 305395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 305217077 1250 305215827 305215831
    0x7060302090d290109140a02180d060e0d03050c1801090f0308031914190902040504111e01021e0307020604031a0c090f04050702250f08030705121606150e130803 71
    0x2107034948c0029410754102400b090401c1140d0001c011104100e04c9061090141403040000302041c0125010910b94034003038803440c2e001e50b1201c0c402070f050030402144801e07188107007140a03050000d407200006007039504c4c05940014610030703010aa01c0c1d080901d10301e86e48102c401031100090b41840c0b40100014215000564041410003000082100f900303c0300000300001080a07400c241007404203c280010b1100c980010700c402d44005074107a40c0c841d041c041c080004961580182c100000c0c0040501160340d44800039400301c0c0c280d0749003010305d60005440c0d0707106520450344502004854490500ca8402c7e40303912003000d001c4646004c1c191000607105202c000070030ba10603940c42c404901d5461003005180010260b880040c0300d6040411007810600a10b84191fa40c1c0000c7e180c0003250900c03001c400c4e00c004950040050035000303100c10b907618040e000124144c0740401704404420105440e0b010704009022561041890582480c150401410008000000654004483c0f10014040c0c8013165 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 305218327 1250 305217077 305217091
    0xa0e0a0302030c15071205030f0a060f050d020105132402070e010306020708070c0e0603010f0b100309081204061b020c09010b09040e1c1b030207060302090d29010914 73
    0x800f14a5100e98098050f0060000c0501401c6c145030220500380c1d0420001c40c0a8001da0400c0d44265803100c10400540700786002d09603006a58480400a070305018112207501e6105060042c1010035040c281009814540d2003070814003a079100240008002c60f42c07008481100c5c1c8094080d8504048032440c03c0d0030103100003054294000f42000901507140160b60b0f070315178840c0b0a800402e98400500c11a000c05640c6548030354070f84210400b0412141c440d4200381c0d9801f52030080c448680b1324050340101840102590f02d40c0c1e00708801004240c03141c541c1d5100d50302c83d12000804041041d9400910102880140150740c421a03500c440c6540700301c0001c0c1101e0300d0144c0d45a0307500315a404076020b040d0041c43c60481d0711504481903200f052031008080304a080e5a41d10f62030190085840c68085070918001d0003513001081c05000583c420340007019045406081402210000d50325000c0c1c0005442c412102c901c0c00c482d0210300304020030b883c540145400078051003010070300700d002d1131050f03000b904a0b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 305219577 1250 305218327 305218339
    0xa0801050f04090615260703060e03040e391606150b04031a0105090f15060a02010509100b030705040b0310090807060605010f0c022101020309030a0e0a0302030c 71
    0x1c1c040382d80d1641c0080030165403000051100045c11828808000d0140c010710981c5840342a410304620301c1c82c00001038094039140203250381072a5480f41001094034100500c0c0e580801c21010420003c103032003440c01003014160b90f015014029029100d0341000b942849000356001101e644030003021429500502c1c0b10088200409245140540c0108281488000000c40c018030005421200c2c60240c0704890045410050b0700c440c42460000e0344009028081c0d10500c000702240c1e40400c0910021313841254444030014a14640300010500c1e004010f214005070b455008006820400f4040380c0c0d21600704d0340c3d0600040890100180c1c03181c00030700881d80903a90311521352010703503000c000d401d00d1b172031004030100202a15810303c620381e54010b03c0b064440a0030700d0000155175101728801c1c1e01c5113a15640c0e0f0030034042c0f56420042800c0c0000e4500303c040211680e040e40d200c00038802903010708244d00041d55148480c01e03010b020b100d480250741c0e1194603403200800160f02c0104500c07004100850341 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 305220827 1250 305219577 305219599
    0x30903030e0a0e011e05040509030a12020721031503020f0d17030405030a0815010503061c1205031602070506040e0726060f2706010509060309160b0a080105 69
    0x40340c0441c9466000f14503014031807000140020074150382c1101e0584149022244907210000d000584d102540c241074940d00400405921510440700b00030190980c4002500c0d2002503200c06412845405541601540c80d4030102c080580600c1042c2a45d0b15200000184900c1d50300015079240840d00c02c2401001c80204800c00c101a10107540c4c80301c0e400c0e8904c1a00c034189400d0aa03980c0d04201e820802140251000c03e4162000710744042001205070340385840e541e40c1c00107200b201810003200280198030904203400141401d5510b281d60f1005a0301c641c0c4030310701400c0c903032a819107869184055401003802030115407141c5045905072902602100e1a076150690100c4164106a05440940c010501854103442460901178080c4801b107030909058468202000119100a607510305040120f0106000c603100441000d94060300505103181400780d000c004c10500d6000b264948030503000300441110102c0e2881c525006041c00340145410543d44035000b401d030303c406001d0180300b0700003216 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 305222077 1250 305220827 305220829
    0x30a03030c02070f1205060705160314070602030403031406040b0906211f050f070e0103050403050d0617010e01020f0301060c1e0b0702010509010b030304141809030c0607080103030903030e 83
    0x4800d40040c81244200c44c41c055646210003580401c1c50400c5810f8065807003c074402d144200155440002c4000043e8210003440d40c1c1514008071070038036954110001e01074000803406034030186107d14000d4401103202805020110480800240814802ca1800140130030b40d071188027120341c1c40801500c2c03070031804240900b407010001c00000c0c0e04441d4480d0041107208000c100c0407106045401010911554075840011240401c0031124a80051001c0c3c8080000d58400d070012508079000c1e042c00c0d49440d071101191410340d60f05070094415092201310450001e6407d204482280140308004c40c11f10f07203a526024260700c018481c0104006a14140380300303008a0b040240c80d942030054012800b04010b2904005100d03080780d1220155107048001806d40d041030180300e400180040103185072074100090020200c1100202075001220340361104841403000c0440c0d03000e03006081c010354a5400c0c0d062540c3c031b0110024454810007510740b0040000903041412178041d65410704060038407040b40c41c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 305223327 1250 305222077 305222083
    0x9100807020a113d08010608070c0309050a09060e0c1602100302160c03021806030729070804050a090b0a06050307020114010621020f0405060a021f06090515030a03030c02 75
    0x8110070341c0c001585819402d000185034216007800341c0ea104103c40080b04c0d0350940700080c0034400c43c00806c0600b40040c0c260352007403207955041440790410111954030350000c18920030903030300031104040d6604000d1241134030b6108001e91100582c0085841e03c10092003844400707003c840c000307001d80000d50075180d020b802078064408682c05200002d40090043c04c010324035503003a20090f4021240c0b003011000e480000c0e08064450340d0064001c182c2e09243c00c20314014001d4910489146081592510106001d80300003031803802e00a40e65552910704110401001ca5156808041d00b10b00c2c00d00030103080d4031040c00040454009040582d00c940d2459810303405000c26500c101200c22049002050580d0001d05140d8034140c243c45800d108884400000c00700d2080780c0620300100c1050004108624000d0010f190154003131050b40e40d50150130300c031114455038260500069a440b030340d080c04000c042c0c1c030816500c11014101c090800b54800c01003500c642c06030302e010701055200d03031a442000f8020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 305224577 1250 305223327 305223349
    0x115090b0307030f0c0e06030f1b030a172110030803040611070b0703062310140d0b01030b0a03031b0206040f030506060f0102010c0f0804051c020309100807020a11 72
    0x106240c41c011308503602d400c00b1000c005001e81c00520f0b03403800100c0c8860070300040170380d521620b01008040d00403100c900400820040d03e0810791500c43c4805410004401d90304104201041c00c4a803130311441c1d4802e5089001d50302d44095640340c01c0000c10018003135040b60700881101e80041e00c00ea0f40352200e0401340c010b019040500e0b42005d100040f0700c1c04020b42e08110a1003400703070fa9410809a43c54a210382071240386040341d00c00c51182241d0003003082c54441d480b08403890300f03414100455a21850340110582100c42c0f84610150b5442460120f543c06002d29500030340112542c05096080d80e0f4080d0400418092030700a5444070203492045454403402c403005004800041441d25989140c2103981d04412583e541c021950594080d0555005028903203130b07116903440b40c2c80c841c41400002c0300c11010040080d2070a208024246c0007100890441520325801d0741e0145540c1c8505c00c0522108200351200c52003005500790801c620b840c0c2c041040041140d00081c0d40404c082c1030400120ba500003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 305225827 1250 305224577 305224583
    0x90303080c0f0414031b0109090f020d0e03041401020c010f081b0d0603050118171c0623011103090613080106060c03080a110405040203040219170f0115090b030703 72
    0x14000c00c00401c0a480e01070014003ca01b02d031403400e40d00c2074000d4944800c507038960200301d041030240310100c4103402842c484815094010f0500681a01035001e03214400791240c62600000360501031610301200201c2e442000703000415101c0301d0000003c10f03003032107610307144100800000070405a4100c240050b807100144602e031034a4901d41041440202042c0c0b00c22107642d841c00085c10021840141d40408031500000d07080c01c04840c5000f410155071015901807080b40001300340c0d0407480740300c0c0b04e05000707041007110b080090048000e00f440d100e0141110241070001c1b4494107084824004101d5903aa01c0590b143c40d10303440301b9018a0464840743c0c00c910504d500f02840441d1a42d445191f41110b00d01a03610030409442c0c0e00c81d10300c219803000b80207020980e0300708001d01160038a60019508241b01038400c07680303161003007292036008070140c0004480c0d0750208610717068040200200c2c0c07007102a0600030403080440000c0d603603102d4003912541030803d0702d4450803011a941800441c0066030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 305227077 1250 305225827 305225857
    0xc0302010e060403020f01150b12070212040305010605151201140112020c0d0f09030b0a05071704050d0e0f0a031104020c0706020c01030f0203070c0308060f21010f0507090303080c 79
    0xf02454046e46135201d181108005618020350950003038044000c200031114000580380c5010340d4001c40080340030008140c08150b11134181b811051001040040008502a45c0001034203400c0804000c01000380308040d84a0344c90500040c0c8081400022450465805040700c240b0000038500582e1001180d6041c0d01106d40f0124010302d03030380707400700742d002c0f030303400d50b07a81318105104948820b9680d80c1050001400c07802005c00041c0b400f0482c1e501c002d0b0004018144811149c0f03d1104502d1514000c4804890503001010f41607074070b60704000b179041c40e107408560284585180c03a0119108882c98130014200411010090005881d0b81d41280c0303004007464140d9000540312000030350f0300c400005100340024608610700c0c0009940e84281c0c0d009007600e95500744445040d44003294160300140515034401c40d00f01d141a11a5121000a90b0071401c80340f9440b240b41c00d104640d400c55a004081203084c03030900081002c42588280e40030290395050070100c1003038a0742c98003040140540074800b03000d00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 305228327 1250 305227077 305227081
    0x4060318350d050109060f0b030c0a030204031709130501080d080406090506070c050706170601030209031509010c1404060504052e170a0606140901050f070b090d090302100c0302010e06 81
    0x2402c03030b4020b24141e42c880300040c405196038500925110b60395201d800c081c1041031011030340d40d49040d8024804614640740150900d130f140d45449038804818400c2020040f8001382c00c28080c1400f00c00c0d0502e00009290030031507507141c02c1c02e0300e46a140806101c82004400800142001400c0d4003001da4650000111034440c070304280041c041d100c0c1d480c0181d8252003480303800035401c1c2c4691000307860710b02d040c6825000740c0c40e40001503010303401a0b40e549505000394200d01c5c0c8004082d6480b54455030225002180d00a41400f0203040c81340012141c2049041c200400d00c10700750020100c0d0304030f50742176403c0c281a12454820010400f003000700020b100003202c1c10020704940c0164490300b03581040881351040d8a550703c0140848034580b00c1c1c40007107906621401c00408412001e414102018100b07145402034500c00e8402903030002c081290002211820721241e40c00800540e03021092a0605080e03050841d0000386555005031101d10800c030310139013045e0400d4800e42100c01ca02c0040c0045800c64 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 305229577 1250 305228327 305228347
    0x203031606200306030c090c0904090c090e0c150306060409020f0a0f0e0109060f11011b020c030d080c07020d0f1421070b15030a05030406031835 64
    0x1e0b201500714100340d40d0400081c2c1208800e000100d0780240c000070010451954070100740a18580020101260b07810180610203403030302d45014005815119807403000b80e4905040c0c4400841d40c07900640e1039203500c0419000c6694075440c52281c3ca0141c43e40c3d217207403255a018002074451051350461040315001143e180005946040507000300d00c01354544080c1d8081ca004100c80d5054001c071030030700280300d241c003c00405014916a8610f100c00d40390144600e1007220066003902d03080300d185242c00c084850142ca03800d505101146200c10120040c01d1880d003122002020701c5005444500702a400059030030443d6900078200c0003107035005413a004d440005007000c44000359007400107039186c06101816003003000203008500411011907120b900300703190394844441c03101000701001e0400c4020f00502242c0e039010444000607074412002195214103280f0001d090346e009060700703250f0b000d0701d904000c00030780c00c1a411018000340882002524054503940c036800c1800320034850101c00006508540 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 305230827 1250 305229577 305229581
    0x8070305010209040b04110d0e0c10110709020c060a0b18010b0d050f09030403140133060305010e04020d0c03240b0901050303300a060314010501051005070203031606 73
    0x43c102040f5410440c0c071800400b4001070b501324205d5045220b004100103854500d16900c40c00c4031051400442d6a600c41d81c10114500010b17080002d000b140c10400d0b03040d0420710401c00c80028103840c0c3d105608102c044241956100c0700074117a0307003d2070b884040c10754454607840031031204c0c8034031420794010a5039070f2030440106901c0319444549441c02d100025440038040ca41440c090301540c0011898549951140c16210040160840c1c855480740b080c00001e06155402000b0074650054020303621507100c41c510710249240c1e00c03080c217043c14400100006420000040c0e80b0603016666001da015440c68000080019604000c3c8024a207040c2c00b0070075100c0d88491200c1a1094a04014010784007080003485c4070b00340300d4903074158410864140300c1d12004940b2070110045240418490200000305049040200c52070018551749a40c00c0040c030a15940c01510703010007400801c0b03294101004928448100f090304020321000140038000c40d203003042152103034264100c095607051218508140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 305232077 1250 305230827 305230837
    0x11a04121a040b09060604090b1b130602010c08070e01080705090d0605091609060f05011103041809021815011404050402031801050903040f031506080a030305040b070e0904080d0204080703050102 86
    0x5005d204800004e0000d0905110b16050950000c912000554a07403040c580044803007000c81007200b1007404035540b49085880604090070890700081415191080001d02e0000004c1c96003003044422124044907981100d0762607005031042c58660360325042600401c09030240034000506280c68071040000100c0c01041c01031400c8900020512119521800841501c0880c0110301580c2d600c094100400d40c054800502c01d450106d043e40c1c00e043e558104207c856500004400499464082410031440c00d941d030046130f5070078000d9564a6007410507c1503201c2d1500c0c10b40c036060000b0810809200100c01c0b065800400d0010015940c03132410702c0e680e49100d000c400c04044290b09002c049101d60b0b07404400ea9043e6131000c4102110140f842d100c0e4034840090040c2c18603840d0b42c0301c002040c0103206108108400c3d029480c04106410a45064a81240c000700004204000c5880d54400c0e5650194a103400c603070001b81c02da07100c070021184403000384100e9112014600c10451300000700301042d00940 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 305233327 1250 305232077 305232091
    0x2001021011030a050711150406061203050d050c09030a0f02181303030c050d020d0e0d02031611040e1608060a0b010e0103240b12011a04121a040b 64
    0x642210044611006031412003001c95452502030000800b0b1450550280303901c4680c1d0b24003040da11703000818160504400f20006500b4100036010003080c02124002c00d40208100340240c10b200f91540c4006000740a10300c41c10b0b41a507240c0307003c00d000c0d280800507100481c80041c1500c0055803545070490f0114503c00d412802490003126030300080000d0302005126143e4081511201c80d880d640c11001030003408483c2c0c042c405c0030320035109400707044e03c050803078840d4030310b0005501d01080201d50715090000c8141421544104982c0890107210900300705010341c03185080100a03507550006010701014400d6040350f2151780fa84040b01e007006014117040798500c0c8182c2e00a034581902040c251100358402074081654168019920b500ca9484190301002030740014038800b5504a44180c800340c00d9006400e05140450801c0c1c888444152aa0041c183d032041000818040e1f50a24290f0041d442a4403544900b01c1c120070902c0b4200000d105c0440b1a0204041d040c581458140c14a0300d0a0300d081e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 305234577 1250 305233327 305233333
    0xf090b0a050105011707120203010b040303320711030f03030708010602070302100c081303111302120438040b15030a140106080a0c0501030c080c0405010e010c200102 73
    0x2042030280d0900c540e03070603210181e4408994000c458440655000c0c0035040c00b04008800c98142e044128501c0514081c00212102e90b86d110700e50305004240d162110081403000b0100c8906038290000d0001314802d02e00c101d0131190320340c1294244103000000e802c0d142ca0f01801440400580c0ca04084000c51103555140c440c50000d0740c0f540812070340d0341c0741c1d0700000f034104645115080c1c0c2240180c04042a41c2c0c0f180c40d14514110355807000214100342540121652143d00c11000010703c0c010031201424542c01a0460500e0302c0700c0c00d0030000440240014014010000d61041c0960389101481c03001e051600c402d030001c01d0a07130105680200112070603500a240c1c2004104110480c541c240120100200280340c88083c42c4c6409074000142804110207642e10180000d10401c24416514010301a00440c0032140c502800941500c2c1008801400c0054003000c00c0700c00038016082e142600c0003072910070805043c100068414080003d03018180a0300c0c02c5043c504075031160a01c1180150a9080d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 305235827 1250 305234577 305234581
    0x3090a0f080604020103020f212505040b16020a06090e0c0408030901032a03091203050402060a031a0a0e1b0a0207030f020a090608071e06090e060a03060f090b 70
    0x14005020610740507501290304901c02240144d0f22030780103000710441907100c0710710300a800000107900c460740610800303e1000f508104040d52407803040700c0d4100c0b84600c0356080d109002002c020024404d500688269580200d00780c150220480e1850b1a41a4041c0041040540310b820180c4031a090388241c03140001d512000402e8203807484151130480355040e0056060040e403000560150022006070220860f21401046004070b0800040b91000010740380014944543d003001c106100f40d042201041c5404d103014040141c42c1c0000311003808901e03180001e030200d20041840780484102d114141e0144910310045008000014154010300c0c00824440c048140b0448401690041942c004050303005501f0030008252401112842d1a00c0244110084d680700e05071001114941e80214101e503200d48028051600c2c3e11110082d5040355410100c80a0b1801400070483c002c907018480c1e01c40b0036817000c40e20a4071000301c80310145034012020302140c050f40d001c600061130a411300344c41034000301c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 305237077 1250 305235827 305235839
    0x20f0c010e1b0409050109020307061206050f090403080c28020f0606010813050f010c03021b0c031b061306030f06050f030a0602070f0503030106211a09060a090e03090a 74
    0x9240b20021141c5400030458040c100c003040f0007028400000c1e40c0a548a6066900581d8240600d2024121584840e00840660342925044a240e034000c68056040805c00310210f5035a010000d0740164545844400c55644482d0b8071140cbc0503111042706158903e410080f141071541001c2004906551300326040d04900c01c980f5a9074410540b0554040344000d004541406407440d94918498047c504460510401320a16070845410f80c2e00c000000303030302154441d00b0900756104401d841c01110014416800d2000c0040d4540d588514000748602414420030310b030b134540b04191942c1c5500c0680e60079580b07580e018003a02402549000f10b2019191070700204041ca8450041c40c001600600200031300343d2a13944047c001e5115840c140d40d215400303803401c00001c60410095020b00b260b0b40e03d2400e0541d407550307141140001504007108150501850b0652500342403403c41d50040c2c100d42184141c0c8950b0049a242c44190f004410154100a00da1000d41000001095001020b031403000790207a65013 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 305238327 1250 305237077 305237083
    0x10501030f0b0a03151e02030a060f032f03060a0606020f03070309230904051f020f1e041805060a1e06050901050405090702060a050702160515070501020f0c010e 71
    0x341900d40e00c102803610901c0424030010662041000c0590300143c544132800c00c01e11401c411480011b40c1507000010400e1601c458060a4028030034240e4011026043d5501e984805641c0410f049290054058100743c0d0550940403528001c0003a09440b41410414510809820300303028060251203001c100421070794000048410403601a614504031078204290150203911104001000d110010103581180c0e94281c80039004134810b80042c0540c00c1d09400f0100c404c004100503c01d160310611204100070807800c116040002c985c6402c4031310340a0f26520301802d00494000c0188421100400a9003084a038441d500502c02203850008040da54106920540f48180781c071f02100d48042420001c05016502401340c1031014140141000c0c0c5a401007034981004940840041c3d0124090188081c80c910445170040d410344080c0c824a41040c0408021290134030860340222610203103611182ca00da002ea550b160392050096645550462140d0141d8200701c000c80c919503c0e200035400c01031000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 305239577 1250 305238327 305238341
    0x105010f060905060304051c0504031b0b2203122006010b1c06030f080d0506011707050a030f0c021c0206090606040203070e0910180e1209060c060c03010501030f 71
    0xd5890030700043c10402030150580010707100b25602d216403e0540300c50600e220008100540c2c85d0b0b94151240d1541c100800ca140501464241c400d003030f240300340f19900011084541e0b40290403030103017007581d1042060200c0a0f03d86d00c054030900c0509074001d242a444032008541400300c05a490001c5480c0c1d4403581c07a04800c0c8141c01000000b0000a12034a001d480c0320f011110490b540020f105a0341d44940202c219090011a0b41c020001940400c1400620660390458001c0c070781f4100c2100204024400d06c24060b102c2e000f40700000c100c00300a988680c1060b01200032800060100ca0079441000e5aa0010310b056000c070808101400c102d024800100e071482079014000400c6580c4030030090200950000e008082001040f4280010640700d549945014013245c200c1a1800792410110100801a850318281d6441c28080402c00c000b400144030340c0e001100003981c5640726512800108035104210802889010f03110070084103a801902560490390280c80a00c181d0b1544440b8104442c45 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 305240827 1250 305239577 305239589
    0x12151f050c010b0126281401080a0203070e0a02040f080304090e0f15131218050f010c0204150302030a0b01060f080610080405030d060b0304061d060c0c03130305010b030105010f 78
    0x2440c1840a5414003018110f402048a08408a04141b07610700000c0001d40d10703804524250b01c0c0d11000b030500ea410b52102e4014180750f0094403044106600003a1200524820704046250340b001042c020300e595412900200024600c1c26645a620342e00b8940325081449082c01403441c05000810703010707000c18044600c040c910064038003c0e0426800c0408000d000e400100d100108140700b000240c03011401508050642d1108519500c1c0c640c489a03002c5d90a03000140151600603e100d004d0760032120984e6829811600429400c402940740d4008d11080e82c4060341c90b00c10526800203001202c0811030580b200b0f9a14070b03101491b49071041c0d95440098480c1030300b00380417050483c042449441e16580045c82003059070700e451007204400090310010b404c08805920004117101c100f05181c8220307800041d6401d010003545c445204502d889a40091070800c01d00d03400900e046141c981031013211118489000c6003582d1544a0504a00a040b9407420a000350f1078000041181d000c420262412584 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 305242077 1250 305240827 305240867
    0x406030b0f100c06090309030b040b06030601080c0625020d12080f0c2d0408070f17070e0a060308070b040201080f060f06071407030f03080c12151f050c010b01 70
    0x1c2c0f566603040c000c101040080d0200002c90b0004400901100b407080d0107140141c8a000320750911100309810070324184d0000b846a4003a030181c0c41c0035101c0b00280d50000b9070034660034040c542c0181150040746c0c0001c01c000d500a0b09080c000d810000710880d40703c040500356079191880d946481d49003941c1c200a41c0c1d80c041031581440092110070a1810019a660054511102d85200d0060b0015143c2090704900e032507402485003408000200a03019000740882002d455601c4000341e81c1c0c03900c0740f481e401381d814803a1850001914407059600440010350740a000a650784495090100c901c94042c0c404034002a41c1030007003403204078510440d03405802c0c01031020102041010400025522071782048a101800c180c4d01d4001c42d0042c44010015401115503811078800c5140041626070020300031030b046841070143c6054030046a13a45903010394140c03200300d1803029803000911070001c60f4100503440c1848118520f41c0c164000c0241900740130050080c0600c441603001510074503400d14440d04004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 305243327 1250 305242077 305242097
    0x50a23042d0b22080c040e0a0b160c14030a09060c0309090209121006050f030d020c0d17030a0f060501030b090c2d03040203060604110306190b0406030b0f10 69
    0x8490840144010310003c501e40c000c4200c00300441252414a0b440182c0d0f507002002c0e0410507040034094403100101410180034030540c0e560b1080340408005e003e0000d46d2500d030030400005402240b41c000866045188141c42100300310000703580303070702021908000419003e80040c900780941e00700381900f9031586400c604682841c02540c003d401210051303038841e001d41011080a6014454031807c0e1003884004211582000d042c8804142c0616515010b540500c80c04c0d5405540131405003c1144121807075001c10040741071800001c0038448000c6050b40e400000e1040c4145154407108455a420400b404a5036075400154103c0700302081164008003080d0000b842c0b01c0c00c100041580c4021310800448000d070000010070081014a20596521800024082545000c12039580c0c016000c440c1072100030444240c03101640800380c5070501503028051141e442120104104c030190810b400190340343d554600c0d000707010717196a2640e140207218030303006141107041c0107854813888046919070751100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 305244577 1250 305243327 305243339
    0x9050102030a1809060602070e0609010b0d0b0402091002060708010b0408120c031917010f05060a03050a060e090a0c0e090309101704060506040e0f0d050a23042d 71
    0x300d610f04444a0031218210b0000c200b018443c861701010b844564000d04a103410720420780c114036409000faa114840c1c6030010071101450fa0200c031380e0084440c0c004240c2c0d501d0b0318007041c040e0180030b611680c0028401c04102007035a0005020f4855410382e0b030707002c4099a982ea16014603100f24003910540d40c000c8628000c0c075650300b40080c2540c81c0e031070088900d030042e0030351909600701c01840f517080050340f182c0120203e241714101840c054038051040e5807840b407500c4006152407140e4030780c2d00241529400051035901659008800406940d2160007180c504081855111b13203040c00c0482e4525a0340c00f011894900303ea145510800042d0b00031407610a0f404c0800c840300760f00304072180800c01c12084e4044100150307011640201c3c803601000c40c050501804000942d90f519207074000b00e500030039400310051b00004072a040c1000d20b0602c00d903140700c2e00c0c0b000c41d0300d201c0c0c4030148940100d03811242c80d0b06c2d01e017841c0203104480c0710102c9400c0641c0c030301d50603081ca007851106103480801606014029 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 305245827 1250 305244577 305244587
    0x5061e01020d03090309080618120a0e0f01030e01060b0c010c0320130b0c2107020102060105040f0f061205010b0117160e120c090a230601030b03032809050102030a 72
    0x980170341071151040e959400788500c0c2440880c1c04603040d81030701d00090544481003080700c1e100840c03027000c0ca00340104075000410040d010b115203440f41c80400004103440c0d009034445421400303080000c1c0542032311100818043d60290280b42c0c0e10b0342c82e180458170624401c2c0304107905130b80341890012034540c0e0100d40d0b92040d0824001c07a00700d09200800005c4600c0104010a220034240c1e028198440310101c0b14040900642da0180c2c1c2000208107440050b80e002c22607905685048500051282200c02000000c0508540e2000710310316001d004108405138001e002100f038840c00080c02000701310300c01101c0200c05859041d00080d8500d001c0350726400d1419004200121900d0b00c03031094413590740020000143e0440d41e50003a00840020200e40c100001d10f10751003011018188403460384000c1101400c0c010f00f9440c203510540c917000c40d1480e031181e08000d0000300006d00b04c0342c891010350b28081c022a400540885d0720323150f2500842010b03000304070b50000c03180160055401c0111910307007618 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 305247077 1250 305245827 305245841
    0x70c03060b04110301031406060108010305060a0f0b030102270f090f070e0409030509012a031b0c03030914010305040305090405090a02190e01350304030606030605061e01020d03 78
    0x40e0103503d614000c481c0515200185000314000c18400070040b04c94071000e17080c0a400303007109040000650050011410004c0d0440c2c105d60b220710000f44180741643c04500502500e9200c40c0c1c1540001a200b0741498545c1c1e500c0c14104524908500c4942c41c0030403c2941440150f1440d00107409200041485143c00310381644080a8100104510318410009044170100841140070881c081440da10030b50340b000360440915649000c3d01c10034418005144400d2800040080402802480c0f04403138042c200c155100ca15441700a903404503460b03160140444407240226400c441c42d2514000c440d600c00c0c01080c0c02076800d0780b50340380380030146c206000103040001d142600e2441001039402c016210f26902640112804c5d004a58150400c004409441d04c1a40000341404004022000c4200010411041c0384490f404c2040600003014055055010743c3d840585074504d0844000288074142e040140f040c10100c540310808035003070201c0100848104d00290042e8054101c924030316000c4d0780002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 305248327 1250 305247077 305247079
    0xe01140108070c1a0408180405061c0602040806072114040b1e0702030a0e010c050c060c1e030711091014060c060a0902030606061903020a0e1c0b0c070c03060b 70
    0x203200c90300b800da1280030090b0306582c2203030604c1b400568108501800c0036070768211a0211801c0c4a542040400030303489110850200b40221000030083e020030419504503401094070b08140ea0361407034502e5000d0050403034919014280d80703060300ba06200c04201c1c0f085007501c0c400c0c502c445410b1340700c603122801231507001404204007054610402041411103d40359205406503401517075103080c0691b004142d003801c04041418802c104100d50001800862000040c11042d91080d4445042d00340c00c030719105806c100c00e00030741c4240744412048040032008010322401001982a040004000c1c4000b00030100c4003281d000944582c14002641049110b1000080c02004c40b030a100c075403c51641042401d4a03100d150580c1c84640303400b14103060003030582c8848222149800c051540301000c041c8000c40500800b019400101031000300e010300d00454102c6c002601c0c511620010b0020700c0071501c80b0140985240d1210030010701100300b06e00c100c90360503604c4418280d099246a803003c010700349070b4600c5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 305249577 1250 305248327 305248343
    0x180106020f0703120e01090b0d090c1413021602151911030304140115090b040c02010608120c15090303071404060905040504080409050426122205010c090e01140108070c 74
    0x2600c3ca0723040002e4903915201c0e500000d00880c0519050102c42c007140e01c502c40c80c158601d80b640701580d0b0b09800d5400c81c90395500c05641c450380b42000c00c03030039400c2a01c003e52001000303104007035940d1000080c0940442107440c088400000d000d040d2440301885c000f8200307a41c8104002070014200200c8004020100c800219144150406183c801c5600340c116903103055507811280702d2440c1c5800b8030350101200380001c00c800382c20034040070344a101810140c14090030000c5d00c0fa4550100f08010742441d00940c020030101c3c01c1a1101c107407250300a40703208001a440f2014814800c0a04048030301b2280d140d11103144491410090202411303005000340e4800200b400006140b81139030150620991041036580081c8000b0740c43c4440810741007948003a0b40300f0030300100d0014141801c0281c1c2141c100b4811100d5620301500085114503980e8000340359500748000c0101064004449800b5200c1e047d00b0051300e60780782d08005240000c24012140040d070b409011075082806124075408031409000c070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 305250827 1250 305249577 305249579
    0x50906061f11010612030e302b030b2b03050d06060c050f0307080409050901020c1c020f0616031d1204140f030709021602180106020f0703120e0109 65
    0xb80d0f82184c1c103036440400300800d81d45100c4c007010f80c8210303825405030048071a6104d941a080300a03600411008050b4204003903000b001d0b50369070701080f0100483c031205510900c603411090750101d0b01e000c0e407803028001c41c0c20b2840d007801d549030200c500c5072039030024a1104880c008424080040900410b030036018804c0400c02d17296603071094003400300944901c2c0c59040e8007040920f46145030918201103440391750814070400000542500456046401e88800441d00d038450040c414020302c583e880c1a01181f0501200b00c001d0401c0605190010300343c1d07007d465070480b292030303000d46600c02107030422026064142040c0d8210b020b07607c080500112110aa402c030060005810300c0c0044198100035080300c041010045410700165a0340d07107140c207a420046043c410004070750b07104403500907400c1094003c241c0741d130002c51030034461040d660000c2039441401d0304800100d100980a0041c0001801880c01e02c070140d00340041c580003201d6120740904210000c0100c125440350100d60a98104814010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 305252077 1250 305250827 305250857
    0x320031c0531081212061302090303120105040b0a0e3903090c04090812070e13050103050f06131709132406020a17040f06020709050906061f 62
    0x92416803610a10301c09807182401d2480f00d501d80862141c0180c2409000c001c1e0f0032070a0740122109401440540f91821210140340300540a030054180701a00740c4404181590900800c40e59030703040f03480554080091601110500c20501487e00440b41e010f05400041401d80007000422240507074000e840c0b5801c00d2040701092000c1d0140e04000e48180404030600005400a0060751145681103508000c070080540c0c9043c0c00d40203d8040d401c00000c1080000c1404d400b901c000440d52400420503c0010b0690880f100105000c0c0416515072040503080d40f4801c0000a115000340b410032500140c4403080c0e9a40c1c0303800003c0c4c00044c551f13601d080c0a400c400d91513805800c07401d0780d090040401e8802e59000300745140104042c401541900c5084100f09650f00480c00210840d0800314044100d0310280c1b004842e44200c1d4040e44055030054400198a540400e00c0019110040e205000c180c0316001c04581e1a1025190a0f6201031201c148400c80d000350707541c000070044503007084510810691 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 305253327 1250 305252077 305252137
    0xb07060b0603010b0a0801141809010e0f030c1c090e07050702092401080106051c110a0201020c1011030c070f0b04060b010f0201091a0415060320031c05 67
    0x84d1018071101404152684131580251031680901803444a5841200340320340000d80c1b006959a6143d10a03100001140d100034081d04401505401741c8112035a0304071100700c41c1da8a43c00000c2d984001d00071065003030217200a09620110401d195690303d110741d420003040d9144964040c14420500c401044108016200c690942c0d100d00080c60b2480d07001e590146042114200161080b410000c03201d006000b11b68005042d0742e140c24281c980101480b12103101803004004250b00401c0c51400810340400c01c0b68150010f1592000131400d4480c5280640320700c0c42035034540c6015400c984000e100103000c2d400e245019041c000c0c040c105400c0c210300151034081c002c000035901515501d4403502c96401710350f00080e00a00c4000c3e41c6c8020081c001e02a100c41d13000008594000c01d1848400c1e000c1010303c80342032819041c0546580c2c0801040c0e56a2400c0e83c3c000c10380c00d035840c0340445662080246403038082200000b8041c1e02d07948401815580c1e030b0441d80303503203d5081c0039407296004141c2090090742c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 305254577 1250 305253327 305253329
    0x609081c09181506111e0f030f0a140c03070b04081b0114070215060d0203120d06050f06070803040f02120304030b0901050a0e07060c051c030504170f040b07060b060301 74
    0x15400000c400d408a042210090216040501401040c14045484030400201e8200c000f246e52101c0c07050020360b40000381000b0f40c0450141c01c900c4046076004400002c07900822150380903840d20080c50100820101c1580500b000b41492500207001c02008285103000150307015205403585454001040301d908407000019020f40d6080c3e5560308030152520100101c030360010154002040419020036980411220040090b4000d4070030fa2060300854408005260310b9031482d82485032502540c0c1e540320014680d5100b0300c0e1003030280c00d010300d000b4100355003110a41c0740c21800007407940c1e990b0f44400f8171010001c2d81c202c2e001a254181804031000920180024500c116481480b13800c013000c201c0d082d103901400c440c0c0c40c180b070281080840600007400004480cc0c608207512405d5950924904020038001281d070240300740740c00c441d40c43c0d40c10351045105d1071082ca43c501e000d0003000c0c8401d40501407212000c621000401040c041e840b44030300a8103209104000c040b070752903003030400b02c2c0d0142c07c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 305255827 1250 305254577 305254619
    0xe220c09020a03150905010b0906070f2a05150a0f0e190f090204050d15110a11060a06031e05010605300f07050d0f0f080d060609081c09 60
    0x7603203130340000d0404420071160040c031604500b80650b5060540d15180307480f0381071105119030400502841001a4900e203960ba4541100540c03406600ca211410a0381d2280c41c528507041421341e5004c54603280540c4a82c101d010340c122007505142c120360301a00c0c69204042c02c141400b1894280ca600356460071101000e08400500141c41140303003891101c0380800790b4101d450310600612050109480380d00c0c150b10740e140c0040398407080e0001003810500920420000401400c000500e06941d640c105c8806100ba1038030401311069a50790390000070450f4482c0c0070040c010040c420030042c0c1814540e46000910340039900000f1030a40d40c0000955040d40498084214140514443d11620b541c0c041002c0c50310405003c0d000c41461911807030b803544082e0003a103100c2c1e203030329640b071003840100c844144810768040340010b0703649440d081c94072043e0000c0d01d10242d12400e03c06e02040080c4a40480030484142e1802041132071411f860048c0111941f034110006c0040d01e80c000154101d02410040f0f10f908 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 305257077 1250 305255827 305255831
    0x20409050a05120c0c0f060f0702061201090914010b09010e190e15180307020d080909090f06060a0806130f080a0810060e010f08180d0201150e220c09020a03 69
    0x80e043d141d541800c3c514140a485140c0800049900f07841c7c079000c4940c5c240b451301e025a581c401c0c07880012603c0c000c11501010118840c000801d0210140d4000400c150007888201e9010909001050981d00d4010820b9003022144d00100911550f0f0549290454007603548103940b0304125140804803240d1410000d030350362103d04c80050f882d004001740ca030081304445a00401c2465641e0750b03640c0e4840c0b00d50080c05024400140b80601500d00e041c0d03542d2907001000200142010485a0f50720100f0a000101501801003c00c1c0145010301c81001254480c0001c0c000c40c4c1e33103890060960119000064505c419582c09060004903680d00a100748803440c1c950307a40508180d04048490301c02178010406005829030030106503a04001e10007106000e074a0210350564030301e10710f0100da8041c0f4480b5403580c400c40381403440342501904074200c40c0c03000b045d2040c80c1c19a0360200320021001680c18003c103807040e029016620a60440141c5218024006000700301c0d0b0307485400c012640611400d02c0003076 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 305258327 1250 305257077 305257087
    0x30f0c02160501020c18090705120114010b19030506060f04061806022a0f060d0b01110d0905060705010b0901060903031106060f0d060f110304140105040b04020409050a0512 76
    0x1210400000000d06002e1008007496280040442c6d01c858684008215040644001848980040101001404015081c0c1d1200c20714105814081c2803c3e50401100381444030001c52510003081c20f03149105504455032409001040080d001414044c103400d4002804004c001c001c0e000c07420003000144426074400445040ca40d030000c0741c44200380c01440454105a60880c0c44200007206140700301054140e0703003000c00c070800015515091108616070445808164000184582d030302032a103554013038903041d6176801d5140e07840761134610b01000034000c290410004d2045040403000b50600520400c000507051b01c0e458002018801c091303020400041b0084010700c00c00da8001c80c080100481000144841d04141001500c0304000b0703500a0b01445001c0500001d105050b00001007403803500904104500b44101880300e00d034400c03901681c440409022000061605115003841507412440e60400d41d01c842c1d0800002c0c0138031803415145440b450032808081801072054103800b11a400040350303a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 305259577 1250 305258327 305258353
    0xc1c0620071205031302150d060801060512163f031407021f0302120f07090509070807051303020402121006210c1103070c06030b04091e03030f0c02 65
    0xc10702c02c0d030505007040024010320444046149142480075070480381c40c030f2444003070b002c1c0740c1c62801180c580000c0d00f070400300002000901944a2801d55000761840c1d58542448180c160351a040e583c1000c5110407403600812880d800616610801004c2c556001c0c1540502c1e032a031010005000401c0b070040c0710202c1c9860800d50080480000f1039170600000d82060000e4000601007e042002da03c40034410100303100e6410701c2a412111103218143c0340c0f82d80c40c20326058044900c103080b108a000b092440d039003c80c0ca840e00f950407a00ca01811f54402c0c02a0713540f103a08030784940141e001d1801d4068100c00100c0180d40d1800940030740004070100700160725044150280a40065000009102040401154044d02c0c86018869204107901c040313500b070710038081200e5082c01c6a030482c21600022440f0b43c20010002c4c0500205c03511944e00b4080240048108800c981034460001d00b60342104408451000c02048002d01c8940242000104000403944d18030075100d54022800c01a00018024086 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 305260827 1250 305259577 305259593
    0x60303130905071b210519081503011401060e06040302130b150a0203070204050603030d0c020a0b010e070813030207080d12050f010506090d0f0203030a080f090c1c062007 75
    0x2200b400d0720280d41540e015807945c01014001c100884021002455240c016500400480d00310701e01d007504000041d0100000200380400c02d4450031500d22510310b5840492a050052a510121080140403540d182030070580310404414421500404103020010150303030303803d603001250200210081091040d49081014400e1440403000345000d02b48001c0c49410f600000f900d9056505890006082d00c2c0c42000902d5030251090070001641031003e039408050340410714507000392181c03000001c943d813104007004804004848410010300b1440c00a03a55450440c50101c80307034007078019142d586845400c1241022203100c41c400205400e1441c9516030851480381c580d106250820300d4016504000020700103204800000d8800d0b0240c985120901c0041243c01d00b00960007000c81c0d540e0000d020010b4072640307044030b60001d4400c200c400074a540b003000c100501c50000c018941000709280343c140c4440329030350100541c1d040c0c2e80c840318080d0205e801c104024800310f18405882d207401462812000c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 305262077 1250 305260827 305260847
    0x100e030a080c16140103090303090c0f0303080a20030601210b03070b0c0307020103020c0708030301030609140c010c021e1e10020304030b2d0a0b09101a0306030313090507 75
    0x10310041c01c0c5404000d13030000100c400510280034a00031a202c4000d00b401c40140c000700c1e4000c3d000140980b40054055020440901124800d03151303001300d9928842d40310100c5441d044a1400445681d09040f00f03210300705c0046070711143c1410080c2c18410310308040c0300c0540345800203102d6180d0b155420b42c26460208000001001d101022920305010301809030f480c2d000c2c00200031f05040d0003041c0d0b40440681804a5009041902c003260344030741c0e480c1808405010507001c150f400020310980c00e092448045144403900300e06844208a140a81d82440401101340640e10716601c064000c000f419a1200e59103a44621074658031414000400b08205151508460f0ba0040d94400c00003000011141d46001e5840346841d5a01d102d050040315031003142c2e45040740302c0b100f0108102c0030000401e00990048a2032402603030240c92941c0c0d807100040c0a0260707401030241d034a8001d50341006540b0b043c0b00465100101178160f90601201c0101a911f06880e5002515525120010400c0544d482200c0003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 305263327 1250 305262077 305262103
    0xd021b0606031009030e1002010608030d0b0112090206090f21030c1501060807120603020918010b040605011713080c0703030e19172b02010f02030411100e030a080c 72
    0x1084043d40e5020f000310042c106d1503402900c0310300801c4d10070f5000303600a03c0108a4101500d42d80d03051244d00d100140300c030f07142c0c45020400c2d150700300315a21158803503c80501c0e8003400c4d40345090700c00781c00c009034103200702c4c0c0299100c5e402100118450740c02e10181c1204201c6003005503295142e6038012804d102001420f040c0004a2000401285501c1005235030886100d0800603003841d01c0b0300710310000d8040c50700065040607550003403002c1186914007100e200c5011500800076419904100800d45a041c0318181c0003440248002c0703e11035078115001d800c59064205078051340320740d60303410005d03810560051302187c00c980020814150044109007030040c0881c5e450080390300103005020240743d18094507070484505003100070310410802c041000034a0000507034040d04c244816a1400780942c080b001c1c01035003481015a010240c0d030007501e0003290f109800c650741140b03000c24005450502c0e00b01000b00011007040d00d2003501c2c00d02801070341601454070b030740e600c4140c0d9030a9803a107041c0440e40707 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 305264577 1250 305263327 305263331
    0x30c03010207120c0602041a1b0105010f050f0f0d050105071d09011205011404060b01030b04110909090a2f0d050d05160618060b090f06060d021b06060310 68
    0x30500044030250010fa4040507800c0407080d001c281d0401000900032500484181c01c07a68200b8032520746240050920407500b15181c1c0c0c0c20714862401c5909a890a00c40d2460541041c0b00c24000e500c0c1011600f005043e01a101220760b021070b20001d44070a10340722041c5c84a17551881072200c95035010948242000b4010030100203030b00c410010401d4082c2c1481102100700302105c1d0f0408008080d0041c400d900102c138101a2503040604102c401400000034041c0402d01c0d00c080007180d42401e0150580a150051200b03041a10352003c1c440d04d49001858599035000310b040c1000001c0c6e1941c19081074060030050007a01006120b4404503586000c04480e22400c200d100120000b0400030340b130b00c0180b0311031030919240c008100820714012141c860007002a030608101d540c2c5002100e078201d1240e8000e6034240400ca0100040c0880120141c0780300010074039007000600d59082c400002d06556032490401841c01e80886070202c13444540f1020704546401c01402d110003882e040098181d18003401d003003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 305265827 1250 305264577 305264587
    0x3300903030403120b0109120c050307170c1536010314151203070b09010f020703050403060507120212040b07020f0c04051054051f08010b030c030102 66
    0x134250440b80034078503840c10749990100c00076034420b0310644010000707504510342c1c0304094903040c00075150501505002c1e1041e190002251480122000d58003024080a400001410814064984011168224440c00402490903e4400c2032258001032822644813074050550002114010174400a100d040508041c00d01410a04409001e6000f843c02503c134054110548082488440c40c640c07102414080440d8050501946000d0a841000c0900003001255890817441040340522080070700050018001407000032107981c4125004000350030a0006c054580b103e2400742d81c407105140c0e0700400d00e8001d00003085015104180c00c19090f0002d030000381c03400030b603041e91007c8500341c0e244251f803604085412035a49404c24006401a0600c103519105600d10795955510b012030075050060754202051848040040c480c0068130580d07590102048840300c02e00e01411000e0013000900e41005010b6600000e003954500c01424850700108605406000301030404a603030708528080d0740100300c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 305267077 1250 305265827 305265833
    0x1103060603130203070513020a080906040302030f031009020403030f030e060f0606091507050c030d050903070e3304060f050f040507020f070906150c030906030e033009030304 77
    0x90380d070b0048009107030007a90190340c00003030702d009066401329402000d160303034003a04100550000c4c941c0300c0160325034440d50746407100b00c0740d590030080f035000d401a00240800040804d141c0021908411940d001407103080d01c42d9121000c0f03a02c00c2d03001301d010500e10b80b43c20b4080740e01402285081154100902010701d003d02d0404d444040040c140ca00c101000510003010f50b94605040101c004260078040e141d00f030524169544841c0034103920b200c0d2150300d2035816011701c100110340e01c10b030015004d80b04952400f2210003860402800090704100b800001440701d0030401c1a140b2040554414031180c462404140011280c103600600c0c040c45503204c0500c03140d1180381403e800a041614006055510000101d041a10080c0103104a0085080c00181440c558001c03d023a0b6a15080380e002e10b140c100801d440d054030506000f00031030140c40d01004014040c0e40280340c1d481003001a80e10388903403c034081000702100411740c0141440030307460540c00000002ca60f94491580070080d40b450400d51 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 305268327 1250 305267077 305267089
    0x31b03120402010e060d24210209070908031c050a060f0b0711090901090308070e030d0315050d140c15220308030f0609060a050d23030c060901110306 66
    0x180701a05100da101800e81e0300351a40ea044641c411a845e904100c4086400c0d41d80b101e40440b40d090b900c9031903201d1404103c8a1203880700940040400d01d541303176003010aa081c841c044c50000c0841090280f031110000b0510402e00c010500c0221000d19840000b0746900c624044a001600e4118810b140c50420f10403100050070850640f466034142580f183c14034034042c0d07030b04949044002c0d04030712441c0a0002450054000c902e035540b2a8a443e81d16684100040300c600c01102c800c00d5041e44546001940340740281e00c4a06028114020300c590f041d140c002240d000300c1c0c00d80040f01c83c004013070307240000d484040c801e0006410080380c100061581d040031b481c1180c0940781f0302c8403540042d0035000401030b0100d0040c10085030304c08801600c92809024400070150b003228040c4c0241d04190001340149400c2e036511007904d0004064456491007512410001310f00c1244403001c03100070b00c0243c20400400c0000d0440319416600401080c50004651803d5038500c4890620a410a105004590b6911 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 305269577 1250 305268327 305268331
    0x7060e0d0e060c03220f0801092a05030f030c12030c07080c03220303301802030f010e0f030a0f03051905010603020a09050f13022a031b0312 62
    0x8a400507111050701c03c1050a51041c030710824180911010000c04e84405001504212060111610000e40d9201c0b00c0509803882d144000744401c9400c880441001d1100036805040d190910894030700940b1000400e01c1c2500c0b1514240c010fa0012405001150080020041070f850414405055080815003060f2602850310010301100d8003181d500307c0a00300f002074802d5800e14551b401d00350b1504440b43c41d0203958501040c0c00040c0d41a0340c07164850100858101b1101e00700710301102c81032142c81043d008040142c04104400710780c03403407600540d50812102d1562481030000007160034078480d056243c196040032030450360300207100d0f510803280c02c0000a04000a94200402c03665501784c00c801c40181880036041817035141c80b001090144d030607405080741c1061a12040407050329841004030030300027032010036880035441c0041086002c594000d806441c8002c101000700281c00200c081c8204181c0340fa0b01e08540c404200c1c0000c1c5d810750f515211075651640042d5141120100402c6804940 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 305270827 1250 305269577 305269579
    0x150a2405090403260709090b0f0a090b0d0b0a05072c1c05030304050f0708010204030803040f2105031e0129040906120203010b09070503041b050d060207060e0d0e 71
    0x442800862002a0303208150f81041a40300102d0135203131949018001240c83d01071940100c3c40c0202c800c0741420140160342134242c004140072480c0707140c4001031024014440c282c0350028404586000080c55499440d03002c0c0090140119441c07601c454028100200c800501c04c0100084054546014015440c01d040040903508540a000441c440e1742011020b40307001042c07440004100814004c01041e0340b00b00c040040181c41c403155850320000d09070b00550201800c02201080810000795943c10a1005d00f480740300b40a922000c50300300f03482000102200c020100d54000104038000d005170840c6d141181804400e0102035042c209001c16482640701c0075400041c2e000600b901c22101101668000c10180c00300f03024860300e481c02010f095054002c100d000350309010102d5201e00c0c085c0c9080d441596a9510030b4113542d02c649a0721715190b01f031191604c100a0202e4003141131b440b46912039103060b0050f030016a4400da1403401008507594200d40c0c0c030180e00503e080e0008075a10454610011070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 305272077 1250 305270827 305270837
    0x103080412061107060902090601080613050a1b08220f03050702041104090c021e0c0d03090305060705040e0a0c0905150d0e2b02100c02150a2405090403 67
    0x4500c0c900b000080445400d0b01e07103c2200816113400b00b107400e40120908600c2901d8a1146898810064076204c2c4143d03100c3c0c1d48000188451450701a0030350015502005aa0011404d524407401e8600d0160300100c40e88000b0b42c00100b00101525848503540410f201845910494402610390708400e500d074002c01000c2107400100d120a660321908040c02400c54003507615030381d90359000c001008050b03980030032002d030103110410707922a0000d5601e850204124400782118080000400030b00e410800411402e00c122640d002c80032440030801c41e4803400b07454440c141d5860400004c0705c0c034084002c01d528900e904260500e40320641c001047c0046403130540c2c1c10900b0ba40e04441c131880d60f0080c0500007951700d25105121110b2100061900700f103440744280c040d4001e4498005a20420081c03a9410250780105407240c0c03e104664003402f2644040d1040d242c194000800a400711603080c1c9081d985035807905e08072108440e280e00b50880e9802c801c25040310803450000407641a1034000e00180900c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 305273327 1250 305272077 305272109
    0x60518100c020909100e010e100908210f0108030a120c0c0506090a110a0e040201080606070503031003050d030c09140d05060412020d0e01020c10031e0204050907050301030804 77
    0x500855a00e400301c1d41c000c080d80b07840d01d400c0303070059075400c800c030300705001c40303040400385000c0d08010703ca150030010032880980300350100050060040d00445c1404c40c0e0203001081021849000100000303000c202d610454006810300900000a040060301f1410a80d08108a9504415045410362088030700c010808210100c86101c161458010b80301c0c090000e02541e010842c400b2400300300300c038582e84544282000313070189200344945584140500e6254009440208000d58002c01e03945511100052002e0b10b042070503074461741550030035186901081c20503101881000011b11107003895600d00c1c0b6080222441010000700300b0b680510030a540d21030002d64000300d0b0307100d0002250307401390442d003258100d00b41443c4c404189042805000014084d031010b40c01c04501c02c06040054100580c02040c10b09401d501f04a081d01c0224032120034940c0e81d400d81400420051103404410910317a40040e2030b00e1800d418040e10b00307270092030002041000c1005100207449541910207442c0c441d41c0c0c00082d8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 305274577 1250 305273327 305273359
    0x180912041815080102070303020405090f040f1104110705160e1012020a09060f2d0302120c04180203011d0319050903070b0301141f030e070e0103081201060518 70
    0x581140d00300940340c4d400000c0e00c000b41a0140c008000700c880949e52034030607980760460740c0c10503207041d500104080004a121404500407550941031710b03a000f000041c0081c6c10b906903580d6075110751003c8886401c005600c1d940011b103c0c907294020803203506a0402841c00800c5003004160368000c41212030500305040c800d54841c1c41815028051a80040100c2c90b00d56490341d02942803489505d0401c40811804900b1416818030012005000342e04080c5885c115403c11544115452040c0a02d201710700e910310079640c56000d01c001d00304180030300c0416201c1a00501d42036598148134805c66a00d20000740340f0144001084440740316800b000c80d2070182c6480c000f10342c1ca00c03502c010710340d145c442d070f460118500341d14400035030488408060694030380380180c0c1482695000c0090824480d412140700500d0240a074200103403d11020782940c0a054840340141100e14080c1c005441003240440d11000b9484168005805000380c1d00b0103071308010010303a07a4000a403603404017500400b000000d89040d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 305275827 1250 305274577 305274611
    0x5011106040b01172a0306090a0201051818010f1d09060f07120c080a0e010b0d0b0606070c120b070206090604120905030604030c06110403030813080403021809120418 73
    0x140040c1171821070400201d032a401d4402c0702480f0140c6201e40126030208052400010f1084040381e03042c0c40b40ca04012499880c1005203500100b401c0c0c10520601100f034031083c180e140385000e440c3ca6020701100500f0003d00e06c2c0c4159001c0ca000c4000c900c51001e1080d44480010807640c008071041c3c40207103554410804a030b40300c001c0c9168035400d504056940308016002821036100f03000c2001c0402c01c54001c90202d9003a5840812420f0b0032048e009900400f00e45100c0800b0b5020740b0241116190010070794506044500b43d50004070607466085c1707541e080242024003690008142d2000340301d036003000710b0307421303160322010b800203010901040703c40080d5405805800c00a00300101620f003280340030b06000e448000203c8080390261724182c1c0d0381e10700c040310710700740da06584c0c00d80e988940e607540700010540d09140e104030603122908140000001641d4000091118403810b01c17801686082c4014042e150038450270f00700d1000b035001e10041c407038280d203404a00781000c00402d01180c02c0500c0100960 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 305277077 1250 305275827 305275843
    0x3080403020d050c120d02280e10050a0c080c0709020304140105250e1f0206070f0e011101060905041b080a0803070804030e0604290c030708030403030204180605011106040b0117 78
    0x16623400c504c48240d04032600110700b5a40c00f440b80c61f10300d9440401d10420910f042d0380300f41040462001e10220440f00d01c50a042c5200030b1107502442d24000304542214540202a446030300388030b400004110400c445903040140030204000203003c1d500706000c50708120f18242c45a0541c3c002000d1a46440138403030000700c8014103000d401c2200307600304540e0f07540c5c1c45000d898210000d0f10900c00458607039882a0880c2c11400003980d606a203041e40030004444003500d0b94090352996407a030401252094452084500562081001ca814500d1020700b0181103005548017800c141c00030701d1003802055101d42284d900000c1c5240032040d035a00c0d0b14041e1500e00c50340c00501c2d00014089808250300e000c802501c1c1000b418500d0141254550f170292104c0341c414044800c082e600188080f00014007158040c5800901c603040c00f5051589070004400303020248810851000e0310b902040110b543c01114580154107000050034041ca42503d507000d2003801881481c0c01131011212032003000c0c0c1c0501c0b10b40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 305278327 1250 305277077 305277097
    0x9040f1b030c090b0109061d040e010c020618010504050601090506060c070303030f0b0405040203070303180b0d02120f06010806061e030906070f050304050703120309080703080403020d050c120d02 86
    0x810a10340781c1c2041000011035000c0c0790b140900e0700e42e22034030960040b403045c011102240d81d0b200c45244181411090350130802c0007a42c101d42c031000726622914080c029481c50300c0e21a801042e080c580740c500c1008541d01002c071440181d2418081c0000700d000422201c0c1910100c2c5030200381074650001007581403161503904460382c0905c060200806d07a0582000b4102c10640e45c003400010404010041110030a650007541680704c1c1008200190140315000c020046000b1081040340da56103d988469000c84030b40e132a055400038841c50342c440c4201c5002e0701700d0100a0a15014600b00001034070121015004510624010510b0b040762202e810613143c04144104038a82c4a05101007101da403140c00382c4502d0f002c01c2d686560100c900b4800c40640b80b2a541240c02040b1007451515824101e0000c580b401c3c00b01a11100d0850100302040700030403d50348607680f440030900e01810002d04040b000c10782401044001c011030300e91404005214202d000091040c6540c2e034502d204094020320587c2403c0d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 305279577 1250 305278327 305278373
    0x60f03150b1206040b040c020c15090a03150c080c1b071d0108010b03030a1403040303150303050c01150501050405010e06040f080303160f090e100e09011e060509040f 73
    0x40800a03041d060414024801602c0a018081080701044182c1d03441e15070210044e803091414050320720b002a1060300006001c10343c6440c110bc0d01c1c0224041104907002616004400d07103841040ca0b0191181543d00e002034500154241010082c00b1490302c80d80c0c0e60f407a503940108108500003c4180980300c02043c002895500c800c0803100c0c0314000b60401d209145207940303080c8003480a402d001c0b0886001403140c0e60b80010098201301029043c1c0c00203030081e003c06a941048042c071f07000a40ea60300195000351030f0183c40c0e107041c41c0240d0944605203040040f00c60001e1040090380d800c030080c0c07025120309003003581003041008007092450040380c0c04030320ba0080c00000010b99040200046014407010b80ca001400001c1c40d100380c03030b613281c02031a210014014000400406413600e403910b800c01681801446807503500c648140c1101c4042e9421212650355280181a00c00b04006582441c9a1480284151850310780003c14000d4012320150a1103101100d00c0200038a41404010355403901c600b03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 305280827 1250 305279577 305279587
    0x1021213031205090a031d100c110301021206090615092101022221170d1b09050306010f030308131506030201030f0219050d0906051f0f060f03150b 65
    0x5c3e50f0f420303011001e401085548034900221a01800303070808441024080c104d00044112003228081c010701402d50b2103007101c10b02e480f10340d07400b03000404400c0c240301d07000503090901400304045014060022803280002e003031148010300300172065514265044034040101019000004d080154016252605e940b0024020454068041c2d1203001220181c131094034054443d022000d040000c07107803031101c9501c2c00c00840c000540b20013500c40c00d02d1800c000d070b0342840320301d0504806441c000f02425010300510710030311280961100c0b064004190840080030329500d80807040d004185a40005401c0000740030004280404034114030840702d600008000b0052241b8440300e001b031096000880c000707402d194640d00302c0400d40c002c1e81ca038242542003100146804d40307410789030b60380150401204281c9071a030240c08a0110f11039103108a00760440d60280c2002001e0011460300650015841340d818120240105075100010035089600c03420002400400ca240d0b0407240c0042d684450b06100300051 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 305282077 1250 305280827 305280841
    0xf0c030c040909120f0f0206010b180409030c020415051305060d0804030602040f05100219020a17060a05011a04032607060c09091a0d1a01120b070201021213031205 72
    0x4c0601041e003a03959040b200c4101213401c940b07104801c041c840040c0e10210041c040b4100030801060300030071400e181a9480c400320046815900c21520940201d60616007050542c2002d0084441c656101e002c03002c10030342000c000032454075064102d400807558460001d04c0c191507001d20041c04a40210071641c0b56035491170050003039801405158804550f903840041d0b1410140c01255084015801500e408003110403c0c03000c1048186082e41d01003003580001660800070f01040f113000340303280e0143c040740c07600007031001c103490060348904034001d041c0f44417001c114405000e407801d1343e80c001910380d0200000c0c2001501c80c064000d2000c1c1042002480900300142c9910541207844580c4400030300e01e07521407810302150100b44120b91041c82d00f40001a5034940024180d404521030101d07001e0039140303a02072030b035450400d81084007180d100c0d02c12602070146040100340d000441e48000e5242045600e0f0003c08164050a01d8480f11200300c801c40130540200c040c41c003081d509000401c0180b900c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 305283327 1250 305282077 305282093
    0x3050a0f060f1b030f11040f1706042102030c010c09140f060a030b01050c0307080c120301050d0b040f05060a06181401060c050304081914060f0c030c040909 69
    0x84048500a00d0052201c0c20340a0a001d01440010070502241d80300581440a8015205e020b440c0400242d46511440d00c0000610161005d4032007a0800c82d103041c01c4c000480760004003161190100e0303112100b0040002d1080c4104103052040040c415882621107100703a00d1030091005845c0315500b480106412513506c8481d10084a6075504400c215640320414000c01200c24809590010410000b080e0094000d420003102c2d4501858441c0c54403241c0b0342003600b10b401000048030742c07400008413805030410400880c0c140340d09000e030051540d4946000100300d904030a070000c1c074080ca03003000a418000c4082030032a4268011040c0c03a600e00d0112a940c000300000d02403446903a000448140028143d8894031160180700c0041d0349d01c03a400c0101c141e403000f6a01c0700c212954441000003240000003071040400c02c62100c40f00c1c03c050135007490015442d196070064456aa80a4410403950007000118150004e0100b02d0450362a1115a403800340340c0b0407504503243c00ba09000e244010031082c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 305284577 1250 305283327 305283353
    0x1006140d14072c0915100302060c07060e0102120d05041502190801152307020a03111e090601140405060a050d051003020d031103071e170309070e06030703050a 70
    0xf44070751014060311010300711190000e441e2488180d0143c0c90442c5140070800e1880e40212400c0b4241e00225034941c00603005500c51805000950090071007040201c0d045800c0210402003400a814a03050340f078030505d207601405461b418010f86850104050140347d02161050072903105040d56140c80c5503101091416100c444500051004d01c00000d9041d108000f4002448150b643c045640c80140ca0140030072000c00100c1d4201c8500304900e000580d100e01c1c40c0c9004520422084603068842002c124203140e0b4007240d14140c1c0620348200c41299035002d11690b104409007041d0049500b0781ca43e0000c4c40c01280c00c10354204200040c8880020382003005400e088086a40512559441710362182010141c0e01c0003d401c8000031380007100003800380b044c01c60803804074022681403007031a0703c9070035400c80e524207005040d07110001c0d00c0302802107610b00c8403005c045803a481071035405c220174107540d07a1489200c1c2c0c070700810040020802c40d960600c031981c021500201142c80c040c401d414035404100c68 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 305285827 1250 305284577 305284619
    0x110406050a020f0622080405030d1d030712060e010b1002010218060702090606031f060c0b0a060602030904020d1112100f0b030a090f050615031006140d1407 69
    0x21101c141c03101d140000395071403044060040b42401c0006801c44199441700c40c80c801c541c0454284404902c5427000c020800040086503923144042d0b2074480072a0b2000f90f028140d5010f500440b40c04c0c080b02010030345100d20344e603215000007078a488000d4483e004011071400c40b135015231810301401000d541500681002c13218a10400b101d591040200070300740c03284460080d006810040090718500d0618091948a40c4e50341c3e040c4001c0c0903280021205682039081040454400011401031000b400605030b44051074040400c11141840c00207582c900468845a00c5150005103044801510350045051100c07500780c055111015046002c90826085a880503100180351000402c0550400c00d00222074814080c5842d507152010000050701c420041511656540010000003800c2000141d1203410300544034131040340284201828951641ca0710311483e030801c1030a10807403401101c44100c0300f800301c410217044403540c0b821850440b121203031580da602881100180c07030103094240c07049902c5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 305287077 1250 305285827 305285833
    0x60606020d0315090207080d050a060905010506310f09050604110a0504060f030b03100e1c02070e0601030608150103020f0109080a14030d0f140a060e0c0d110406050a02 74
    0x14550a080301100d10400305901c8640a000e420010b0308000c1e07000f1b00c503050103108000d01d040b8056100506551050700c640311100da0b170300b10070490085103101d0345001d080c04540715072600c2054502c4526140040404240da48000300c54120011844200340c4000c2400c404481c0340c4c0340e640c0c4402c81c01400b040310390f58041d07814545000e0b05002c08408481121041d078039014101403c0290854001121541280034036683c0c0c48450046e6508118008401d200c43c00082540c0000740c2d4800e051010840300340c3c41140f014048154420740120300c1c1c07000c3c3c0d442059002001c0d40c85d040100c02900450b4440644d40c01090301d440042d41e103072942e45058034020355001d0f034001d8a134401114041028800c0c120503420042e4080001002c0035000c1381c840400000316800c003100900c038a02129844d14405250fa542d403aa0340f510518040100d41d841032035058100847e500d01071001079010740c010000307000e000c030004401040013003540c07040c0300c0b0b0708102c0040d9485030789800000d4090b503c00301408005d0b00c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 305288327 1250 305287077 305287093
    0x11706120a260405060304030e0102101406040609150504020d18030f0215041e1104112d03040308130b15090f09071401020c06032a07050c01260406060602 68
    0x200c2c000866003200d2024004503d9aa52030303c0c11039542c0e10001030f050450140c00302001e40042d090003064082c51204500e01c1d590300b40340b403c1008880d41940b103501c001c0e040c604a98811400310400404032142980d000d40d89506030503040340100342090b0070415840000b03466509060344541610b951042a408660600b56140070201c40010122401080d11074191040701c5d075280c2044c405406503200303160b23201041503041c002a054803d03102e01c010000d800400c450904010310900000e05c1c04240d4903807002034070200c2d003100389840010320181c00e210b10301010035103601c0315414400500d43c1080008006080211030a440015440c00051180034103c0104445901e6486c45038060303040d050003821403514100c442580303190032002050640c062075039503101760344540004622031505030705025507040515010004128906600c47e00c0301e1814490840003030703000030700d003510031801b424055001803440c0c0e4044510074180785841000d441400600040088580010007580d100fa000d4034050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 305289577 1250 305288327 305288393
    0xd1d0603040c050109211101020c1f1209080f030705070605090312090105090a0b0a060b0d0506011103041d10031416120201050904020a050c0609030705100506011706120a 75
    0x280d40301ba980b2107a03403a103101d888030025995840285c8800818019581c44030300107000612000082a07924880346140707840c05c9503550b80100300b011894407001c003c10002c030780e80c0c0314814a03004240140810800000108107442e00800a80e180c9907804001400f0516001d20350783d41f280c0080d0178a4001424000206d2300c5200d0602401d4407404110300102514012902da0b200d084c240504100c500e2941c0e210081f401002c51b100501307101116404c04030b41814040300040c11035070500e0143c100d40e08180030500c00007860040301c1e040034504024103c0e058803100d40f00d003a18003081e40010301654088803c4060004c0100342c4a00f02120560703c100c2603551448682079500788080001e001500400c801910351419038080c1407080454079005080003c282c1240c0e140c1401a42ca10409900c08682107003004400c20140f0700e14204030b0414000350420794000307000303180814140c40040901d03200040ca00d4440e0848040940f000c042120b00f10000c9041408520800600405084550747d0305403c00c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 305290827 1250 305289577 305289599
    0x7060215010506160303020c03160c05011e05030402040b10030902010306140102070b070804030b04030908010c02010b0a090218040f020d0e0105150111120a0f110f0d1d0603040c050109 81
    0x403140050080c1e0b20380364809540404c10a000c1408409041d42402001c035205000c00c00341900e0041c1a507030000302e103010308003105144480d510280c1000150748080a012003000c02c202500081803e181d503ca448600c0064050808944501e4000020200107600943d141d0000160035000b038800b0003440341c4815001e14401c1c00503064a002d40d01001040007000b035040001c08240e4001e04940d4105926a13032606c3e894038058800740c0c00107111034030500000100780f007113140072101c9000821072803514002081582c01180300b0f40400d140d0200d440080300103011344040100100a10403c04501d0b08a1907000a4000c1c50100a50303d00d403000d580b200178014485d0341d0040c48051000500704045000441d80c030041030f900303180d19015407010f04003180340d468003030041d001044d101d07210b034051400b400034803110b043c40021400d82e005d944445500f900100e48074405084074500046106000310340345201c0500c1444658026200000308410700a105080d041943d00036625001051740d10111038035 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 305292077 1250 305290827 305290829
    0x51903080a0c0317010b030601020f060105150c010f0c050a030c0e0d0f021504080d110d0f050c0312130209060d0809040f0f0f050621060408090307080f0706021501 72
    0xc400ca080094140507405603030b82c40c0003a8468680040c01d1460038441036210036081e40150080100802440ba87e50b070107104a03c8000d003810000d000540c94000042c1c2d10a2462081c2510300c1400509000c019400b074204400f00c501e000001e100040291780d0041095100b03540c12000240b43c400002074a40c03041c420400035901c010103901d0700001640703440342414404002240d002d20340320001e00c80d800b003200141001b0300300c0350041c1c82c21002144000d40f00d40910101030150b034100f501d5081110350400b400c2d140c02c0d101450050386580c0e692100c24910302c1804510294941085d0030005d40405e6007006102e058400da0b402113107503c58170240310310701030713002c00c0241b1014040c07090b0300c840c3c10300340e20584060001c4400858400036840c0460300b110400c0707014003030240e00c4900b00002c90030100158550810544842010551260720a64544801410040c0024000101318005640802521019107102015900c0c10b401200180d580d5641911a1101602454019114180303008004034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 305293327 1250 305292077 305292083
    0x20f0c060a090e0c16050307020103060902191808070311270112020d060c050c010c0e01120f2301030507051905040203133e0303043309051903 63
    0x40b003031a00304031083d00700d2040203000552038281800a01c4000c4140f420380c906441c0100c010319030f1521180001800d9074070940050292034010002480b076000c0c90745044c091501d051400e000c0b030a00031111001c0142656001401c54411001c010060007203c2907002e00c0d0310720884511104428003a000045001c4005003281048142d0b00108031969150144440701d500c02030090404107003998820044580031103005000513000710b01100391000074400c0580a41c001d09103a00d40f801c0e039038002400c4078001c010707009510342ca03120409001a41d80e0401030414000c0c8102c5860b0841c00010380c550070b0f03000d20007035038a4402c01100103000d050074160642001242c141880c603140c1480c0c2407002a60010700110b0b40e2060082420700440c0f4101c0c5440c00b04120908000e4980740c0500c0c0301301e285031403071860802d41c3e004141d1050440e80c00008070340071908007403110307850b24501446501d00300c071100090745047e0b46000943d8282941c841680d50954100f01c2d0482903000c00081d05002d440d540e40802 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 305294577 1250 305293327 305293337
    0x3060b03091f052e0e0708010815010b03070c0807140a02030d0c080304021002190302070617101a07050303071707020321090c270c03091009170703020f0c060a 70
    0x6248a1070b40f0004440c1392107460404040030b07652240804a404001c0f02c9140001e001100180525170041c007034260003c4002180ca15a5414a50040380a2001400d0340302405a1a007082d030820010400340c1c0e08058111855098500941082e940c40d628840306c00c80c481e00440da01c11650f5800340200e1204150030465250943d0b40d10307802d0050410768108420f041d0710502c601c100340b820700f4031040030ba114403aa01806a0a2030001d000c2d07d01182041ca100700e01200c0b070200280410816041000ca4002c86d4142044070906030303194815100740c9401919030300000080140094000c1c40c2d405003051401c00e50352890751000380498076170040d18017102c600041c00d20407426142c880e00704141c2006421080e00c1d612642a000a0380c0c0541501e10854000040340034541a18038040350154030820400005141d450030582964542403444000d02d13815a07983d110704140305010404003214512582291303507660310f5080195441410100104061081c60a06882030602e441555814036003030f110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 305295827 1250 305294577 305294611
    0x140909060a02070807060e0a05100605010507060c2105010e0106031b120e03041707050604180c1812050f010b011209050c040501171605090a02030703060b03091f05 72
    0xc15406948440020f85134284d0a02a61002c10f056200d4220b4142c10400140061501454024104a110801c052220385041d108019590308401250a01c039030050f0001a1040984d1050b2200d8100b10110500c9040401e14012503580c2c5901260690310590300d03408250381d9a09040301600d0105032800300410050415001e41805090381442d8985040d402041a11540d1500c41c6141c000b64070002c0d028884005402c1d6607603081c08100003404c1c060f0303041403800703041c010304200c600039044c6000710041c0d641c00c02c0084d4074071580f4036201c075034005031100a4003070345c800c83c0c0e40e103031111618243c60b54080c1440705200d01c041480360043d10201038468180c402c00f04010320000b800c03264400e0352940140210f99840340d50790300c5070b14040c16112103000c000c840c4444030301d49400752504100110462010061180795100b0790b0450f4409100300300035039a07903100c030801c40251049501070040e148002c41803011580300440c02403541c0d014102119008081c207040300d4103590050b24440601e41e03451603 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 305297077 1250 305295827 305295841
    0x141603062a03091703090309040e070f15050d0609090204050603071410021213030c1a04091d1c1202120a051308120412020a050d0f02070e0a020414090906 68
    0xc104003184c024000c003106440c07507824040540e80101d6074050345410001d00c8030442d251a11850350100f01c00701c010031007181405400c0c2c0308a6824003d801c00e40350481082c01c0075603c9401111205c2c0400e071028044c8613600e07001200038080c03802040388180e003000c00054503420002a00c004507580340820310850302c41b00c000d000d5034444104e078801c114011800300c6420000d2400c0141a005a07000e000406246182084600e4180c1c46d0820300d20081d43c0c080500d02616110140e4051380c00840e400520086041183d404110022907003030894003070b80e081c0c180010009050454100e4580c2c8801c1c1c022060310255074120301c40c116070000c000003208013003242c01e135a0b54010395000030b02400541085c6903c1c9c650001503004110711810750902c410401c01000a81908081e503251140020401400c40c3d9071981c0d04d540782814554100400c00c00d4019906200300603804c010900c2c10300c0341c0010b003441c1c80040041d520070b000c0e04203640c1c1243c405030807a082c2042c0061003041c4800290007a41c0300c4803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 305298327 1250 305297077 305297081
    0x2090c0a0c0311030d15170a1104020d0b1f0305100302030703060504060603020d061b0e0904120504090608010209040b030c011b08091e04050f1e04141603062a03 71
    0x31030041c03d01c0c8014030000ca038544044c4030349903120507004040d881d500d1030841fa015a0f0500c6100102054010706c5020700060a00c10010390402c034112400740c1c8444010034060300802d030300410326500030070000c0c41c40c1d5040a19503d07001e10131810340d030610965943d440e8103800b800007440000d41561004c00c04001183d00b40c0d209981040c817072100450f001e41c1d00d0700042c080c00d11002041c2e071065030351a075214085080102d51030090110342065140c400d000c4002401903540144080d10195581608007009482201110044e0031a031600b006140d0b1a0900d4034002c1d000fa0240c90702491404521030014680024644080b403816954020561a0711b08034210203002800100ca02050521244e040740c1d60b40400806c00440c0c1031200d20a240c007000410050fa40c018242c01545440308003404284289105d02c164805408800c1c030009446900c4c0916a40e4007090059400340100000701107510100d190b10000c80307000300000e10208840410703500200b011030781c442100001c81810300c5045070080d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 305299577 1250 305298327 305298347
    0x60207171c061404051902130e070c0309030807030c020301150302040b09010312140c1b1801050306011518030b090d0206070905040f020d05040308071202030c0a0302070f051902090c0a0c03 83
    0x20030190403443c403151b40c024246e80165604070600c5014100522003102640b00aa0f4000d070b075458524142d100e40d8402410b0200c590001904c0c0c01310005041c420b15005440074080340e45c1c040c000b000111064440396641c0d0a180c00100c0c410360400c05002101d240520b8a18182ea4000c00c24120290001c0004d5070b0362484a81c5030000c442040c40301c4060346805000ca2804007084429a21076440f00c4030400135601d2a004803406225520310044c40b05403030000341c2505440e00201203002c6070b00007680607260307101c001003000c02600b1540e5012080003114443c40c0e0081d050001120601c6600703c0040c0c0e100c0908942031400904407510812251402d5003090f000d0111a14005103008030240000050304c000312002d40c04502c000c01030290503a40113800c0c00345003c1000b8212b0940c01c3c07800d01c103030640c8101c610354003c06401240c0760b0180520a01e4000002d5404011a20540a106041030243e000c542c0f050b44650403d10000d15007401c10780840e0500f00050740c03000e910070001e540596501c0b0300c07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 305300827 1250 305299577 305299591
    0x12091509032b170712050702010f05180609061302013618020a05040302040f0b2211040806040308180708030414060c0712060207171c06140405 63
    0xe07144107190791042034030264482e0070030100400e12201482005407400d44603900c0314245070240d0b4100088158040b01c21040c4c100c4050000c00c0c983c4035100101d001d4800740166010300c603d000240041c005404c0c00b55050350100e1000d4400070754070b8081060300c842d400c0310041d12041744c143d000e0b40150705c0750700401c3d8240b09141c1030704540710701081c11030802d0034200c82010300c90014010512510b8260b1000f41d2403901c014000394680070241000810178010340c40028007503901c1c4c1c9000d036030000054122940401c00617100c0b404010315500c01561480640c122950b40d546041d140d14101c02150044a041d207000c0c0c00180900c0d2955503003101e8140c0010702030084035520300c42e032504003241400300300010710b9140021602ca508103249107450301040b42c0e580e84121420400f041031a200070518000715040c1a200c490020860b041c00d40103440b071343c40f000380990005c03c01094510f0030140a071900d4860761400103140d118200011701101c165000c0c0c480c81d00d442000c1600a4602504040c0c1c0c482c80c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 305302077 1250 305300827 305300833
    0x1090f02040312050a02010b030607140309010e01020708040311060f07230706030c110a030e1306050301090b0a0e15060607061503080408060a020316031d070e06031209150903 77
    0x2d42e81c1c4409112403901c200c00b600042c00010140201942401024a0000202d01500a500b8943c00203840d25940081101c442040400042c59004007076000d1280c4103018070080d0340d02c0401d45850041540070340800c0301d14010007000c41f045801e048082c0c801480c14400c50500e40060b944500d0140504118143c1c820414212580c40410050006100804407624040341851254201a081c0c4050034a4081c50b030307100307105000c0400d038000c1d030010000c01d0a6803200000034004152101a040c00d800542c0c042d800c103444101085415182c0d90311440b01d05404001e041400c4003516121984440c8900d540ca040e68003182003450804005c215080c82018006507480c000c0d80e0758412070186070301c103840300b45001c50100200d0006001e0940d011100c0802149107240c881c4140c640070402400d02c40406680700c0d81c0c1111005262805158595000d00729441c241d03641c4a5115400803c540e03090003800b0380340d4406154004c0809640006000a280c4100107031030508210143d0080600107501d44 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 305303327 1250 305302077 305302079
    0xc1104090f1b05011b03030c090e01060905011d0a0b090604030506040803010e34030905100c11070b0418090b0c0703030506011d13020408030406020307050c0d020901090f0204 77
    0x164044800105162003400c042e5040707a075007102d01290001561240d1305110300c5408841800100c068501030b220b0381030400003911101c3c140129500c00ba00d400c0320b4000c02ca154004101590403811860448400f42d031101802000200c6034804410b480322541d80011529409001026400c006802c3e8402d01515490605580303482c1c161800c43d060710141d6007120000010701001c2a060f4078984e000300c8401030200f01d00c80300204609051003040361b12001401c0c502d030141d200d510075088001c0940c0c004040341c10f64040700510400038401d9003c2075021928081011224000102c0c64900700e6407600e11a5003002c3c5090307049102008100f00c1c11031060303610080b400000d054001600e01a81600080b25103d80c420318014080b200c0c05001c00d41030100050218183c000e00c0910701d40f10b80c805035203d041c40404588a00013a00483e002104c5a0102040100d01240e000024014041c00380303040310303001603800044c0a1005180341000c1d400000010040c0302c500f001e071300205d18852600300c1c014902 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 305304577 1250 305303327 305303333
    0xe1905210309030a110f01050f2b02030114090603010e030a1d04090b010e0903031b0d0b09090d0305011d070c03050906160218070516030c0b010f0e160c110409 70
    0x1c0b0020150440f070681030740015010a0074005001c8031380c100203080184c0b40105c404509c84a0b4000d91040d4070842001204900b902c0d0002e48000600c43c081c00c1055449584500c0400120540e0b20780040c01000b410b00050104d01e014001d0030300e40b114400c0030b50310f400d0b100f00382191200b13903940e000c29030b000c2e00820101c182c0d2034a1245054032400780c18103c0103541044481941200e0252104600303034408d01c14484095420701c0500404240c1c083c40d595698516050200030f00030216440b075206c4485810440ca0381030108000741072200c1580d04019503a01c0e07600341c913007400444890400560104000441d458000c0742c552690034080d0a000e4240300340c10340050201d511198a89100c465007400400460414070314060800d0a40105a4014906a9401003070341c080d24101c015000036001d0b404040c5402881104100c40c0c100c440c119296840d4241008003142c54070504024010380d0380040c0115051840c204040011980d4a0040424607204e15410500710707144554030640e079020398400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 305305827 1250 305304577 305304583
    0xf1302010903080f0a0f020304060203040b03040f0f080d0e0a050c06130801061401030b010c0f030e060c060f0f130f030804240e0601060c02060f03090109120e190521030903 76
    0x300b100d52207016991806401c00038440c202524601e407e550003444103000c0c4d6a00807040d50107980400c12030710740340e944a082101810034804400b410803d401d849000912041c00c000700180f190040003404038180d1070b509035542d1a0b080c0720144c1036410241c020003ea10b0440f0042c021000004666a016a120f24000e82100c0c15540401c40044500c00ca200e40380d40c0500690002e030100342007401401d030858a0f01201854900802804c10001c0210103136a5500c010503224214503900071a41d05140801400442007800e4400e0014103041000040c4040c3c0c5000000410319440b03e0146440710f0340d55030503601850b0240c01204e103450341107132654202e1004984100010304580c0007081c07012141c03500c5401c116040c0c10102c20000f890b4054805170301c4460407922902510241c035075982c4e5aa84529004000e0484020300003c40c10300d80406140e0711403141d400003075003120604c1d410005c0300388494038650b69204030b40d00721040d484c405041030b00c00c1904064034140401500d04d060315083c0040c0c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 305307077 1250 305305827 305305837
    0x22806020604020102060604091212021b060103060608070f090203060102030d0515181005120a08161104060302010c0308060409050d020d03110c1c0e060403081804050f130201090308 80
    0x10041e40034408100956a0400029421042c1030314201310100c0c040d100c1c01040d1101e04814000e0040802601e401100c0e07550403120014a8441343c0580143c03825940c2d40c5500b030a22090342c01c40c3c00c0001c00b090410010a58208440c9200252218186032030345050294000400d01415800b040c82141c0010409010366841403200c41100000a4540c008122001700c0c10700e890f42404c1c1002e42000310100601c548207003580c9081780c2c001114180c0c84038917490451268030046c01d02c02c012400e40e030b080c2c01940403869000e02c1000c202ca500c4103004244003c0f1500da20001e4001000d08200c00b000c0b81c0281d00301074000d0780140c00483c1281064070713250b15100c02c1c20304140040c3d21900091590320b6240c890140f1410b10f90184034500100111101d603a9900141b4541681c2e04c80d83c1d04080300f80c02210038900c0040040c4c82607882d5580ca050140241d0024000305400c08500c074511421841c040c4a018812100d00003010039980361081082e11030305203410224144403040501001261160300540 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 305308327 1250 305307077 305307089
    0xf050f0306131103010c030b120d09061b0c0f06110a1e0f050d0e01020c01030504050a02012105070224070c0b06010e06030a050103052103150a15030603021005070c030228 75
    0x302300c405150040c403032402d50000450b8107a801c10580c03c8101f03035000d460a01290503502d0442991030407400001c2020012810091280352149400520241600040f400300c1e0b080e40c86120f640b40d00d1030755007501d03170219140003060108002c43c00003081d003100c440411120f000c0c00d101c2c1242d0300256034040ca8a041d486402d000301d605044c12419a607410820108844420b00e000d101ea41481d50f5001e40e00d00582c1e400906225000300c0c8804034402800c0b50b1090b14030f520509208a091002020f0b48a01c41402840354940701c0903808181035000b1150360740542503a0755048903802440d1180c9030307040c00c003802690400074038804465541d61030354055070250640200006043d413451501902c0d000342011011510001c40e41d0050511388440250382d40851160580141c7c818103c2c00100512116000302130300510400c183c0754000d906074070000c1900e1007580c0d01c018a6203040c0003074a4a0103200310090000d641b040082c001403c04034040790306244403d01c5a5400f00d0801803c4040c1401d0360081 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 305309577 1250 305308327 305308331
    0x40e100b1c06050604060e040c051603050423030d0c0c0b0a1707021c03090f0c03150b01020c0a06030b06280e040c0905210f01060f050f0306131103010c03 68
    0xc00e0015950320942d03000b00421607a4520b0a0324080d805040c0b0710f0500400e42c443d95403210307541c0c8464010380c110381d2032020407001c160610840e0b240c00340243d040303402402c2c0491104040066030b00517480304400d2800d0010b0017040c004070454411101c14408000854640d084480002101d001110140010800545500700c10740e604e81c801ca940341100a02a1007158449048030050100049031002421414038002c1a40714107030070000040016224000c01345041c2c44000010b011403030001400216240c4814800c240800c001241d0754200300d00712552024560004110321406540310b1902124040d06050401c050140720b2800e4416804400c21000c036413214101815a0102d010380840c1400c4030100300000110038018801c240500440e130140c1c90280c1c10000c1ca001c1090b040110301070080442c0d241d0061703000c400d4040d1416100714001b8905188010800e8a080101c1c80c0ca843c20103002030134a40e4400301e001c1d02291a06c0000d4607907203e40000222551828002c4141890302a180 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 305310827 1250 305309577 305309617
    0x120f0d09090b0607030813110a0e040302010c020f0304170705040203040c050a090603080301050919050c040609050d0f0605101d1b1e0a0201020d020d0606180803040e100b 75
    0x1e04400e07904611001403042d841080b1810019401a4425802200c0390f1450342d01b0f11140d28001450306110010b880e0b01c04912400041c0c007000001800d8480e5200360b00030b004000e0059420b0341d0754401c40b04045455001400244072108900004043d408480c0d411034030400e0b540c001140803680250b07070a50360001e10300024800303818036851410050144c881c04100f0b613842d503100c6240c03a00040c090188111000b501080107804800d034441684101040100207e04001d410200f2540c41849084045035040000003841c0c42e02c0403041c059140c111160410700d442c141d99050091000500503144503500c0c0300081003205000700b058424140c00e040d41e21450500303100f498589030040c100b401c201c039800c007c080341e1460b80d4150740c01c00c9840417541c0342c0c49031401e242c103902900540345843e0b80d051020400300c4801c0300301d41040c003c40ea0b0030f4a40f8071020402c1c2c12007a8a4400342d000d121050303070041008000944100c01019840b04600300c0045506468001101c41a071160000c441c80200c41e1034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 305312077 1250 305310827 305310839
    0x307091728060c02070803190905060307090806060103060819020103090507090c020c120312060f180604050106050703230409050a1401270f090506010f0e06030601050f120f0d09 78
    0x104030162151240005d29060b4a440300c615668403600700c6060304548403190a14003207014034400c80161400403c040c1e103904c0d000c00300038121180c900c10000948110408504194041d104400540d101071002e000b96100c403090b9942081d41f4014200d040580e102000408038605220b031502420381c0d204040340f0701d40d40000081c82c1402004250380305880300700000e03280301800022a0542058a05c418981d40c0e5150005014410090341140c0c00a940b050041202d15003004810700c43d40013118100401e980b00d0004580600603403a00402084080048804000c6090989038000c000413040f00d182c503485411100659000307950041310a03445241d2a24017242d0384031494050413520300016000050512100745880503582c00805030340c0d494401004e15034040d005900c0103034020341102c01c2940c3d80e59451781141d1309442003801100003880491050314000c100b09049030700051032071490350b1400082003141400340800100911501c00100c04501003400500c4c1d0540881e03e03180c2040d032601c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 305313327 1250 305312077 305312081
    0x140d022101140907120605060f0c06010b040b12100801020d02071e03140c0321190513080d020d0e010605240d1e0609021e030709172806 60
    0x281140c141008210050900ca85503400400c0d803211a81c58030b17012a000721140580200700540005802040004d08441280344500c020860340045c40e080390b032280e9860100b03200030b018500039520801410080c1e101410700030703a4040d81081044e01ca100300c19580790310031422a808090080c0c846600480c04009201c903149110100502c4003011401c8a0040d40d4018000c122400c4000c603103500c0070403c484140400c0054071074a0140c081290041ca5410034900940301c4100c400c000e42421440ca102030f0303e0300710702509010b58088803805800c81415a0f58070019001400e0120f140c56090150f1184c040540c010000c40150a0000081a6040034107025034440c0d420311103a0520103514550040b80c3d243c00c110f8515030540200001c44075000702000100e91120f515041c0c28074281303e00403400c40202da0090030a8040c044d0f2076a5003d0302c400b401400c600048503c0000b0980345981000700f11059100c0018004e003000960f4410141d136003c1051100e104040c00c1503a44105c400181041014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 305314577 1250 305313327 305313329
    0x2030a0518010c0e01050c070302030307150c14070f0f0b16030e01231003020a0303092303060a0507050d020f0403120801030c17070f090b15040602030703140d022101 73
    0x1100c000c0c031500c441003d002e00010500007445040282c00603032003100076814402480910b82c0182620780c0d400440c02e000b001025180a01034846241c500c0e50640c160141010f120200b1000b41c10606082540c6c452100800c038100301650040c040261603c00281050b02c20703403181540d40010786601e040442c008044480c80805000560f1400100c4245c100348600119030f1240265480405540c0d411040d89881d81c0c6640020b4010515010200805410030509401e40b40388800500d001d124207400303458908030022001da090782090000c40d01c90142c90700919400049810000d01d0291014010301c200d81c4160001007540c440800e05104000d82602070010a003a1388c41c21a841c1d50450310b500c000242948513200e82c012041820441052050102c01c00804400b1070301142941d481c50110080c10203500c40034440c03116010b45c084121120000d80d804d80d64240e00450910100c7d40c0c0555001c0c0f0300b50814a84c0c03101c01e0010300d403030300300a000030004418071145410f07207001544034400c4150b0701 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 305315827 1250 305314577 305314621
    0x20706060509130209040c05181e04021e030a0c0f0602150c250203071d0601020109081b010605060a0f120606050d0b0f030a030207061107050a030f05030d02030a05 72
    0x203990706001c0d44944025030003803000e404485c0d005180d1071784d11300510084040c2c1c8c80103402c09a0180e4039103446e042d041c00d440c8078001c1c1120401e00300d201040041c584440072079000790300c8809070090000e2150400e0301c604280c28082c0490b80c8040355501c840300094a180d116544030600e80c0814050a54148132001503d166511340718618101103212000e94040d82910202480103030030b0030940c1c03820f0b00e8514a00030760050150740003103450324904a50300700a207500800c8507203550046002544148109620250440415400c1098102c040441821000b0444040307640b00c1e1000f080ca9541d850003401894429154241039817622840544100b0140210004161901c003003006003542120450302e03013801d80702d40010b026841030300194095110384d000607054030900c020102095000510f11003940e44c06d455110312040d0f11052141c0d81c1144d4000ea540011000358204006038541656083c402c1c45030081c2d80c00c080e0301440c2541241c01c1100c2e01560035071580103200714901c0d42c0800b120f2110f0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 305317077 1250 305315827 305315839
    0xf020408070504020906070b04080910050711091f1701051608010506250b040201120204050312161205070204060906080d080a1107050307020405010f03031b081b010207060605 77
    0xc034200d45203031280c1d201d10550f4012074001070032403072907a610002c48940d030354031036021070782420507042941403070300184035080c01207180340c091102090158069a0030946c0c00540d0100f100c6540c020301003401d2000c2c0405501035049015149034104105c01c90000c0c0007941454040190041281400c1d1703030014141380c155800540c07514540036800310469040d19070541d00c1ca5640c0318041c166190b84013100c002e00c45520b034450f10600400021442c090b000314003d999440c01900c6030003161089111f41d12076954183d000803c0d1160682d00031001d40030514114080740e03a000e080340c83d0484074690440c242400a900007400d241185010b2142c1c0c800340215200070000c0313a00f425078065030365000d190010140000f40c000511803d5075904a0b1010784406440b09403600e00f2403070040c0d90703508100c004a03c0f8038100000800c0c82c1c0c3c00c07090b140d4100c0c0e80651301c4103000d032010195100c1c2c400c1e0701d000507030f491078041000760100a12001400780810300c2c0b0000503038445690800004550300354008522480d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 305318327 1250 305317077 305317079
    0x30507050106060509090103110d1707060524120c031c17010312051b160303120203041e0f0605010b03060123042c040303090b0a050601140318070e0a0f0204 69
    0x1c6c07034020707555040d29408a0704d6100d800c03045000464440c0c064000405480c006148020001125400392003260701c5043e06024684409144500c0d250b02c3d00b55901664a29a40d2000c0794545a000c03040a0b9171034a094a903411580300c0400c1c2003032565100030490f480d040344407480c46503010042d41c1c6102d42c000f42440d259411961980320b540000c1450904020010802000100d4101401d003491242e003011985281d07200848001c80c1c00f141e2000b900440e14640c1d03002d13080d00b468001c42e0b20482e40b095951128610000c1c50144070700d214002640c11100c0c00030703242c2c0015a1032103028081c0180d540402c0d12813804030001424510b155a0700c12003003422541a81428110405550580c0d0f60b02c108904104000d021010710030807000c0032280d91420040c2400140b5070580c0c4064030b007038040ca0950946139220075603035099841c00e0f00c06d5400031f0403102084a202007800c000d503030420035805101030341418582c1c03a5403820204d078101a0050316840c00f40502d4602a00c038030f40e08095003150942c142 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 305319577 1250 305318327 305318329
    0xf06031103042010031a0105040b07020d03171317070f0809030f19030f02060c031f050306040308070306051009052b0606090606092d050d030507050106060509 70
    0x50001070801042c1e0000020a50000f14076400fa0003207210300a40410001c403e000402006060034568503a00441d114604156070b5200f1000c89042d1804060701503e4894543e0034004401d038402401e804000c01d403c0b0071203001411080c090f01500302102a0505180141409003480c030207544031030038042c8104003000004030810340c42c44445412020b101e4a031091503020a040a40b01c0c0701d03c200d14021000d03a20031b131000c07001c210010b0500a0b5152070343d8400d4000242d03661001a0703425514000c00348005203556030313250118040b808003036100304605c96440b0b010038503100c0250f03011400305210404100c152a817501c0b4080c028401140e0400e40301d82445000b0b05280ba1a010715800341001c441008441d802d4000d070040b05512050b0a50000c041034180440101800d00a0f0321140e03040010010303d01b0303c942c00350000e40d0058000cc402000300e42d02420b0115001759882c107020044080000b0300c5a0301e044484480c40d0094440565400c11381c944a421034003d0f030403000038058240300480361 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 305320827 1250 305319577 305319611
    0x20c0f01020421051911030109050a0b0606131401140703080609090105060109170114070f1805090114010309020a0f090b0901060e2e0507030305180309040209040b0909070f0603 78
    0x41000d0251464517540d564240080c0032600030055a42641c20200d08108010740041d818440302d0041d0000d0310360fa2114001c2049610070b46003103179140d0740180814080c85e40451170594450700b050400e040c42307230a11908144d043c0c00060040d40450050710401c80f060608111007075110050f2002005689400800684010381c5401041414034442644a0b0000b0095004509010104a111026213480c0000800d1907404114080004403c225045419420100c18009440000701078216603030070214003030a002c403040321040c10961a284940f025841d0300703881001034555525503520b8070b42025600c0041d20409550b542c06800141300401c9a00c1d4804003041c04200c5c1100c0080d126441c8200b0b110710038242c18000c145406071140400405a004001020b96512030f031400e0001340e0325910386240c42c42405001040a8104200e0100c01d49031603030040101c010002d1001a00801620225403011001c0b552410070703502208052200c0030030548284020a040e1406105c1c01141d11881c1d01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 305322077 1250 305320827 305320843
    0x20706020709020a031503080405100903050c060a0c0b0106030b1509180903041a0921060a020f0d0633120b0a050904051005090a030207031401020c0f0102042105 71
    0x3841030f80c040303009440f141c460b401003c0d81a1003220112450754403030801045690040c400c484c0714420700c10b4105121409107030400c00300c80c0c000c8043c0101c4409441403003429400950300d101040700804081000038105915940a40541ea40c00121940302805020703c4100c48404800340b90b0003440042c20a0303503007011020010a91081d6404161a1240d42c0c80c40c41c080c58115882c030405480103881901c400c0d80280100700d208a40ba161120008003001c0c6100d0b50b883c1c030000e82500040d00080c0700507401d4000701606905120154030b8280002d0420044030341c0c580202d0302001d103801e0407400548a82d005c0b2656a80110403903d001004031801618a1404520000c0b0030b5856039024600c640d6a420040300400e40940b24040500c0c06107811500c07885d0160300e18a0143c0b41201249091100140f5043c140d58180c0081c00c440c0d003161600b684109036282004403030b40d000c01003480150024450540303140043c50005d626035040c0700915110802482034121289003180709800411b10000b5028 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 305323327 1250 305322077 305322089
    0x8070801080708191b0e1f05100e01110d02071503060608011202030109060507080405061b070311191209080606150706091e0309050904020a051c120e01020d0207060207 74
    0x2e191103a99143c11210060080c215103802030345480001b0315202036882452052101c5941c500c07440c03500442d1900c40421900800d038104c2049030716991518080e0042d010503601c14185501c8680c801202103141c00810050b500058110900030418161180451072592281e03040c244034460501e0b174001c000740014451108441944030b04141503403000e41c80f10b503070107800c41014411885c0c295009403001c41c00b6107044441d40b044200150300301102c4110800c0240c80e0170101860702083d628100c600110420703492465009002028080c50f0001030680e00c090300c203a145a40000c125a405401d03042c05038090307244d64114a0030020740e80c3e030300250b42c071204160010540e110142c030f0415000038030900c10014041c2100f078010404051030a010050070b207100b940c580c81d000341c840040c40b6004c0c0e4190380007034102c0c040301801d00c03007460b20358000c00d051011012030013103c160325111002c103c0104003145011809814201c03c203540e0501039418030302001e00040c44000d103441002940d03034006101d90 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 305324577 1250 305323327 305323363
    0xa0b0909130f021c05030a0f020f06010e061905030604030c0b0708250203090901081609090b0103080714030d0c110307020901030809130e2404050606010804030c1208070801080708 79
    0x40c0a1241e03590780340c00544d41c011048a4840f00480c101030611800e0291100140c450f0403c90b0456041c0043c0c828160f4a40c0c25060a503510744905204e40388080010002501e10350341c0e004140c40d241000314510035400b0750750b25101c140c0305060400d803660001e00803008003c0710340700300040da0511740e6146160b4081103000c2d40464041c448120b040d40039800d180da6004020f400001282c43d13001800300c29030034405035a80609666141e050044892403000140b4640c2d0a000410100e01201d0103401000c1c019040d80c402050710303051050071030707000c100c2055440e1741e01c0240c0044564042805840b4508950080d80341c00d61907000104404414030001b4110318002410502507141c1080343c20040e5040841803148035024800c1d030307849461101110001c01955490f00740f54049418946000340e4005021f07040d00d4941c8001110342001c01003040e000d011f40c648020f00041c060241400880b0000c1d518a0541d05142800805150040c0d04c0f6500c04ea10910f001c0c010804080307240c4030224803104032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 305325827 1250 305324577 305324599
    0x10c0329060d140f0702060a0618020c0c09100e0c0306010e040b010216030503180f01090303050702011803080d0606030507020706082706160f090905040609020a0b0909130f02 77
    0x1028081c06990000c3d528010703480c03040c400000c00350f840300ca00480b169002d8035580c0d0350302c80d2110100c80c2c82d0b00c40c4147c0f40000350002416000390354010014010000c0594480c000d55001040b0608015203802d100002415402c000000e05075a21a400000101c000c0d03146041650008100d05038520809101b0781e0786000300340c12a8000c029141a90f0100410302e15074503664205541c90350082e1241914120300448200818030703240740c001c84101c1c8161a80c5840358116203003110b254100060482c144858111324004918461300100029031045540d01c0c3d42e1241840c91b181a2035081d8004000e040c2007005221310103030041551004e0340c4e0035140c2225641d403020b03182d420412425000740780300002100303807585100d0007180b854440c1092600466210301040c4003114102211018000010303039422041c000301e85a5045180c00031300401001c14896081d800040001f11968021400180c000400001030b050400c516030b4031006400521030306402c282c594003107250568500911410100c88 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 305327077 1250 305325827 305325847
    0x80d12050a09020307120605100602030a05071e120e03060402150a02070312050301030c1502030301060e030f010c02160b03041a06030f011b140a090905061c05010c032906 75
    0x10000502c5600181228011503503922540c1c2000803128040d0b60550504002805507003580d0042d100311703402940103501e01141d0340d04c1241c0981000c401103d43d41044204c0350905034043c04a03520306030003204090745c441e01050002d0f1a402e0b0740f0f001c95000c0d410120400c00942d4450f83c80c224406103000c002995201045022070a020300381d0002001501d000840c442407a9002d070180d41a40c3c410f0882c03421403511040c0c217084a18a2041101c0180d1042005014091140a1211442c04003904452800503504401030035508000030724030060703025011100d4081d044125040c02051076110407441c6003000d440740ca10808010001c1c0c20380c9045100840c07840c1c1c40800080e9030110303982008100303c0c025a02d00810098a003182e00d0001003042c441e28148238920401c0300c10011040e1100030300d040c90f15900c18040e2038000d20295201d01c2c0b505070101e00030041426407090601c100d00009080b035899602808542204000c82c90790000c801401d210040100383c1038031545001c5511644902140f1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 305328327 1250 305327077 305327081
    0x206070e060904110301091b09030f020f150a020a030905040605060717040b0313060f020f0909040201050409230108010b010c260403030c0302010e010507021f060b0a1206080d12050a 80
    0x100850350b15200010001a503841280d20060503c840700040881c05408c10400700c40643d4140000b400d034001c81e540c07540040c82c04600d003980c5820098a0b480400010410740703086030700240b000002503003004079038108050340102c41001820041390108505400c1c100842c1060103030038001000100088110300407902100192002440ca004e880c2d5920716040000740b4a80350b403c0e07021103050381001c0c1c82e014103c83c58001c0d9000258030324507450a1403030802c100482e203403000e4416818440b0401010400810780c0c0100c01d103000b800a8508426001102c1030440c003201648401d17403c2e450801074066680e0311264a4140301d400018140d00d204180001100e03109070131950441e403800003d03000041580121a000c81a4000d400810150444404072030076214110b811000503041004000c00341c08442c198110f054020303190010b44551200d40c0842d150b4003408000022400e035141e802d90681403400341c10050700004015180415290001401c4071074038030040c8120395220300025802c4010307a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 305329577 1250 305328327 305328341
    0x108010b04030303110903030301030f060e03120a0903090b0f0c1905071509080a060902190e28090b0906100f0605090f04140a14011508090a051b010f0206070e060904 73
    0x2c0c25130749d1342d503501e140025069040c00350071118a801d015402d8541d400100a84103005840c0c00210082d543c5c444803070004000015044007400075070080800c02000c800098903001c0760100c0c085a039a140f642c4031070f2130841c51007001c284120200c3d01903000250081410000c0f100101c4d00030f41441030030b5506442c1000c4c5600494524451000140e041c068503800058001c0d009544104070440140000070200503203002d40100000b02070f001c14032240d4016404c2600940c613982c1e82c0c00000ea00c0c0080b034165105a03009036140c500c01010b2120508041c4a4660005028248070110380d180c1551040900c8483c8208002e1160100b010081d644072a481c40300307a014024010040c281e40c0408070445c003102959591202840c103044078082a2704c14214a0580301c92400c0001e80c070b81c11031300c00c4810400040c0000c015001d45901c07000000d800704801907905026521441c0c085420500050074070440300b014808550084c401d000d411608055942d684502c143c6d081541c07042d100011502030924 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 305330827 1250 305329577 305329579
    0x1061a0a0c120503010317090a170c0414060f100c0b040c3c0b0706020d0e0312040b0a020702010c0213020f0c011509140703020313020a170105060108010b040303031109 74
    0x1e0a9003182c24950120045040ea445018030380100c0341d071095600e0b101c1c05094101608240001828400400c00d0649444903003c07860445507000e03c00404241507916617141c190603144c0040c00d00200380f07810035950894600558a0781000021060000d09214600e40054824481c0c2d60124040c482082802405040b01c004810b120f0804082030138000041c031500b10444000e080d101c507008401e46100b000440d90343d01e20782400c2030740325100c1000943c032034441c0c00b607aa556891510b42c034440600c041d00c100034086c0040351080c5098204000c800303800800c0c548800e48100031900060380c020050071507003034065070443c01181c07844200000a100b00151714140a001280300b903a035a005421040b904c1900079000300c0f2075072342c400c40350050340c00340340800030007075029000071740010311941c040c43d400b00c2c52038025501c1c5050342d00414184005034001e00300c4c0361141070389500001c40034002c00d41c000c1030a02e8558401e41c504288011a070045001c02400c054032102c41020380301c282c4003a13a0b20103030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 305332077 1250 305330827 305330843
    0x30e03061e01090902011211180f030a150615020601060e040b090406020a0201090b0a0603020f03010c020d0c08070821060a0e01120c0f171005010503070302060912060103140f01061a0a0c 82
    0x5008d00540441c3d070401c00700c8607201445242e640403d03041c80031604e102803102400500781c40c00d280c0e9070030000d90204010214801e5498a0000706040500c1441110044680203401d036035040510007000780410f4507446004a0500b09034903055111140a9944180c2040b00140c44d070424090403800740031201c801400945508050001c0f07020140d02c14407c40c0d10884a001011141070281420380340002c803a50096005110810911030044d40c508844512403428549000d0056403044403030741105042d01c90f40d01c86d0402800c840303803402c48400d420030022154001460f10b0081204504c035014044c204a90f00110400c504220702d40040c1000340c2460090044050346903d0589143c403070103000604c8610a110001d042550107104840c1030303503400350180c44400d05503001e0141a511100381c00740c20000c1c1650751401c1304403c0c01a18069441008025014002402d10910b4060745801032805a45001e80c104502ca40a26010301c108000201e01c0d600c600c0c0208090b200544810001340200d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 305333327 1250 305332077 305332091
    0x10e03160803041d092d060403120501060507120509040603080304200607050d0c0201200109060b060a08040f02040209030d0206250f0c0606050409030e03061e010909020112 76
    0x100400030300162007030a0200071092109025200c0c000308262080070b031507040100c1d80c06c0c1c0040c1511880980070107400031180310884440d103151820704101c60540006080b250040c4461040d400365900505d82d03403400f10b0612400352181c0501d201d81004040034080f00181044154890381c028100035074000b41d0068807031525082818641c0110408242c01e1507102010181c0703850107105482040303070400000c0402c248100815034502c60005810f9050000311030300340482000940222510301100c00000c42c5000062600c203045c7c61041030f21b98840c9000f4050700e19019406370940358060b0b08100307000b4050305070f07001080003449400c3d03080d44c041c011131212491203a00000d01c1d6003c0c0700350161610b11800c5951150500014040300ea00c00540d0040e80c2039101c611400c00031021900a81c40041c00c16990320015040340c03040c0742d080317012401c613501d070b000079140a022032580034225591406100080d29102c010700e4005028102c0b0180c3d40e4401d500959210f2807280035200c1202d20200018 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 305334577 1250 305333327 305333339
    0x180f08060a0f02040806010308090f0409050c0a0b0f09041e111201050a0e0610110726031813090501020f0403050105150303161707030c0312061202010e0316 69
    0x10350340480d41c1c41903590400c07107210440100d901c200c030101c3c0c1d140303400ba040a0342581c1e20118140c0c400d50ba441d0388001c0e5050107482c240d54900c00d9908052184005000c1c410b00e0609200700355410703501480c1200030a001d01c3c900c080c1c410045403045241100c0c00110604400709002450500c02040e01d445031410405403102c186000007071000c880d0402c441c09103681d0ba00d0802010182034007402c0743c40010350010602a0600046a1034501ca00c1c1c01c0c0415002c2d0241590f615110701035011040c0003140d900c100d0580e4991078404208203141c03601035441c111400a03845103a113884200e00340a5140c40e40328a0411031640d000300d90095101d0020741daa5600788070a1051500030380015100e0f54a000301003264000600107160603118040c01540c2040720003d1403600503a900102564440c4c4003140e03405c4544205402495180c0c420f0b1208102000395090090107004c0101c0d6141e981071a000c41844140b45810940b02c0b00c0764246007811490030004c020a043c000b408980c0e4080e0842c545002c2030b4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 305335827 1250 305334577 305334583
    0x91b010315030f06150801020f0d110c010c02030a2d08040f120504060f1106010308030c0408061f0e0405030d02030a0609050a0b0f01030b010801030b04031704260316180f08 76
    0x940d0107417402c4400340d41c407085020300b00c0c80345651200250b203082111070807441e40c82e08001d1171007000090003030030102e42c4c0035034a00b9182c00700d0035480142c00020f10354a0954000640341147d0030900c0e484c00440f0b42200c00ca1a6a261848001c070610000800060820201c11f0300c803400302e54400d080044000341c03010080d206411a004c1c04020442e0b101ea0000440d2007401c0a03103403100d000c0d00600142c0d1840c0c544000550000d0021506041c042001080d040b4042003014021141004181d12004a00c0d00042c410308540d04003030b601c112001c0038000804c4000003511b2411903100001a501e49502200000402aa502c80600c0d9410002003080e40d03142c9910003580719105888000c0602030300001141260f4a03001a203010625860050000c100c1c41c8907400c2d44240700e410050b00041d04414040186541200d0464182481460b06080074281a081d54503020a1048550940c1800070803800c1c91020028a8810420000182d899000005114500400a19003012152030f11020342c036403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 305337077 1250 305335827 305335841
    0xb041b03050106141809091e07030611040501051206030a0f030804060c0f050d02090303040b0f1305031c032c031206060301030c030210020c0a09060e091b010315030f06 74
    0xc600e282502d20040b010800403200c48284014040702c2400c0c1405c204a4841000f13401400c5912660440074100030a0038069200e840d030740350007442010300d140703010402d1710040c404010300f4132005c0c0720420060760800c00f903130050740304807021408550b10f04002c40e181c0f500310078010f0512182d0290700418141c0290103d03004070b00808062040b12091041038031390102541c04800011420400d840112025601034100b40c2401401c1c0c07880c10b40d40b0b001081751500309501249a0240000d190354014410300d4513100280400d034003810ac40f02c0215040301c141c0c3c961481c1c1c501030544804809154080d1003a5080c0100c0d0b20704268030500301c000201d00d581790400d65512100148003000316245140910a4074101c0342d10a481d0080541140e0034450100c1c1024041001d40c401c00c100c0030312554841d1070580240c4004400051070030b2500d001400340d40f40c050306400d100c2c0c001c11101303041c00482d1560420340150038200469899048400d800c40101203600240c1607480c600d4404d0704005190300000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 305338327 1250 305337077 305337089
    0xd0507060f02070c090c17011203020f01112706030a0218030109050c1305010302130e031204030f0f030b01201515090c121906091401150e030a060b041b030501 70
    0xc54120840030595240712507c0003c01002c41c00001005620300014179407600300e00c07d1051350414200c06110350f0a640c16800c0c40d0301c04920104541c4d08012030369101d06242c50b034039014640f06448110120344ae03844050007440c0701d9900000d0240b01010041041e941400024000300510a190b0034090340b00e4042183e0700d4418100b42412460040ca0781c050241030b20b4000b40500a0350104201d20340051080c2181c140d540e0006000301800c005020040340e2049002c1c0d01c0300132002c4a10f9400a00f402141c4031004d0038180740c03070b100d510341b6640200784000c1191103903c1103030101c92401c030092404660003100415500c200e0100032064008050240e40c01b5401d807000c2d4500e03100c1c41d003a07030140d011b04140861184802c6000079101e07050450350717000309a01002c000880c99210382650007521102e4286002d01c1e880034004000303a6841f8100b500c1031500a00d805801000c07001d0000381c03203502410300a44100d4465000c0551780da04c5501c280030900c101100f181d100c070b00342c91029010f03150074440c403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 305339577 1250 305338327 305338331
    0x70609021e12010603031202131a0403050105100e060f060c16140301020301060210200a02060403020c10050a110114040515060102060c040303210204080318120d0507060f02070c09 79
    0x80070a2060500442d000e4941c90b8950f89403c00901180e0030007074201c0807211400c02c8271007030700181811031040301c0c000984180e40b525a4072030940c2002804d440b070240020035003039440e20081041558149955810803800c9903140403910050000461380d000e01848d2030000d0080c1c00401c801c03500c1c03680488041340c025105a60080d0340d50b40826080340400d02c114800b580000b28400126162071340640d40e030f080d11040c8a0502e0f0300e0323411303a90010b420079200440568401c80c2400b0034540c0400c8026107201c0203c4040417410042c0500424a001b12500c02c0c0900510310500c9600300000c0d00311482454111600100038034060525a686d5800c50442c2c01b50143c0b11004100306520100e0b1031446030103843c5c01e0f10b24241c5036035000c4a42110180341c1c0007107825002081350440f1240d000810007800301600031620307804050031909254980b030751007900c10702c0c88080d00d422055000c01d00d4400c01c0c6290070015215542828100b014110384821584c640348002040720030000c2c45080175050310340d5042d003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 305340827 1250 305339577 305339599
    0x905070906050a05091305060a0c080f01050f0415090c030209120304050d080c011d011a0319030e0d050109030305040b0a0b13020a02121603080609010f0b070609021e 73
    0x80c041110742501031036400c0b2106983c144642e051620b00c440d0014061034190f40608019201c181c200f00c1d0690f030312000d1540310312105600742ea02a81d6990040034404c041c90139075140c0000602031a0005031841d005588550801d8040002c002502e00240591a42401000071255000307000354495107400b440f4072010a418004c081000080c0e4090b10000b0b40240c6825041d07032603c0ea402e4002ca0f006405564941c4462141c8400301c0c3d1421281e20340c51400412020750341098941070b00075044929000342c3c07041212440040c1030141c84150703643c245c20003805c0c401d1a64086641a401c5100c040d05a6007802240803c043d4580e0140b4411070081c00310031713020740306e003010402230310700712092158001d409111409080304030ba0b00030014450140100c880c1140520300f46480307600f180a082401c0c118403103075441490340141c0d9150344138a003294003103030642c180081e4140c5001140a8082d60f0075004c2445006c00109031b0011030130940080081c2032456440e10345800320b81084152902600410039 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 305342077 1250 305340827 305340839
    0x180b070503010e0606090a03020310061505090319020114041d060d2f0d08090f0405040203061f050402120720030706090c0302041803110a030f0c020310050a090507 72
    0x400d0340c1c140c3e0b100002c2821262190300401003a604114921a440b034070036840040141e8003001a0703200c0050451000c039444c4d1510b551031143c50300102a8406104c01004510a039507004504030300c1c0c2040c14001110380c09010b00048520035440000b2107030241c0005000300d046c1d42d0324222000c0e04000103007000107641d20345050044c40d0038a05401040c2c00f0500021002050840303544602e84884142c04d51100e51005002400c1d00c0310740e0300280c03800c690019110381c00d800c240c41110030408060341c040c08541441d0303000c6650b6400080c6002440c51054003c10220615049510004d0034020401d5454271014000d8070310700e030000d0300d600c0085515070155181d51800554140e10700d4142c0e00c00380d8102140e5449480140104102c01c03250200529004401a900d5118011030300e84044122004c40322140340c00f9110900c0620090055800f803001c0d080040c1d440b840307000c92642035160050820001d03101103480c01c44001c0c11440414100006c200301014198000200e681c0610b04503062990350310 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 305343327 1250 305342077 305342087
    0x203130b0718170f0318032a0907030b060715050601020708030f1b0f0105040506180c151b010e070b0408060705030603120d09230606040b0301020d180b07 68
    0x1426000c2c1042d2503582c01c00c00100681c0354a903200148206445075601c0710404241140d002108001d6503205d1036008940c0c074281040030020380e088200100d6000c0e035007410040d00304071200310300340c0c4030308000b00025951500c250004580510050105a00d48065160404a05040d0b00024041d0707031900000401c5580f0020f001401c484060001d140303403100c0500c060066500c040306d0158050361040344003c141008100041c000311062000041c0c42c1041c1c42c1c02420a0780140ca6480e0015240d028804a0080812128002c0c2e504941c010b0321481045a0f8020a0041703010758044001c50b600c010500c4041034210a1010741c0c2a410348106603184c0180d020035006500034940d140d0f00c607000040006d0302030401540c11240040031501c01e402c00480079091b0340e0000c100c000347d207626070050034100a92050489007183c40c10708815035112111014540e11b03031005040900c1287c4030030f02601192002c1d41143c480c00171495051180103004541010040c00201c0c048071501c10820005003094410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 305344577 1250 305343327 305343347
    0x90109030e01050d0b03060c03010807050108040809010e22060f050d050304030b180a0c05270a0c11030a020c10030203060a03120504090c0f0f090b0a12020d0203130b07 74
    0x36071562101e00101030011143c0750010b060402d22140c0d241e56840381613504020003441042402c600c55600d41c1820412401e1042c10b901c010706020141c1e043c40006034a400a0f14101f01080ca40340c43c50003a10030000d000000d100c0101540712400b2840c1784044e0b500794214a06903201c804041c2e0005a0b900203004022090010192641e04103000500c0012807002485800c00444006040301e48801041182131460004040b60f011020030320820580c10007200d00741300300042d150f1046d104402c0b81d080c0240c51100900c500d00c500ea6802e4450029409010754000515803101241c1d1100209000a551103207111a030510a1030700c840403e141502c01e0086a102d64030140100442600c1c1d5a0b400e0001040c444600d030601006120105144015100358414429643d0701e030707400e840f119600680302c00080700c1c3e41010041d40c16800d01c203460040048071424401032030204201c0c0b010b070080c1002406584418140030380008180035402e00c1100d0114030b4031b406103202c0d0400b0f8840d400140c5800c905 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 305345827 1250 305344577 305344583
    0x50712094122060914160f0c03050306032505010305010e01050a03020105070614040f110904170706090c29121801020705010608030a020d0509131d1b0405090109 71
    0x84a40010162101d80341070015a10481400324503e511110404291011140001c4072039038940c0400c00703114243c0c40065a400b8560070000d40d255990340004010414242c0041c0a2000000104001c0d4404100e503460301c025040301e20346038207070141d00151140c18500c100c0e800641400b002242c4d4072104003400341201e6004040a141515680c01501d0325004207405641b0036640e40141c2032020300b01e40ca00b5100f41c0c42100c20514881103441c0c050780b01840031180501800713001c010000010710081e441039082d100480c2d01070300c4620a140c4100500500b060041c04070f10104c9001684003401d023401c14a04000310034401105042080d001d045002e01000d5a94081714240803444440f4181c3e0300c500400055000585401c5907503e0741420b50352190300186842d400080c0c004909581480030a04442c1e50b4503049140290181c0007540289403121404a0aa65607079030543d449001c5a10140511214080e0354501d0040000620800e01c4280580d010f54180000640c05550611410b00384c0c0d54 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 305347077 1250 305345827 305345839
    0x20d140d111e07090e060109230604050c0c030403080a0905030d0503150109030204091202010e070f0b0310030b07020f0c010e030a1407120f02030d02010c0507120941 73
    0x41d422818500520b0510038141c10300403504045107502203070240c0086411034900500565141c1940c034412980c3c5403d40307140400200c0780e5650582d103203503441c0390458411180441e190300c9002d100c0a00c2d2240c6080050240f0000400104001c0358201a1003203052580300d405034159100245502c50640140c2003002403400c1000603144403011241c0c8458150614040009903101d0340403e0032108034180c01c1d100321003450000e015031603090190b801d9815040c806004850318010031400c004201d0301900b0119180400003400170700d92460084019900308123603550a0138140030203034480c41071703480c4e840081c00f0314280321401e540034031701540b60301101400038041a007551300d82c01c40d562180451041c141c01030300000103070341020b03411850042d8042c11045150304030900c10103291010508054003517904040004c0d030a16000400d039151980c100c2c000e580a0201134500320b07184c180b640c01140120b21818455240711445d0510a40e43c031b103414a488003c50401c11010703804034902c45005034002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 305348327 1250 305347077 305347093
    0x1202060703030f32010506131a090901120c0501020109080901030513050d030f051509011502070f061e080108060a110f16120302160803040f020d140d11 67
    0x684039901c04903100104440004e8030140e8000d113a00890f5007980d54045408080300344015003964642100e00400d41142e0852403d0031940f544800d0005600c0b424003203c1501030680341e100949030840b02201001019082590384459115010030812031094130501c180c0d580c0801c86500520550b9035088d00321203a141007080d034400440c0640001849201f1310403060020100180b000c00045502040c142c40108507800c4650144044590040c400351800300041d0210b20303940c994458041c15280841c00540c0001140c00c0141e1902d141c2d68004407200d0713100d00e400900345134010403c0c15852407000b0004c441038028442110320078000e000d41d500c03a410140106044018541c00301700542c25034000c9500b49007820b400c54015070400042c003a6a00703244034105040242c103107000d41c0b580841e42000c60501c0a20b00109110030a0301c20014089807000020606200044a030001d95690040c160950003501c0c0c600000c103101180741d0f44130203110785a41c40c03920f140603c50107003503000c1160007000c2803 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 305349577 1250 305348327 305348333
    0x3110307080304060c1b06060623040527041109060f0a0605031b0c0f12030403080c030406060305030304110103050601022803090e010828111002010204080102121012020607 76
    0x8000041c580f401340020040c82e04981e00c0d06d24003030601a4014040025094030b0200302410b800c02040380c200401e50008241500d1000220548003a51002d440030145092480007034807040c00180444040c600b009001c000030000c03009100c5d81c0109040e01c1c400c100d074660005020103942c1c0c48800b00d9200c2ea1000c07090140600c90f9014581c4003100035050340d252002d424141226a200d01102d8203650041c903404480680200008212401000c004500e1464541ca005100f0b40d0082c0c034400c042c0d140040410240a00c41c2c208602844c0c000303064a41d40c0c1031500c2e1091100c03841032003190100c0d09000c0000c0d41907002107900341516107a203824400c201818012422040c5540000324240b007030064012416190040c030a90107000f02500500d020441c090b6030f00e0114200741034504210f0001c51100c000200c600e505441c0c55030050303c9003d04c4004410b400d9019014030f4002060541c8041444c45251507020041130182c00480044452982c60342c3e4061340203403020601a4105100b00246000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 305350827 1250 305349577 305349581
    0x603180f020d030513120b0610021f0f05010e040201090b0a020d11010f0507051c0501050f10141804050a0e12030702070513050108010c0f0e01030e0102040b1201030311030708030406 80
    0x650f846480c02d00d1a2005840c0d115103aa24641c0105814826200d110410001108600790300104111242008281c8100340250344901c0e00c1c000002c40441420a0406074450b0341010b00e0144100800f8007030342d0f03103800c01c840000208480690024140c51000244035041e40e0032a9440071050f4040c003072018410509840540f500103204900750b69810806035074402520400f800f881d5183c3d180c0d961b64441c1091301c141d03980c446000d11001d030310b41401040240c0d68400c880c1c50040055420109810101d04242d550525215025501c0302c00000c4481c2401c0a021003180e03182d40840c0d082102d6291354410b201113403202d40f1340b01c065030b0183d842d05500b040700b00060760744040c060ac11200c10984a00108440c1382c00c20740b10000443d01c1c1c200501c054034003801442c410340c146160000c1c0021100c07000800e8407451080d442e0500d42c1d82c40450020100079011500a401d8640341c0340c3d520700702c91a07000c80001091106400040f412207100740109004000c8446250304805103d0954030746441d5200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 305352077 1250 305350827 305350849
    0xc040c050301091806060605120a0204080606091e0a0606140306100c020303071203020a080105040c0e12120c030403110901030b0f061210331406040506040f0603180f02 74
    0x8000b219050313041000801c18050320000e041603a6a040c3c0b1401c008008000356031f0003801038810b850050006025a4200060703181e800002154488441c0c3c0307400c12416900300140d80d0301c0d50b6503404030040142110b241d80101c401c45502d0784e038514a100c6e00c9a041c1d81540810760389294484e21040341407036024442d070303c83c00421b40001d0559182c0385855484e506500c06c252030f0030010035004036824801c144c0190a4500424040d20140040c2400e000010724000200046500c981c03401d801e1560405020412810090820022203030780d80801e0ac11103a80f81c11601c41126281c40801400304581018180e0b10b049940c03018400d9065141c2c0c021030a0807101c0289104d401030503512454003049000c100b0100c0e40e4030344400005440580c0e0080c2c40106240c0c1143d06801c0300e0040546464000601030101207800165008044401c0980001d416101d168049a849540843c01142da1820035011400f07d460750b4500b00400030349040c0550a0320403405000c1d121070202c000c030b00c01500784a1850341c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 305353327 1250 305352077 305352101
    0xd0503090a0f1a0f0702010810150206041407050a2106060905040b011a27030d02250f03080a09032a140627060304060e0c040c05030109 60
    0x281440410004541e8401d5103a009a50000b8141d00411052107080706402c0580d0406100c18640418100e280ea000d01c140320b0000e04110040b0009060124078401d100058116103045501485022600950307944c01600d066274000440c215030f0703600500c006025001c42d81c014200c1025a0320300000b4503260300d58080c1306c00040b034400e003c1100080d0f09210b060f0190584803800a9981401e007000c944442050300a04024801946e910801c0d540785416a65045041e168140401d142c81003010f8400c0710302032a0581511920b600c05400b10b4020500d000316008070400030760100c0403402c802d400c407051031040a00c2d0086900e801d2000c0b40f40e041c000d200780545820b200d81c10301c1d56603440b0b00588214030300344200c011005141303881c1e00b0103a442950040c160948940354055520b4001020340c0b040250211014006c0c0c4400d054403002c2c1200c8824100c2d008080a40707034a041e00b4440cbc09841981c54403020f41c01401103050403454548121103140b466581c0b042d0450307082103c01d40080600c00161 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 305354577 1250 305353327 305353333
    0x30804030302040f15020f15131e060b01080f04020a06030f0e0706050912030702090a020a260a0b031c03020322080405040510030f0803060d050a05011a100e0d05 71
    0x10130f00d1014140028002c10243d104d41c503510340010002801d1607241d442a1050360081441880003690250400d504242103145810f030340c50283c0340444180d9019a00c1420416480755200248281544000303daa2000e07202c4081d107941d141c4c1e50800c0e05800300e500961266105605208451081d4404054050700f81e00c005810031004908034508103480d40302100140d00010711103064103101132901906044d1304015418485c5c03e43c000340c80144005e24680d002980400c45042c0c051080301e15040041e0a403a1065080c074100035406074454003103c02c41040c0b4104a45181d050400145650b44481d5881d0317103c005041c880d600b10003942c40a420f44032908a00d29100514840d07101a2190080c8a901c1440c1d44916100c140300135075000401c17400144c44925070170408248040ca00ca10b09079445402d6658030360307500c07002402c8140031a501408511690040204000055212602e071441c01201050007404140410007084401258540084c54880e0740d242141030002c49506024031440a03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 305355827 1250 305354577 305354579
    0xf0510030f060908090d0506010501020f120405040f320f01050d02010c02010e0a12120926030f0c01020c1209060a1107080313060f020304051e181008161203080403030204 75
    0xc0d6891b5900b1100ba0303020b0f0400801004603680401c80c00c440b50083c10040c01d50103009a070342489901441c400d69018035100c48242c40781c066641d001540701c2032104041445d003802c40341091039010741440c203108004940408505460103610145040700d40062840e00c03400e07003a500440c2d00400400080381400048000d6049507604c01c446e8001600c040d03070b03e41a100d8018208060b01d00b01c080a48400e00264060a00c40c00b2034551141140340000d0400d85582d04c00c1c0e200191841c8076940c03296514540200b4203070b0b03804c90190001e16802e0741d08070840b640ca03201400c2d03007120340c420786a10f9613012400708003960003540540313010002d642c462002c2e1804595140c80b101e003164031021070b4400c5541003440030301001d6000000b2010781c007000c3c401541030900303110108101c186110200e048400300300700c0200c010750f249107419001c100410000c042904106030130080c0301100d40205501ea01034125101d5540701440c5250084a8020701454510881d40d00c00341d500d980064410f900b09074007040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 305357077 1250 305355827 305355829
    0x2031309021c0c03020d0f090503040b0f130f0611010b011d0d05060c0306011805090c0f1303031110090f03051b1b0117070e0907030e060405010f0510030f06090809 72
    0x1081c5088003e50303407005680c5213142401d83c004c4969560503088403914141c64003000c100000140e409a908a1303899550314210341040b113030759000303a00e443c075051000d500020a11030030700c198040c11039890740c41d407220700104281480d00b62686656068001603240c030448059016189086542d0700c0302901001903003d40361103040c10540101c4a0b0102d8110000c1800119688254582ca00c2d108a19070403440c1420400007400d0458090a69184000c002c030340805410b00700c0d000ca407026203641140425a954a103009405900e00c001031030043d018505885410020368010242050b0b03010b21040000c1007a594152020b8000045030141c180032038000c4444607108010342000160000030061409220000040c4000f075907008651091a403e0240070005402c81c01c61042d0090131611580c0603030701c2140450041841c00c2090150b40b00e88000e000600c1019884403c031700520380c00a00c2140d9500c49120703042c49840c0700c001c1030030294400103400711310191300021026100310340c00c501c1c00d40c5c000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 305358327 1250 305357077 305357081
    0x314060f0a0302060d02090a05060301060804060518030c0a21090b0f070c0e0f13020d2d0305030907080a03020a0b070c0f03080708060f0109121401290102031309021c 73
    0x101000c5807140e000031024681e103840c4c0c80b054009c00c02202c0c81da00e1507040200080001c10044d000401c91510b44010a8136040c10081240c101003e02049940300c482100303003140e968202c440d0a0b1031440c420740600c4445080060b041003500d482e61161408540740018000e031a40c4082a0744001c00e005000100005c0e40341040f090013042580640080d50403c007220b04c104802c090950482c2100c0710740c3e0b680068a800c1c52880c0305030303042448021400112080c05440c00048082c104a9054400c042410582c0241c050b40c0550070030400c0b0340d1101e803220706880c1c4da08000d00c40900540e00034140c0d0303000a0420010640d110b02549410101501990b88401c0c1c900100901100401c4072368080100e032075804502c2c580c1c0035104503912541c5281440c0042d00560160180c1d000d50080c0007088001e200307007464441e400303c007001c00800000850029043c880e440f02c9c90080c0d200c00400070300408079031002007500d0451307842c48003007048646084001e2009501c50800d11002500c4c0021074003881d1a54 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 305359577 1250 305358327 305358337
    0xf14030a050d06050d030804060506040f02030a0c3c0c08040609080105060405010510051e0c0601030b0a060e060d0302010b0307060503070e0a0b03012705040c0302100314060f0a030206 81
    0xc0d11580d0702c4912040c244802d03586140c0009014042181d0210080b9511000c4035411a810a40c00100750b01c940d00403d000c3d002c9440b0b01c4103018000800e200d1241c007941d121482950a42d501d070021201030415140054089004200c505601c10000b0403904400345c0d80020030b208d16041c84a001e003415643c0142c2600554400d0001c1a00c00004010716982805003507480401110100301a42c1050006040042908800000c1041c0800c001450280c20340341d0703002001d106803209844a00c0b21003000d076035000074042116040100000b20300f000340300380a00750030303584100000446a41d485080c49050001c540d0203a08540d2104d082c042240c0302440300001a15031940c07010b03130301e107450500a0701e824000c2402d84c1c018051814200403a45060003030720305684221381040e8606103d8804c10916103040d902074401180303428180010841610342140c100c034420b450045151828507401c0e41110308050b102401184501d0004105213031443c0e2000300800d0042483ca45140c590700400c03180c0d045 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 305360827 1250 305359577 305359597
    0x9090a050a06050a0609151401020a060e03070204180305120c07080705011b0216030624060c031b0209060d1b090515040b1809030412120810080304030f1403 69
    0x61001407003581c1404d0301441c000f801d0340007020b1207042418022118a42542e00c200e01000d1202258401d1f01d030b10a10520141d941c0010381407000103280c5558546a070300c0100100d10980c94840200c0c09112005640d280d440d40603203c260400031880121103000d0002010304588120811a10000404d4800900481030041b0000108021103803c0b86182205921518007954000702c40b6080e011090107010099a501410203c0d120450185440101080c001005000e10700040041004c5500105081f07140d4001d50343c1005400701400c24081d2141e100b600a90003e85078030000305503080c0081c005121510072281c030b0000312143c2c4c002040840e100d030007540d8020345450602c0108000d40d803e0400c1558115810055800c0b081e00180030503003001d214030103d400b80e20000e40c10040034404c0d903000788540200601c00c5044e6140c0800c07081483c030320a07000b0030300d42d10110345141d01081303841041c0c03008080158030300f5045840b403900100c00d00c5003c603590031400542510251041c0060300ba00a0703 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 305362077 1250 305360827 305360831
    0x50402030a140d030e030405130b0d06020403031107050609100806360a020a0203030117030f041206050a05040203030405010309060b03070608070f020319120e15010801111809090a050a06 82
    0x81c044004e06691805602d9121759005000502035541c6034001800c10941c0c5210009519400e01c0200710300d2001d00c0005002c00303201103400414075401030101d02000d0303c0c1c0c1060380c1150341c4810820250307000f401e46541d0840440c42c6a00b111502800360141c010100601d0a40610009003072550030601140700d00b04e448000c44402c16a022800c18101d8000031651025030a007a0150300003035590005200c0c03858010382082da140300105007801110210f900903500f06035610740b40e080e075028403e8031003800c07209689420002050100c2501c2442c2c0115401400355141902d0b280045002c1c041d030020698000f5920310159a85540400202c03000789401d882d42c624500d006600a40301014401c100d0f81590000c01440c144003800c072284c1a0307444500e0a082d007210150098140c002c1c00d01a40f603caa600c0381118018100c48a001014100c8503030000078080615080708951581c0505e44094004110780030400c0203601d400c41a03150310600010480b100080c2580f28140303070040c0e02d10181d508607 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 305363327 1250 305362077 305362093
    0x30702040908090a08061e040309090e03030f010b0c0c04020a050c070807060f050406090608181623010e040b03150a02030a06050111030702040c03320105090415050402030a14 77
    0x3013070882c0d50318000c240282c060b1070a07103000003c1941ca01c0d80307143c1641c580303800320002504140c0aa05900c0107856080400c2100d00c0c182d01c072903a0340c2d600688880742c46a02c1c0000000e03510036400308454201c81c40d40c01030714020716900d05000182d000903040700709201042c0884001580100104401409450001c4c6201450610044c1c00300802c0c40c09082044401c000a20201e0b4001807207904030b0340c039854101c440d640c0e5070142180c55005055a15454010502d0032409a0b00000030401501c9207060300703400881c4a5040100c080252103d0725001c1100480242c00b00e180c0750303014107180c0b0b030090207803401046c950b00a5040d4250071a2265500742e404130034440c40038003d00c540c60103402c003801c2464560782d40d882c17529901c0c003c1038002803185407520800300e5642d120f508404122010007500f000b02c050840d25007201d0040c003000c00b0b041c042040000090034504031901a0250382c002e80103107035107c03103416a0400340c84018070a0341c06100340128a400240f0800c1500034007024503000d40182 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 305364577 1250 305363327 305363329
    0x50a0b12160915030807050a0c03110102062a03101e090b040203010f030b06040b150d0f0204060903030f1b0b010509091b010309050a14150f19020c03070204090809 72
    0x71034207401ca42c0e00c0c1c600c0d0110b140003205450b000303601521707001044103444085601e08249800b09151004103840e2405900100300010b602e244412020243c094481a59842d021032030f01d82c034070403005410f0f0403003541d00c0034641d0840c60003541c2044507582c9102e101902c4910100d8140181601d8501c2071200020400804603c6d12505054442c211400e503e107501d400b4408208501a0001810441d680808900c065541c0c4d071142e010780001804114101010522400858001d603041c104458144a40081c5101540c800c6170241c0c1d1f11601c42100507403d40c0c804503184012108e080007840b03080071810b106d081c4d484840f54591480b0b0802420780d507041905124040b18060140040c0e9841043c0b408418110b051415020b50400e1074001800c2d5910700b800352034810903660160100102c2400e074850680013140a40070b160303d5500014603511035440c2c801509404031181c4da071080750f540386084280920303001464480040d04c101c03420301001d500000d0884d200c80c0401c80e45403000258100781 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 305365827 1250 305364577 305364613
    0x9111e0c06090a0f03030c0c0501050408040812070b01140607140a02010e0306070c110a051c0c051207060c0c26071505041406041a0a091413050a0b12 66
    0x102100300c6000c0c00308001c03c2c3d503a502030102e841d20010180744e00e41c0c0c8402d000c20b1144046a0301c50f80c11000038401d0b4201424a042d880e406030080c1145801402d8032081c40852000854442a0703201d100f0352a40d03840c02012491900a0000070340e8411070170402130000c181c8803051201081c41800141500c0d0300544009802210a8640c0601942104040081240e01702514803919a0014580d5000c840e1400000e03103404081c1c2c00066010b180118001110340c3e42c80c44d956004c2d44102e854030790b00c0d612901003080c04d0754843c0610500707034803081c81404414031500c2103000007441400034450158483d005629101e603080d40b201120131000c21060040f500070008000200680d6107004080040124001c000d03200f94041c000e0482411400441251240c0c400c960080564841ea80c44040f00003c01c07401542c002d11401e8001440b0b0f0101181600c0710030603514461034010804031928513003031034002c09003c0003030000c00159131b24012128251185160108840c010401821a01c2862078802007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 305367077 1250 305365827 305365831
    0x306100f0e0412030b0f10080a0e0a0c03030c0c0914070f090602030433120c03020301050f04360b010e01080c090406020d1107140c06030109111e0c06 66
    0x3410700c6040d000e000214402d02c40003e100341c21031030701081500f0b61401151025445100702a042003102d460340500d00e62201c1b040d070191040b0203050040c460074040c080c1d03607101400c40180500000c0001080028095942c5003509445124018005030f039450b4600d048517602803103c2034640b030340d504200080754020407070703584001d990406124060030181c00079500d01a6006101c6541d582024440244040a0303503c078180800081d4810702005030800200003400b101000c02d2040c2c10242001c04e150301034000e89042e2000504040d9421204801708009406850844030004001710b44030300600209007800f8001d981c09030350000c6a4001071070b0243c800f88050340525005220400180126107011601001b0240c081751000510f85403420048001e100750109102ca262034400390042c4c054150001d0310071030b4010203113800000e801c0c0c0782e100d407500900e8045a921000c1040180444011a0b02134400f680401c0c0141c0e0611103045a480301000321704440000340e03200442e15400909041203066 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 305368327 1250 305367077 305367089
    0xe1e0907030507110f06070c02060706020309010905160e0a050c1b01150617040b2814150d06020c010605040f0b0a1205300a080f01050d080708030402040b0306100f 72
    0x2200c82500c8040c1d00d070304011f0070241c03c11400c0101c07201559030709811b84007050b4115604550b0b0b8240b40003102d0082c160003104440600500f5030080e804c2c4084030f074800032a4110500030000d580c070350032024001c20000307184001c02003040c00541403100e10540340c89a071550303450001446100c40318150800d0340540c0c0c4620308000a0f40001038054142225054001d90f0000b074070709450b12414401160b08040741e10302400103000000c2603581d44115001500380c0480300d15a200981ca5004107407002c00041344059410595818052000072015801000c4c0350301801c0c0000382c00c540701e100050540e5130100c1844031541c0c549960720300f1854110404001072071050114040307040036a41c0c0307540300d01c0251400e858032500b40b278540d03202a4600c07412080f903061405100c3e5032458803030809001403005031504416a4400d41c0041180d0034204009904140c1010b1294100491961103942580c00100201d0f0401d450300f6410605840411600d4003071640c45508590b51030074140628801c4405034028 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 305369577 1250 305368327 305368333
    0xf0e060f010f1a040b0708090907080103030824010e01030b04020d0204050f0306093c010c020f0304060c0816020a08063c09070305070b0a0207080c010e1e090703050711 74
    0xf1481e5800c00c0101c0b0126222441010344841840c2040041030241941a41e00000c1250800461651202d0914141c1c2d100b42c95a000740e49501031981c07030302c0c140007070743c41d80c00c0d07a032f000c1414219801806d0071048500145000b14019010b100440c040e42c0084072031040041e0040380c240300e10320742910340742218141540201020700d403000100b0342c0d485141c0051000103080084904000514030302007848129014018401c1d200a00b4100340241281214031005014844ac00300610030003008803002c645603a62a81c5000d5400c2d25000300c2940404886403c0008a48180d00140c4509601a0040c54144c0181619242510080040c0700c1c20310070642c4142040558000c048041012117501c501c4242034034000340d915008100d241c07a445410180040c407a0b40702c005012019540141440d4940d9402d0703030561540c4102c25aa1107914cd0300044c086000c1500208040c240900d204106446401c00e45100280890100e03001d0f54040e5a0040003030380303500811a00a4000d017108450000607002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 305370827 1250 305369577 305369609
    0x70819031101140f100b030103141506090a110d0510050a08030a1b030201090f05010c140903120f0d18060b0603042310021207020f0a150f0e060f010f 66
    0x43c4101c414000f010300da0403003244030115214107184c28400016140c20788605070350303503124184024400103c022006c0b191045c221316080f042850b020041c001d43d80640740c6006c41c7c40308441d007009421401141074808105011114403d2002d004480c090800b0b01405d00d8050f003401d091100f40130301074201480c50b0303008006203196150b0244020003091402c0700141e103d42c1c042c0c5400c034050f00142401400e21000b880c91001804010b51042d0300801064990f40240c4440300502020b0340a0080010343c5900411001d41078407541c803004113803494828007040d240c0210503100c0812540441c012a00f00454291280204031913486013584170070003105c0f160b04528007a900c0d981700c2c80c51240c0101c10041c1c58500003000e600200400ea0490303603450f03c15501d4160b080b40c0168011421030b070703600041c40399080038103a0b1800840c01e80d644640040c0341c000c0f100144070303444000d0b10300120940c14450751303858007038070600d01480943d0085c49000b414060035450270821840c4184207400c426006401804 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 305372077 1250 305370827 305370851
    0x70b040b1801050c030a03060906060e151e0f0414151b1e0c0405071e0e0616050f010b03191b0306020703050c01050a020a1d03070819031101 62
    0x3040d100a109100205902440007000490b064051481100c1d030521000c54215002c58145d0004800d8072964501041010f0790b8682c2151710211401c9120f4200d204644440b8034800501c0080c10402d962000c58807070b000b456a0303429aa54401c0b08040e003103086c080340a01103c00111500c2e60716600465000795805228508002544078090100401d1850805040803070310051000028001807144168150344164080c1d03070301c1d0b108102d000c80c4a81c2c640400a00118024012020f905079000c200610b03041a140003500c9a8044401c07590384004e0a1041960203170030114540c050394410406011800100d100f180d0a4909503005a0b11035048126402c24001800d4040c1500d240c001ca407010300c0506200010f4001d400035000504414000641401896084030080c212000d14200070417955a45400090803801100c680c40c0024410b8004901e1101c1c0c0c0d0032401070f00c0341008003922a544e68440406203090740f0b2900b01d200b50407040380e9400a00d60400c9035503a00410400c024400140545 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 305373327 1250 305372077 305372099
    0xb180a05090c071b0810290d170a030f1805100f02071a0103020310021305090702100504030e03210a0507030504030b0a1d0a05060708180105150102070b04 68
    0x8240722070003840803d4420600200c0440300c030308120124020960786442d20a03058031440d45148820302d050505200407050707810300111118482c2c1e500b1258000d42008001c20070307071000d681d40c2a90b0f00980c545500101300003076001400810860744000800c140c91007a001c0c02d80d86074055882c2a07440e14078840b000700c2d00100c0c01a4458141010010303551000301c0812009002c0c180000c0c00340015128641c044425203900a8141ea00840c2100c61001c24184044143c1c40342c1c031040900310b01522403c01103414140304d00742c2c20100d140151030402c2501440f400858030106e0b416400941c805840c003429080501c124014014014042803c9280c1c491900b6014866020040c08100001030240d0a0620980c02e44001d90b0384a2041c224030304107110344001400e160003600201c034800300f070400c40d40350002a02e207a00651010141c84203039613071a010758250350020421448005c0794100000750680138460f8034800d50031002070540700b0083c031000a1515103142c0140211100c20001030101c08008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 305374577 1250 305373327 305373331
    0xa0e030901080a02030a06031a1e0c0a0315180603120e031b060c0706020f1204060813110301020f03090607030903021506041b0c02040e01050105060417070b040b180a0509 75
    0x50f80000da90798503038880d0f007001000700703910207842e41040c03084103418610500da299000301c00c41c000200d2041039507400b6403d07004007500c07050040c150030008001c14034001c3e04025105400c020804007090356507406090070130140c10400e503c4e00d40e80e000c10310400100752002c00c4100d4042c07618009010300040800e54500c0b141d8800c81111201d071440038101e50f125030480307207407040f4541a01e6819030b0f0f5010213584c920a1300ca50354190301910b0136984011242200707440440d695a40e41417103d4030b032080440d41c540181001558005410005408180ca00740000d061401d07103080f07216660318040000500300394002e40048101800c001160010a5002503113104104503038030650600d803107980000d001840107c21011007034012410205d05180c02c04030343c596290085d54240a5005c0041107182207640c24002c0c2e40d4424810312040c00b094000b41a51100b0003102411929916103c0e07140c5149a0019407003030000a00c002844014200300600010b1490b0007a00c90302d02190500000036811080 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 305375827 1250 305374577 305374591
    0x608010c0504120609080a05041d0c0406050c07052205060901051f020a0b0a050f060d0308012d030b01181503020103050603160609060212090d0201140f0f030a0e03090108 75
    0x340c0c030f080200f48200d07640000000396001244580c0c0380d02084000c5c080f50481d1043c81c01319019501e00018013102c1c4070716a032185c4501040e00349464106001620590005079070314204d4490f8180c04201d030f0700c2c3c424038054210704140d40b41c0f66812440c1031610546000401c3c00e8000d51004004103d070340c6880800741100100300c0d00d005a00040014200d140505e116000703892001e90a05000c0700240e291722981c0034400e2070145103039581e81c0c0408c0c441c181000f0080240003480d035000410200c803904d89444000c0007080c2c038412000444e007509003800e0045030001c2e9409514400100402914001d5991f0300d203210500c2408140380c0308013406400ea80c1c502c8060b05268441000503841d60f000d000319038000f001f0804200740692242002041444a40034030313170140c85840c1c400d088c440014400e40c1c0c81c81e40c00414031062494583e004403180211180234040a620034406001400e5521015008004024501d280c5920301100c4100c2901d01d003c2482419070010008c011040c2d80c48101d00d640104 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 305377077 1250 305375827 305375849
    0x2010908043b0414010c02060a0b0102120f04090623010c02060d0f050a0f060f21051506010909020408100902130c02100b01110a0b04050c0904150608010c0504 70
    0xb01c2d40716000464000c5609800c01140c800c0703485030203201d41001d481d00a038091420f40d180092a401914200c50b501c0e0303503072400f50784a03c00040c5d012080c2d4100c10682441881503a4103806a10141c0c3d04540080d0010301400c21b010030300f88612013051045600401507030780c0b41d20005520494918405222034070290401104845500640d00e5003401c8a50b50400c0440400c00002a001444003d01094400c16500d50a10200211540c2c0c0c1d80120700594400c001550803541c5022040d013a10060300f010081c1c42c0041180c3c40c00030a00900c50141d8801e0140101401071814600040880a040c0c000c0c0104c1e9106000610558000048684d902e514500002a48a041c4c1c00050550056080e1030010b65080204800e00300340c0c0441c260480222908050085100f180c00565044550b441008015801070340c40c0c40104400d004565082070280301640c0a800541d804120388940444d0103036101c03008009482500783c0681705c2c0030300034950381000300454000c0c0c9900521910680c451103134070234 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 305378327 1250 305377077 305377109
    0x6031b0f030305090a0b0703020607090b0f0a120e06100e0109051506070c180f0b0405040b19090501060311130b0102120a020c0d0303051014090402060a18061d010201090804 76
    0x40c845c2c0d0307507100151030240f00c15901d680c01450000c1d07882100b02ca4078800100c030400d0005003043d800060300c1e1540119841e039403c165190204072008000c00040031030054840c44403028040003401044c0c094550080013200c0141009007807003d0220682c031032500980381c1410041c003088034541c022805081102c80c17550342c102c1d0381070542540136603030003241325000708814030341d4914895440745480101140c030034411642c3c940208401c03600111405804046507800003030011040ba01d40510016640c540016400480e4075190b0071140380f608100c4655840c814151040d142c401499604609058814004807541500007512103610315100c02c60b108001c43c55612060083c44034040741c1001074481d10030b0701c1c85818000c004e040281d60942165050800100b00440300c800a800c0a11000e00b40304e400d03489039424002c09611a11880040250512222190002072520507000740203995805912a20024103020070407180e00c84c040c191ba240c4100f4400099080007610201c0f11124600c601203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 305379577 1250 305378327 305378329
    0x1030c0e072f0a051605100c20190905010e092a12100501030204060510090605031306020a0c0b1302010e0907030b0a09020a0810030803040f140a050106031b0f03030509 74
    0x3c8480c00100411500031782e5003070302d00240c24858440c11168100c2e0110842d20421170f0a640344400644050041c81554500c200c102114484400c541d01c0041c0280800b416218003401c1c0840a0ba0042c1c92036649803401000122842621150080c4000d000380040250701c3d040c00e041540b070030969404e200c520030200d0b4040c0e6142501c516585004500340c4403102070420101c002088240000c0303100340c0c6030400110746418a09802c0400e03410700d45500f40d03050b05040080d07600c3d800c020300c5071003030800035200c00c0000751a070b00103400c20351110740f81c0c030280301418034182444850051104404802032510000540ea011014108890f0f041e40c4811041c0c0703480b003040f0040d200e4130f03c840da000505803900140103141c40d4000e05400e07249036680d5040342c440d14180020140184005817540e0424000f00e40443e484010340009144640c0c4068800411614420308024074000c0c00d58003a50355240070000c1c4488959440000482c000e10b540c1000e0404100d40d80c4001eaa000c0074040007004101f440309 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 305380827 1250 305379577 305379583
    0x6040504021203070f140d05040902030a0f18030801230405100806010305030712020304140f0a030501060b04030b0c0703051b0a3008010f15050f0301030c0e072f 71
    0x120b5001c070001d032581c40c446030420034a40c0c0c111107822101c0700c010181c0aa01c0704c0002c00c140480c40d17050380c2c90514051a19000001940024003000c4c1980e070344410410002c80240314203080c0340880c16006100c4006402c0c050880c0e24142e21040000c09810000151111040b60f0410607500464000429460386115500f0810780c540024200d4400d070710011090050000181940c5840f84080d004240e0050404a849015610642c2416054480111140d140c507400600703010b42c0103403060090980c0ca480300b50139641c107584984850a000201031040c80041900c0130f03880708a902500c0d141000380d42c2d0040442c4181c0381c07141e480c035100c01080055042e042c01040c400303e4000b89000315604484c0b1038078548030303c89450301e202d00c000301d10889101c6028042c400c0c12507035180d0700f407070b0000e01d890400e4150a07045030800c8204001000f148520201c110041c6003c0d60113842d8400f20213080c03044403c0566005001c3c1400c2c0500b02403890100a00001038032450080501e00c600e00d0105190203900d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 305382077 1250 305380827 305380849
    0xd1e0f1e1101050c04080d0f080138030711010204030f02190f0e1503010902090c130e011206051f0306090618110a060f1d0a0302030a050d020105070504050303030604050402 76
    0x1055500f00028408000003030302c050401d80718088241da00040d51400c040c1c07007140307071703007442d1004075506100400441d540141c4401c0d0038440d00342c8804800d9981104107a030036030810003515080c003000c018429665808a40705a01c0d44048008518090a58546980d03a800c0303544001d01c01d865024180c1c00100710500002e0090152030f1260004030303100c602c1e15585000451b5541c82e1880580750030140362070140290200300e03401622030055600d64000b108141d900040c01c254031051000800601d014040759070078000c0482034191940b10400d40303820020344001425410b8007000c289407100351030081400078030849605c07007800070381008180b40150190104039000c2443c4030128010f0414060084800f01c004a01100c0924003141c4800e016552400c1400e8550b001440b01d020380392801100b02c280a40c0b40c4002011282a20342d2680001e1400e0182c184c00c451682005030007009640d02401740c2c9030003030f807a0706000d41001e0408000c40c1c0e4a000081080b8411900c50010400b07544074007071504 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 305383327 1250 305382077 305382107
    0x7030506160219060606080a110a0807050c0f100606110d1107231306120206030603120703180609050f10031d010c140a0503070f020f0d1e0f1e 63
    0x101d800141e00341130001741414410240400c841100240c0300744181e1148642c011f0707a9103000c905203559007004503807501c0000c0210007400000c00c0520f001c00c0d0704110328a00703130301c41c1c00052054400701c0d400e0a0548009900860a01100b5001d29121000108940c0c41403003540c50305c009560407024540f45020260b80c00150840b11040340e1101400f00c3c441840b210410903509c41f94001e42c16030100c0304890840c46100051702c4100d000303000500d0700da4011341d008100281280c400a401580845041e405484114040f8143c0003a800c1c00c0101c401d0020004d200f40d0801c1014a032505011510b0021402942d901c5042c94207214605d1500a50241ca0342105240b100b014100342c0c41490303070003004500c00310400710703403040d180d0b03102f0038200c80450380400307400d07580d641c1503403200317801039a802540c403044200f540207200c81c01d1101d14080020030842007042d13464541102c2c040300310942640c400d40a5400304a40c1100740302c00d40d0382100340c0c000701440b0b50061414091a4610495031a1115001d80b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 305384577 1250 305383327 305383363
    0x603060c0509190e19090204020c0c180106021906020c0106030302030d1103190b1201050f071e021e0313080f010b0604080a0f0609082109070305061602 67
    0x40c900381e000000d44000e060030f44980c080c480000e54070348080c140500c42c02c1d041010b60070005040c005a038408042842e60f03a41c0100c6d18a02c0ca0340090700b82d0b0000c00320201a03a1048805126a10f41b0202401185660001c00012035060000080d140c1d800c401a82e502603202228100402c071aaa04071540c01e0700318802040000e41320710740207481e80d0100c41500141030074168200103052010040720300070304030038128043c08010768100c0e8000c2c1030443c421f00d5010b184844810f075166020700801e40b180000c041c03500101c3c036000001412200e4503000e0300310f0a070248250310307075001d400082e13444070000401e0141074100319880019296108041d415010b030307001d248001901080024030f40d01c120508400034000b0103242c00034070007240202d100d604802d03884014204007090b8100408211507000301c0011844540588800200b035104c0317843c13010004104160078106e070344659032268010503110080d000c401d00c1c54850075501d64024045001ca10320b5111547c41650081189020b818001000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 305385827 1250 305384577 305384591
    0x9011b150218032b02030a020c0d050703050a0b1b030f130c050a06170105150409270807050705100e040b060438041a0d0f0f0c11070305150a060306 65
    0x3d10303031301111101c48800c4020101c0d640030302c0c2c0350000c000d860b0707100017944c000c140f08551a02042050b0649400a40d22801001000720215100340070314a2018003c0800241604005014805d035072107031210700091000904c14000808250388000c0e8111101d04042e6110b0300140c1020181c17003001c0d03405564403080a4000140842d00140301040000d0500d8444171907030380e150140058808100c0580358908000c00040c400e00446034004010007c04d980042010101032a404a451400f52000e0302d0b00c0902284d880200070080081e1005000261350403000350210010142c0302483c40320105120b6525000840c0713664844c0c10555008110001840e10100d0081409032140c0491301d905160b82204900da070b280304907080c0200c0307040b645000c042d1652641e0090000c170058008452030b03c1c845485000c01ca44450b814050b00c80c0d034008000c40050007a40c40c84010304060f500e604207138003540020f03008001103400800c00d6074018100c06c206810f243d440e106a0801440ca60704000c06140c5000700c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 305387077 1250 305385827 305385853
    0x60e0618010e1807020f1009020303091e060703170a0624020a080d06060207061704060b03010b15030702010c030501050609090912180f0916030c0507080c0309011b15021803 76
    0x94140300440180341591107416400307e56200b0707150f4420000c2d4044c0d01c00c006120315410803030342c60a50000760301c1c07284a10792801c0d00000e07644e500c151010307030018005a003400207004004050741e4010f40d41c00001c022052070542c01d43c013080c421a220b0450002103100704204075009002c0007040c10b911080b0955650500c08040c0300a12079400b6540c01445561404900790340103c210750b8028801469a44450341c46607100c001070481214102e4155482d800e00c6151915600c211000d84040710901030384901c4c000c1c00003401c50b00031109001c209130400b00104000c0c2c482d001100c0e800d0718182e03405412950b0740001c01e880d00d0300d00d1881804080340050400f91011079401002031090702107400c41e200720941400c00000b10f1007a0f03502407015171a2110007010030301a60110b0100046824402d003014501d840d49a2281c20000c02c40320075800010740703040301d503034030200b40c40d40c080d8428a010360500054440c000d10f40c55060b000415940d0000c0d0000ca0040c6402000114400040883d02c00c400b50300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 305388327 1250 305387077 305387083
    0x6020c01020705070906080d0203180d0c0503030c0a06050907030c0905040f080d0203010f09090b0a0e210301080601080321100906080a03030b041b12020d020a09060e0618010e180702 80
    0x44107c204600480c0110701105101000b12200ca486440201e001c03040341e10104241400b00030400c88040d448460000b0300c5480510142c41460f000038007901200c149810b000e02071f18070082040f140c80c2c0106200f88005450109250b0944000c0c200014203551030b0303d00341e6040b80b010b80010349440070100301c045038070815800441c10386240c00c00756082c40d5503500c4880f042da5000c030300080400c83d0344800a9604807850b03011880c2c2c1d0304400102c0380144100032000844807018686100c00ca403001006200c40c1208000c2c207801055007400071482c0203c852510344420500c001c2c2030645031011000701e490504801114806412144400c202d1295074801b403a50743d1424010403004030b402c0425003d032a283c1445503251034001c05180d00100c00200c10b084a401e0203a0310224000d540c2803000e118904c0d403610107889000000e1f22000d0703003503080c0700c8003800000300340742c3e031910a4404121480c01c00d8016441c103260040282020a00103080d100002c0c1070080c02c8104810b525291400c001c0681c0d400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 305389577 1250 305388327 305388329
    0x6070f060b031603080a0e13140f0708010b1803070b27030c01030902040f0504060509060c0f0d020306030307050a080405011b0809101106340c06020c01020705070906 73
    0x120020031481c04801c0c01c1c191a40c40c4211489040c1c854540c08001103030b110b9005201e50201386c07409402c03190550002508215041e0100d224280c0d46c2d2800021000380e5401d2141c2048401081000c54034100c0c40082400d5014014100311030070114000c581d4111500840c1092480181a01d86058448603001034942104255404242c1e400000750f0030707010008690820b0f4800500a4120459400019400342214090490b00580d80380103a0014580e68458280628828003000c00c5d24186214411314020000c0e02c1c410f03851500708404110907000c07000f102d410310526100540c49a940c82c00203130441c054000064054007c2d00800000c00c002034004009895090f251444003502c1044400f81039000e00307900810354841004003150130b00d00443d800111140a00d03061010b0940d080243c0c1c01c003c0c00b56580465040c40364220708144020382d814080500d102d265207203440d410154010100305c1c003600090003144e40050f0171a030f006401e4040f030341050742200468004c45c4d0b958442100600039 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 305390827 1250 305389577 305389583
    0x26010602100c031b08100302041b0e01080c0d09080702040f0b0310020406020312101203030f1a300d08040507050f0102030409050c04051809010c02071a031506070f 72
    0x6499040042d0340e02070320030140b000c0c60b100b06035496285001000d450706007010300b5203244c000e2a800000010381d0307640680c26034401000407001c01101103c1c005040a440090034905100c0309100300f14134106900e0541e00c0f00c07840b00001280c22415400c01c01039030700c102d04c000394102d03041c000d10441c000015080740306030701010303401c460320911030318542d200300d00036401504016041003000c10816040400c240b07070450304c240d08840f02c0c69601e50740281f2040e03a01e4001c60109440300601c04c10340c03143d0720411450120704081004050902d00014000c0d103482044c10f650a405e42078264030234801c0c800b130021140f0040d000c842c03258800110181c0200000c54044900d440ba2050208070b604103803424901100c41a0002c508250618441c1800780c00014106c10b0140e1050000003401c0d541c451106582644131102d80e416401c010b81c1a9003584c0c02400c2840075507100c0c0804000f030f1018400c036009203100c0e01c02a2070f01d039241d9440c1c030305200c02102d000c0b83d84400c01044040900c82d0040030700b40250f01c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 305392077 1250 305390827 305390831
    0x4060b03060c03160e13020406090608070c08031303020a05030d090c05121c030f0507030207031d010e04020f090a060801050307060f050307050c010b090c090a05150702012601060210 80
    0xc1c610020301243d210440d1100c00d41e01d80c00003040c26160060740c0500a00d900100000344c2c400b0142c40364400c90308950300c003d00240c03000c88100451904038900d280c000005141c001d0313001c4030b02d4640c8582840060030011203e000d824512040c1442071019030007003580041030b02c0d599070b0f010685c500a0481181c0580d0300400d6039200040d07a1800c182062082d920100207450b08100c80503902400d0109102118107254a842e0b4100d5103165a200c1c0c00d201e50100c0d10016200e1200707003402401c03000590604601c032043c2c40c58000302c1d6a0022000a0004c40884015a07207401c2060100035a00850a0031a00700114500c081410b94200c1d145506943c01501103c0140d6a0340e402102c4950300140b201c40030940800224592510034030040c81000207610000c260b051769480412141041101c0c2c4508148020441e400710b403525a03401300c000d1030121a0007002000c0c402c00c2070365600c0b418070b0007818040e60488141c103048080e201c0305a6104124884c805a41c0e444030040e45450072603000e030311014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 305393327 1250 305392077 305392081
    0xd110406080606030c2103030106051201050f0d11060f0723030301120b071710050111010606020606060304020409140102030415060303050901030e070b0c1b01020607120902060904020304060b0306 86
    0x4100002c400d84545001001000710303103a10710502041e288a0713404030b4052054242d0b0718840c0c03141000118000e048130f644465a070075403090007261690042e04028402c01b2540391000c1c0d83d5489044403408180c000c10a81c07842c4440d500021028410414050b100d24004071303600c4144003203171900071440c1000b1921069690780d40f035600c0c1e46074407090190354000c0e001010f400c004901040310040d030000050070044400003000b240110802c4048458841d140b101c10010310565034010700702c0d0724401c4000c008dc0241e41c100300d1302a4541c2c0c4005c00141c090034001c4001020342d40c954100342c0d180f03504000c42000368007595840754080e50089a090b0b80b00040110b0f9461041d11724403400d0100c0343c0543d00c2c40c0c00c0815080044000e02082020412244034100c4041100312000c801001014404001040800c24512180142140c40b4014905540100d000c0040d4682c2140d441c0d076003103402d140005004401480002c104d40100824907402901c00700402c0104074259000b07166002c1c0032001c0307032025 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 305394577 1250 305393327 305393339
    0x35070605060111060c070201030902090a1a060c0c01030b0a091e05010509010f0b09010306080d05070c0b0309030f0c010603050a032a030e04020a0e0312030403090b190c110d110406 79
    0x2203a2001500c00540c13042d0000744201c01c1000190603a20310524012403654942d0300012480c080641d024681c01c1e40d600e0104085d12041e195440100d8810389000e0300744140f0340220382e00e407045400d105051540311041840d0f2543ca1102c05000741c9004142040110b422380001e420000f203440104410524000010131180703044040b40341201d43c5000860602400d141c8450259084010a64107140c0c4a0001158228050043e0304114515655545c2c5405075401c04c4864080e10390300556140008106000c107540021044541c80101400110b0707039900042c80090050500b640301a1082c0280c000804c2010b50069130f50710b10012140c40d0401401115201d1204d5184400c001800b0400180801c0610305294020717004078041400d1403c1890414030100741083c180000c500c01c180400010801010780000584d0050601001d000c2d00303068003145200c464282d4032011400303000c1c00ca49040b003000803181d1401f0301450083c1104828480c14604a90380d41000c420031031181342030507400700d80 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 305395683 1106 305394577 305394587
    0x90106030218040203061503090a05060108010c030e0c100e15120702060702070303050708031015030f0b10051b0c0306040b01050411090607350706050601 68
    0x1945503403050042e030280500ca6001c1c81503105105004480c0c840c0c40a00804e15080f404035540c0c1e8942c2d000f44c52a0150f03102c3c0041c0140300f064004101c0c0031042d00076200300f1480d928148810590100c3c7c5a40300c0c0e0b107400d0320395000300c01229070501d141e100e4007a114100340003614803402c464a01e03400d100ca9512144280d100f804109050000240c0d04006580d1b00a030140f01504103d811550010070074403c0c10f40181460f18080007181a0f09040040300c801030101d01e1040c1c941e90b00208000e0003801d94100c0003024145004014156400c085000345880c010699841c0d00d0580c040c610783c0318100d100d2403138411501c211482d0440c20780b01004028003a5004e4030345c140c032940c0350008210075500f01241d0380d0040c2c0c0041c44800000e840b2101030700c1185134001e003258141d0328a000220b0b2502c84220b045210020701080c11082170260030700a25400f401840140032aa680b41c0040d58 = true := by decide +kernel

theorem cover : BRFrame.Cov 305215827 305395683 := by
  have h0 := BRFrame.cov_init 305215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 305215827 ≤ n) (h2 : n < 305395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
