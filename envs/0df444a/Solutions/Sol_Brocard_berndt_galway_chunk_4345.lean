-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4345
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:19:16.836142+00:00
-- url     : https://prove2.me/submissions/70861970-7936-417d-a52b-3ea7de1b5fcd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 781294964 ≤ n < 781474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 781296214 1250 781294964 781294967
    0x21303030921050304230a090c08181e160303020a0501050907141309021003020909060402070f0f050f0304171614040e0a0c080a120c1e1110 62
    0x41540141c10700010314121042d80360006014a0040c2e68004004506052070140000f402c0d10300c000c1000117a207500e4002500c540ca440400d14040c12001c1004110380480e100000d04440b002005543e1640b400501c0354510080840c943d0300d201160a1910341080307900107010318295502c15460030801c001100081495401f040340c2d01c400b485200240f20035240d86c00c1603950740c401801030008106d01d0303421620540c41c0c00c44800302c3c01d6402c004086050b00c601e070006818001707003000100c040790300042c41729010300d0401c0310145c2c0441c045504500f42075140e02c4418284424420092003007010f51954404d108040141d0701c5c0b523060000460381e443e51140044082d1b04084501b01909100d85114204151080500c00003a221031a50800c038551488003040083d000c49140030380316006120070800822080d144001c0903001c5003000700031061440c81c02d0410400703540762040402c80b1070004000000c21410744210074500d61860004801d1081c180008065111000310b50b001741022402920103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 781297464 1250 781296214 781296227
    0x1200606011202040501141c06300b060607022d180708040201030f14130311030f1218030313020a080a051218150904063602130303 58
    0x140c03400e030390303200d2407011018054050b400395000e11404120030004042d04240544041c01020061103050b00c1d45240c400b4500701202c841da04103a4a5241d8808003541200e2500341589065081c0078072888c0014698544803001e0a003d0401449101c00290500942d5a50b4100d803012114140c1001d41c541540d409210801c00b242065074001d4120941d030405caa03c0801c2154480d440903280d911041e40c44c1d9004500070f0540345402c011003941d61056241c01d030b031000c40f0070b4800c800d4001d0800c40c0e500a0b05000e04002403d541110055104000341140c0c07549100c02d0b50307150800545181c0480c1c88140858042c148021700a2155100c01310070080040301c07030341941000300e000b602e82e50f187c1603d50007901e0f105d40c0c004001401d07030b6000420a40c900c036080d200401040e000b20140d02070030a69000010443c00f005400b0006692020540309071f01e1030503200e50402815000c109004071000115120360349842c440304841100301c4a001d5181407000398049031701010042902440c1d89481e0716014041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 781298714 1250 781297464 781297471
    0xc2a17010207060510050306130c210506010f06020706050c010f090602090f12030901081b070507090b0405060f010c020a0f09020d05130b0105091803040902090f01022a012006 77
    0x240f5041c030004c584902d8040300c0d075006503030001c0c000d40015035501060f04050905040211641c2b5061040002c07034128110b0036020f002c2d802c1c411624030781c11130304119143c1078040c0c10041d00405d8003d42042901d40008000084882d5401c1454039003c10000081c010070301d500790228110b0410400000700046035000b00124501190400400d6a9100910600d81943c405880caa640708100c0031081d980079048040d84405000d103040d0300344580140021365600422400c840a903c60141489140c00c94040c03420b0002c41075070100898a0000c0024594500c1800100d0500184100e0b131015900e410400d00042c0611512040c1801d660301108402588144000e402c402c0c9040c000c01c5c420b485034504e101255030001415420f80e424642000004003014051110034148220101c0c0440300c2400500010320b01c000c0010303160010031040c8410500a800e0342070440d04401c45488000b4040008103205000d00e214240040c0d9070480140ca981004040454620283c100b001c0c006110000d2220f20 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 781299964 1250 781298714 781298723
    0x181204080115050604120203071814010e1006120b03012c0a020d14070e0a0209100f0c03031e0906050105010314040c03080f0f07050105090705010c2a17010207 70
    0x601001c2c5220301022821500945500403410081085200e08007544408440d0008040e039600968804d0015188460a40640030a030340f40c0a007460380c410030080040c010840c5280b100380914000d81e0b88090f500382c1e800f5100034007505000781c0c0e4140d007103580310640c80741002d0b000300803c0c02d9110101c0c000314001010714044007503070012a00c0441c000300310750918030f81c0a810401d4600640d92503100c40c02560301500c40d544181c402c0000c1c0004000030060140c0341c40d03540180c4d5501310702c081c03107900c500a0242e00c0602481160500078558041c95244500740c25107000100344000c0640c0c04545d60400e9503121015080c1b641750344c184034031680018100d80f000d80b130410105c10410300d0780e46c00c1001100d0182c020340749807104002296032440203201c80541c81c0300c40761802c039040c28a1055604480c03000c0c1d4448c3e43d40e00400800007003c012a4019100c00d00388a004080c4580c0c4e03c40744802151503418011262500340b560342e58482e4000000340c4900140ea00003150a01c0703245000350098041030340d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 781301214 1250 781299964 781299971
    0x11a22080114040c170309040911030a030504090c050301081509070b0a05030f0603060915060a09091a06060f09040b0f0604170105011a04050906150309010c0311120f1812040801 78
    0x205200d00c0d082c0501d0000c545405036003007081080070400200049d810a8584414250030107034181d406200e040010ba1103a140c444d292410b000d034200856440e01500402d012040006001d002e90014003a21002201080041ea644c0e50701465800c0a0701c0f980041a04140441c00340d04517a0414080c61080c800841c02814554980c0101503172008191804c0328070f6000045820b1901d61410006940a0405070a040b9450744e1584240700b103031082030f020f54180498041d0b45821b40c8842501641291003140c000c2e08008039194003e01e03074030840ea00a0300ca1542d1f144d401e1800d0319030040517034130a00000c0405850342e654030200b40c210000c8001c1d0030300035441d00c0f00100d544a0300800700e08141a0071521035040c00e0500301480300e44400131b00a1540070440030440400c00b42450000c61143c141c14002103410140110040c013601c606030040c2c10305000601503004e2405402c0c2c806948030491410303400b40c58507034903180c10070020128091903582c0100c140110f0101510402802104c86020080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 781302464 1250 781301214 781301219
    0x904080702030109210806180f042d0209060109260c0d0c08060c07031e030914030a090f0b0712050f0c010501030c090e07051908010e070e011a22080114040c 69
    0x2020b50300e1103802d1404103023001c0000c14030000d50401e5050381300784102069003207100500c4504418031503e400151441140380c03910411400c0501c00d00d0b421140c2801e040301e045040c504050307009101400090240700b001c003032040c41c0a0003004680390641000d003801c0654065800c1c60407111081f40583c84140c4280400304901401680407640c84035090390340d240305000d486a80c0c0c164191422150002c16841c1c034031a802044d220050844070003040c40045a460b410400094030100c1070b83c2c400b030307850307000c52408102560350042100c19440d03201c0391400c860280d00105982901410b01d0a10169074003095110840300150321960580b4001c002014109a442c01c824080e1900b07841000c2843d0044c0108100d6410080200c10035036113654100d403403064403034a6003030850341c40b440700044a0b84080c03002c110042034400240d0141611140c80c00b41e03c001c1480b000c919200300c104c1e8000c0f085560007440354a00300407489001603d0103000034849090301030b000454016098600b40c41070404c44000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 781303714 1250 781302464 781302469
    0x901050903040e16030e06071e030b010530040c061205090d0c03110318100c020a06080a110a020102030402030111030108121e030c0703120b0904080702030109210806 73
    0x3074078111541074000543c550b6590000c5020024400542001d0544540301c0c0c10780c01d00144080da104003819a21450841c00c0131034000d0842d280e044480081c1032030150003800c903903401811503e010601c2c13040d000c0c10102c0c01405d14013000d014883d00408030500c01c207000c100280d4110040c202c0c0c44130b80e00c07042d0002c2e1040644c02110320a0b44c0090840e84403c08880d5941c0c0114903100004dc041e0520544070290704014074115070210000b0740354100410342d03140061409888501041007580340a195461442d800318070000f9480c040c4205003ca4100001d0b00210650040300072500d15840060301c4240042e006400303500155000c81c440c0d404d1240000c42c510030035095034126105080100100b6400103103060075580040c200c5444901e0114440306401494002507015503038910b078140d621503c41c1401000b6080348ec0d01c5042450038420801c103240d41c2c41240300d4006401c1038002c0d5031280581700190040c9103030100208440c06c3c2c059008000000089180440403107502c44105030703540c0004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 781304964 1250 781303714 781303717
    0x10903090812030708041104061505091206041a0c0405100f031d0627030705060405060112080d0c0509040905030a111515060409140103060608030a021c0203210901050903 75
    0x40b200c0001700110f000402141100303a1079011068013070000982191120841c0d1318184029806801181d4001914022420300032201000c0e040e01c04050000c0741480d59809146050007580e0310400c0c8105000b04040c1c09a9004440040c03030010618201c0d80841e802c042e011300354000c015800b10345884041680171031b03048081e10f50002c088020740016584c58440d09050000070405481040303800b010003038a20420402050f541d8010801003a0074686450414034001d4140c0040c1da5100020740c003030740001d884806071a03544501400105200700d4805080f1624022000f0507680103040081100600c900072000b0302c000f91942e41e6000d0401e03480350b046a42c0705201c3c0c1510740351921030b5000074403800c1480010308101a0041c415441d050b507034542107003a6a401c903449000c0e10024801001040100d01c41d8400801e1110003030750500d100140069119560104001c1621920000304201c040c428800c80d40d2882c44601a801c81c0300e044914100d00d00c0049a03e0702c0035603e040c000c510740440010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 781306214 1250 781304964 781304971
    0x14062a100e0c010c080c01020d0603060f0c0c030c02011d0910060305181b0411030106020606011e0f0f0917070510030b09070302070f0b250e0a050607110301090309081203 75
    0x3141c00900240ca030740c8917181940302541d5a10195400e00407a80381c0f90703a6001d01e134011402020041000504100818220b40c0e07003c5064040c002004d00721390001c0d403c0130f040005182c09080c00e031800b040824030b0aa0380b560008000b0b0b40714810104000340170b80558400e4041d1141947d0800080d030b522018801c1c1c014000d00307080c0e03d41c1e1180307400030300808049099206000024202282ca040040e102040c2b541080e003000e000358000d0010080700e56481060441c0300005007407a0b089241c0424405403c2c81c8076529441c04102510500300342e0079004502c0c1800400c14078001801c0d840c03818980ba910303001c0d1801340c00d12540c1002d8080c221a8401c2c010481000002060164181c07904030050300250300590007164080c1d504016a80824100e0020510400300e08014050310503481004844002100c0d00980a0100c02041c2c07840d50740f500c0d4905029205c4c199209903a50145003002c0511140302d02c2105c0d80340d802c11440c2010140c2c020031601c101c0d02070804030342402125a28101841c0002c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 781307464 1250 781306214 781306217
    0xe07050f1e031015030b0c0405060d0902040e0706030903090905071e021207030309020f1e0d0201030609110a020715120207061806051f14062a100e0c01 67
    0x90450481661140c11400c07105400408840c01c002210284000795501d90b18000300c1003031071520810502c90b04158941c1d0041c040d62000f80f6081c20680003402c40d0092007420300706565a48074000454a50f41d00510b0071740100c0c401c58070415076a00005010b1b11112101301e000401340710001078601034038011107001c0d080a495001002c1c04a45020059400b007030b009100318805c1e0101e809503001d02d00000d18065029580104a241c03240c0144104603401552031801071030300104060740f1030080507a00f1500c1004594020403c4003500048000c1c0800390010302942c1d03c0d2990300d60860070008001c000500da00c0d000c0d21102c40c1c0c0c42c120161244014004e9601181050540e850280d07419802007103406e00c074110001d6404540d0710354402081c10180e007142c40035910400d220722103184d03141d1200c030b06925200301542c450800644440c00303100a035107a4011040032034000a90100030611010014030b520803052845080510680c2d18298846290006132510600d840d0040020400c140104c106 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 781308714 1250 781307464 781307479
    0x309180a1d030d0e0a1703010e0c0903060c0d06050a1401030c1704020907050f0c070303020118020a09050a0212090c041808030615040528050603060a180b040c030e07050f 75
    0x394210a010300740383e86100084e0701a00002c00002010b031403400d00d4000b01e004400e901c944c10040207903425000170302040c006600a21252100b40d500181c41076200c0d4002030001d881e80d83c1e881a02c0040e00703071074000c1c40d804180d50002140b2458107a0f060342418000740da007032154440c0c0141c10358142c0049100c901000c50900f00107809410700001141d000000c0f07160080c03400a001d070040102e82c200b103928403115004105c041091540c240100701c1c0b0303001c07502160800b00c1095400130721a004c80784140007490b6112b900152905180c1c5d410f4544042004010361100c0c80d02d103081c0d5854880c81445540314500c0c01002000c14890510001101a4042c00861458685104100c000c1581c1602d00c004050204008034250f1100b031034095405840049800010581222803d2010000e8120320300a10341882005030383c4e5640301c0c0c2c41046420103c0f02c100e07100640c030142c0000d0802c004203039030454100502d1a4903164550300005061808100342ea200f1502c1d4000c0012000c03001c10b01036804440b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 781309964 1250 781308714 781308727
    0x7032304060e031504051e030d02070506040c051e1318050a1a0106050403020f0a090c0c020301140c03040f0515040c140103060308030a021612030e0610080d0e030309180a1d03 77
    0x40c8a647c600012030f00f0101e81c02c0c00424408407040c0c0e0320082d0110b030107401c02010300007044841c0c0d5000018180c100c0381010802c0c00c5e10401c040c440020403030284102e40d20350291282780d03400d9000b401da1040400d54504101a2420700c656120105401240c0084404c41c1c54fc9072003018015250585490303540e0646058510b800b003041c1d501d0070b215440d90004450a000450880038031552503100300030b8513560001101ca004040c21942c610b25500e07100e015040400c8618143e40701200e1348680d102d50302e40c1c0c03401c2035400c000340742009080c50b410f0100340040c02e120903c20760700c1c0410102c0b91240140c0200450f450011003e407000da200080080780c003400402c00c25039041e0080c01d603c0010b54030502403114507480c0c992011118800980100e59200b480c00301c0d0240900042d03034000d4545800e0000c4038903155400382e6907c070216084003000017034900ca034800d540a10480d440030000500c08200700c4000760122502c0304080e61100074062518840b0706894940c0060f0000c00720302c03140503609110 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 781311214 1250 781309964 781309993
    0x906041d03031017011832100b180115051902031905090906120c0307150e0913030302030a0b060c0c090603160b030a06121104050609010302030307032304060e03150405 74
    0x800c100c1c85446541c02d100100259000001f03030011000d1844001d081e00c90b0941c00b06801c0700c452a03e414019442e04c9041038904130b080c8602ea04540b1030520a26070f82c6010350382240d0300c2c001c104003860442800f0320040c4a2070303030010251075420502100d01c4444070300302138244c030307248200101c140c1c1007865440040d070146890380101044d101c0000035a039003071100d040060b04008580d04041c48807400300b001541070607800381001801240a4550b40020b00300305940d50b84880100350000c1c1007680000c00192a03601c0c1d600709810f03184020300384a882e0030080601c562a165800d040f140255500f0300003c41c0ca14001941103000c80003c180b13089031906000c1c04030309036407006002c242246e488110004980880b6104032101c1c0b03000c0c4844040d035000d618100026a800034203040d104a01180040c0090303a00841183c030025814184840840c3c4c4481d0702c0c1c100080d0518204240c40c00200740000c1d2a0f40190150050a5044041d141e40303d84002c94528000d5003030b0707800b600d541d01010b214039890 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 781312464 1250 781311214 781311233
    0x3070f06080612070801060e1e0603070e040f020a08030901020f0c0a0314190b040b0c04030305030606030a06030209010b0a02010f2a0c2306150906041d030310170118 73
    0x107a0103c010307521250389510040d030a44400350b01c4000c0030000c020030001c090400408071185605c051540e100b05050190010b540c0e86014020132003080702c0c3d60045410004201c603160482c5601400030041c459864032031507283c1c0c0040501c40e01600408081900100003c140030746035075002030075010440d065440d483c0214011140c101200d20860a2007075030220704441c12094107100c1c44084907103141600e8030141107003018103005900101440f01b440065000b0080e2503004a017074a40342c1d1241e0315104a0070190015074000303504004081c0010501c030103608003d011ba024150000d0050011003001441101c895401c20f0114045d402c02d94010320990034542d240c4802d031490324600c001202d4817664035040181400110300040b08120201c0c001d404d101d0f00780e1003108038070340280941e001e2000c01d03e0104020513840c031444d91004c151000c2c2d1004a80601e10a400d00c2c00c032500c074942100e0358591100103000383c210005034407080000e454814010b88202c1a4a0310884140d131083e903175000c040c0d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 781313714 1250 781312464 781312489
    0x3080708091903051308030304030f0503070801030209040203010b04050a0b180c040603020a050c03130501080106020d0801031122050702010b0d031d0a030623060a030b0f070c14070503070f060806 86
    0x100002001010b110202c00901400070707046c0704002d144d0384d007064a005880011414070703840034040203104203d4080c0d0001d02c00ea044a8041d186482e255407540300081c01008107640c1c1c9580030b86004280000410180e2100c480a0780503101c62074501280d1841e80000b0740d003212542003c4504020920145110750007525100300141055424486185406802c5402146400c052234107850310822240da4015015401009540050300c00c0005c0d40000600380d11050002402c220b102400c00d002d10b484a020020442a280011144d1001d501c80c04402600302550302800641c00c00d0040c07002c40c1f0306401c0c0f64125aa040d21014000c9564561403c1081ca150210355804080c060380000403074100e008032400b002070362030340481440081c22526855078004d440399000b284030400030300026584151954012401128500950755210307411190f294180f0002003c41401c4241e000e10300c9000540002a0b500440030f540380145ca03240a10850a410320a2100040b00784000c0343c040e041c0042075022 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 781314964 1250 781313714 781313717
    0x1080a02090f06130f080307020405010b030f07030b1f110c0109080a0303090c150f0207061b0b041704080f070b03190e0708061e090c101b1505010303080708091903 72
    0x18440c2d1303940800421005d240d20039207a5820004813142186001c1c411a40940480d007045415814200c0000401c40c00c014400014966141012800b654030002c41d1b10030000d80252031010b4a009403402030402508540b2440713188030f1805034210543c0142181e00940b8002c9004000c1403145031401c6001c0d06d41050161104002070b000850020150581c103078101d0700d50b4982c041c6041d040200285018ac9c2a800340040021a400440d441030100300c500450300e420018148183d2142e0400c51004640d1182264a112001400003404c0f20f01040308249403a6410650b8445039452091450387e00c41142c0c007000b07081c030200244100320007651040d8070050340c603000c4410032034855030142d18005054603220440e40c18a1032601040c072001c07120591002d80c207400740c03484485000200d80c11408400b200014020340051316a4583c902000c01c1400c03a0300901051201950b001c41d0300c009042c01e00040d0700250806c0006011140683c40d440e0284400300d004000a011001441a0045031a03008a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 781316214 1250 781314964 781314997
    0x5121602220c03020a020d0201110306060a050c0f0f0d140d050403020309031b150f0a0f11030712080a05060a0e0c07020a030c260303061c0f1101080a02090f06 70
    0x110390800701e1040740d204210340d07100140d5890f0300130720103440d255402c5090821a07050240740c01d0b40c40201001c1d42d0700b0010540c4d400752984d90820094070507010302441c0e81d0291040800703000160100045500c45090320000b40c6000004814003190451884501e42550001c208100070250300c065101175440381c080d2041d2404c140b5041c0020f4109030205000c501d690784203807802a42e42c902000c2d00e4146556070503286140c40750b5100380c0492401000050310a1004945030001d20502483c41544500c440780c043c0c130742d14141071070700c910901f1b90741c184200011440e100240b1021018802e003400b40000405080b4036511304400b0001003d1300400b03d980040c0d0a0282900507216080c515015601c40c103510300d0018103004100800100010898054000e00584003a5a100c08130441740c102c40140c80c00850050f1030400540051104400104006180a0124103002031040c080c5a104001daa83c03690036107030304200f04240e0280003105a03000b0961000b940710b81c6000c90060003842d0a040108 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 781317464 1250 781316214 781316269
    0x4030f0215160507050103021c0207031b03090f171b012f060c03060a1505070c06030506030d02010608070b070213090b180712030c05010609051305121602 68
    0x62080e000b0300c9403600e46900e40501607040000c18060400078040a1030214100008003100325845c56030424074022690380000c20030141881800720500040c00740e00340a07100040c600c2c00524038405442001100d550303019022880010220548480c82c1e90701009010009020010b01c203031440d14041c05052180c9242d56000045004409800386041002e01c85500982076442ca8200100204041c150640c2082005869958803410038117481000c20107000c1d40c07652030f909681d03502c90600041c1003d141510f0005009a0640105114200541c00e444131103050724016802e07201c0d80c0c00f500015401c400e6044c0400d18a0f030000c1c0ca10103000400c0255840c40000c8000102c41e80408140c480506403401c008180755155188040d0110010082100614040c030301c01c100f484561000b010000203000010500000350004400b4100003a42002030341000d5007103400041e25100101d07001c0c05240300361843c981c5805c00f61000e180d03003980381c07000c5428242e00300042d04844080420f08041c041440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 781318714 1250 781317464 781317499
    0x18010c020304140d170a03091506031110021209040917120c04051e040f0510061b0506131a07090608280e010e0f0616050c0304030f02 59
    0x10a00441a40d03005196501c3c00d05101c440000503480e03803140500315034441e030030000744110b03070703101003004040904c944482c0c85c000304401804000501414012100402001c031090a902030000c0b02e124540e145584210b61003406844600284004090f8000d5001000b11007003100003880802e00c000c1000481c0c0d00d02c0d03550030307a00041080341c8103041030300400c0c9843c42c81c0c500300d03406810039100b00420741810318040015000340d9a20700000841103a5002069144e01e8542103506000d03580c0c0c2c000d100924018106045140607803203000c0004204482c0c0c1a1811002000880c01c1900304010385080e540d800710390054848896000ca840c00c040c504140442200c0c851240d0150480343d54680c0d0840c80d200004019040c003400101d100f61040d060745514521070643e0441d0608200c1011451703640002c48140100103000c0e1449440c0681c0c10720004090002c10107034450000445221000307010400c0448140c00b03040d00801a0380d204100a201144030070142d80681440100116031a54002c0030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 781319964 1250 781318714 781318721
    0x1a01030218150c01110c0d0f0302040315091e0f12090803030109021c060b09190b07050309040c08070f0e0d0c09020307030b1e13090f05030315091506031801 69
    0x10034942000e000c078008800b450f0030701072000c0f21882c6a041c5401d250108850350748807031040f001d82c400d02902c01000f221f4a8080d4040c8c4005640100c40744d00c1c0200501480005400f0008040b00d2801000f50505149102c441800164030b41240c601005030020782d0b9544c9122115840c50014031141080010b1060000c00086019000b40380025880310a004d81c10001d51000c400e000030350a00307103041846040c51010944080310740803074031a00102c04210940c0f4000010303400000f031650703000401c0410f0050000042c08004000d070b0b010050030019540840319114156a40381c001101106421104c9104540d41c007400800205620100700490751000c03494400b66002c104d03503d0b004420050a1a050302c10340102000c161004115029109070a250204045d200c90307100e0b0b00d404d80d940d0005200d81d4010040654001c600e14008902c03030601680d241c2045400c003101c400c2866126546040c107001c0d4500170000440b41c40005000c2c207081110300e42009240b021444d402c102c04081403d800d00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 781321214 1250 781319964 781319989
    0x504031407030506180105060907270302030102180a050402090f060a02030d0c0f08060108010e0c250b0118020405060301050103020d0e16080d080f04110109030f061b02011a01030218 80
    0xc88500962507454402e420b56034001e040309c0c46100d50404104111780c1080e01c4520108071704580c00052080d010098407007002d1600060b41561010403c1501e183c02c0a07650035040c002120340c042826910b00810050744107150520b900144088150241c6040c5003015010442040c016282400d9500b120481103511400030742c0005a1040030042c0d150340c102d9551a081002032a05d0243d560420020261803000a88a005040b0303000070707106915091840317010308034022140000014485030801000988080c050416080610103804200800d45e108813011030300040c14490940e0f00e000700540094016010381140643c540313040c0e40d4540400d00902c0c40c07012a8a103100070050800750b141e441c1006081c3d10506000c43e103000e2000d4461a50f0300c00e940544c0c0041c4140000320f2500040303403502c907182e00040640042d130003031808100584e0400042d551455948240d407514400c0101c3c20388001060400084912030b5019020b94803980043c01403840010f1442a00c00e070305004a5055540350 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 781322464 1250 781321214 781321231
    0x1a060a1b0507060f020d1e05090d08041401110a06231003060b04020406090302060702030f3703050a0c110d0602090a062604030e22050a05070504031407030506 70
    0xc0c0001d01c00d0580240014030004c50b20300c0180000c0660880c05444011180031a0b80100d0350a50b102e0452071240080322503090000e0611506072017145080c0d042a00a40030781c00300c2caa007010320182d85501c59000c500343c80f0081c40c000c0c40b809906441d0b800040018035010281e8292003c40f1107a80b00d010b40219000c1c80f2124400500b0600d0b50900a0440f0b080360020343c0f0603801000100b202e5503001040300d0a072a01102d4040d42c41c405880040d241801810802c200c07070051091001a913034803500c5100b0300100c0300ca01c0d124521040c080e8814030514606000340494401d01050800f1840b90a010b03244a10402d000140c0035100400a5072100301c03039100f00c65068002404403841c0c1001c2204400620070303420700e104860442c0d00e14000c0345420f00c1d40623061119110008061521402c07200c40204170181010640c0460340d103e04c00c4000381296400c032028280004902480c010380305140c4200b0a0355039007420542035a030355441c81440788107075902c00e202d4141d001c000705a052000d54011b020a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 781323714 1250 781322464 781322473
    0x30f150a0b0c15150103050a0b102a0c06051e04231801030b190606090e340302090603010b12010b040312080612060115020705041a060a1b05 62
    0xb40702006260810380341454100c080340005011039000e40200c8100c1001003403c0114156540c030f01a0030080400300065603205001480c62000740341c0250020700007045c40204140c00c40d01c1c0c180c18000100d004035008110940442040050610440142c1244c081301c0c140440e0300028501c01c4981c6400c66004200782c8483d40c1c98690814610a180c4000c1c0601070f00d07201031a900707039080004038090500c07002d820344c000c0200184668480c4810044c03050b0512000300407454540c2d400a004490b00d002e001d81c11001280800d100c4020500410b00704a081400d030849042c1d0a0841582d066803034003c2e4040c15000c2c070101030f0b950384c1c4801039400380c01502b2121f0f4a840c1c011900122a03a8180d10180c0025000c00003400492119081d114246000b8200180d40307480d601c01248011420300c3c58240a07006080020541c080150a105403600c070340c0d82200c900c180c59108202c102c2c1c0d07029109115801d129100e103189410803d016004440180c00c09601c007580d5111150f503a401c0e5107408891a030070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 781324964 1250 781323714 781323727
    0x1e230312040f0210110c0f0a12021804150b0319030f090321090f030804090b130207060902010809390918010609090f200d0501020903070b0f030f150a0b 67
    0x6c1103125604401214440b40042e50000810030188031030140c14084003403000101d003503481d200360202c83d002e20907608117414a0f0504000c0001000040804c0e031140c24240341009500d0001809040b10139003031032412110300c03555010340d0003d0800b10002c09009414000001203000036445021071001d4030500903c3c031341450700052001c616900816500c1003222400d1010401c1d080c00ea034144e40542c080011f102e691440012000c00e403100216442500002d920800c0000c0d80c6c1110000f54401e8035070400580700c9030a40c907207541c08004645901c04a440c4000413140d021070060750013650120345800d100d91303502c01007640400101da82164030110032010744c0c0120002d2290f074004201182c010007130104991788507981000c40d044081c000c441600041014045035130620940f4001c004e0035440c1c40d800a01e8414043c0d0065400e0074828003d01c01c0009a0002c03070300c1156520a11012010300d5691140c1c20f441c000030016146082d03501c400780c0c907140e082c0c0703485040702c000c0c000842c0e12588552 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 781326214 1250 781324964 781324997
    0xc06090c0411121510030902040b0402091305130203011103090f12090d0501060b04142e0c0525090b0109060504051c1e230312040f0210 60
    0x104495440c500552500c10042c1c00c00e10311506031803580c414a4410728041e00d84071a186903071a001d640d0140d00402c2d4080140ea0650140d2211140c14070039a0244904100002000200c0c000c80080d242c000e80b82003020760140a0a0b8070055101d03116071450244031029801023402c6880c20010038014032000420b20842031401c01c108030341308100c04010180042e20f0b13900410140940d40c1e1650044402c10181010408207420050260484801d01c03a110b0f1707030700c0c0c12084400b1030354200345000f10f01d41100c2e040c1003c0301c01c000e403d011014840c14030000c0c0e0310701340440712110240c805a400d4040c100030040c1f5403001414403501d00719811041f6450394203100f42803040700c1480b903c0030b06012103440108483e81d0484282c4040f0390703044541603094003049540a031a070040c124000c1c8180010a610181091410203011a0340d0040c0b80c0981c0280484d510003a00340700701c400c00e07022a40144044498031840c40c200e945c2c814824810909010402d9020031034441138070003c0c00125a0094003442d104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 781327464 1250 781326214 781326223
    0xc170a02120703030e15070501052a03010b18031608010510081c11072c130b040602091807020703020f0a0315020a0c080703081006091d1504020c0609 66
    0x780001000303400300600c1e5603400f03020244402943e6016030385656801d5114800d000c00e45e4660b070b030018020b01c00744c50315481d9240088002c649a407803004031021346042840c90101601d041e1010780c11511b00d080244900c40004803645681036501d803180780740102010700700600d200c0007000c000300042254103110007818124002600412540d500030b02042c00410b294444580a5460703a06001c030403007006214140c1030040399000b50b500200c40c000065581c541d40d00101002000f2100b0b40b0085842c2c41c1e030064100134110310007a040c0e00070040424089131656000305012000105199252080400c802c42000422900da03405601300e5079080066003002805500c1200b02111280c28950460307884042c01c1032244000700405501240403280c81d4082c01c41441079640004040e52164000c1c54010001c10003255441c81c04904030100240050040c2c00d00010780307004122103000300b1700d0034000f40d591042c0104035502c03000c0951012009038484c0c2c070042440d00d0a41005d05000e1030a1610b69191 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 781328714 1250 781327464 781327489
    0xb0a050702010e0f0d030c020303091009050411040b032e030f050c09090a081e070b013210021515030c060c150705070506070509010305160f05070c170a02 68
    0xd0002c05907040c02c2175440303c0315120001c0d810f01f400a10f41c20180080f80c918000c5001850300000200c21080c0d0b41d58020318854103c1d18101c80034015120106501b0391a80030300c1c401c90103482c00910101340202013014958400d50303404076480ac8600080c02c0c003509003140300c0d841919201c1c00d441422003846000d10108102900a507188011400c00c5a42c0680d9040d0114000d80000c0c404681042c070b202140090380700359184ac1034420349409560401c10101d00081c07080c1942c0f13207800940d8540b1406000d03180114980103400344a9002c45900500600c4040c521402086008040603041d4040a451441e03000e00200da1000c00412000e10625140400d0710410501c80c480a10403240c10380400a406080941214100c0e000c503192500240c07118010074900030310b207025020412180617030010182c5080034003664180815203403002e2104054041130401d5000810315140c05034514042d10003040824800d40ba007686107a925810f518029826041044403034011084907010752401c00c034039620 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 781329964 1250 781328714 781328719
    0x501090b1206010e13050f061f0f08030316050d09080a02010605010e0a15020a060e0c090115020d0f050f040305070303030501050a0b04090c0c15060e1609090b0301060b0a050702010e 80
    0x10703d505040349510484d9004004034044060305150b41c08111090010030300003130980040740d03480d05104045107003110842c000200d440c0c40241c000601044d4002038102100c01e004040e51071358071100d147c8038042c10001401800c2c0315080240601094282c885c0100f0f15016840b0386494000381c01d8000c2c20348070360343d002c0b504004281414641640c0c50210000c120340e83d6002000150765002d6041e414a002c07004054001c52400b4261260504d01151083d000b6400f02c2c0c040000c1d03a255045551124141c215110060b4408420104014000e507640580d0010074100281041407208144645a10540040b50b0680001c042001016018064a4090a4215411884203040400c14501030180c0d10460b44030740d850b10502020540910800c480c60360304600803906001d111513104004d400144100035203003500714001502041d00c0052100040450f90b1480c1800e454512150050b01d40c0341c0c41607034195a5800c00091844011000704400b03800354840d15101d22003400050701e004d2411202a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 781331214 1250 781329964 781329973
    0xf0d030c050f120405040c23040f0b03040305030f040c150908011116030e040f050a0e0c040c021e15070f1107030b04030507030c0204050a02180607240f0501090b12 72
    0x1601183c1e1501560290341e8141c4001496007422442225003009400000806045000103c1141807003a8010805e698400c800301000d10360701c015181e040d11048401600050342030002c1050800003200e00d0390014010344805140ca0b880b203071681101000540c11034042407200c0401c0000c51004c2c040c11f240c06150503501070900743c048404000d441d08404005082100100d914140c66480e81e00112025408035410081c52820400c9940100003049000d4410721400584c0780061900d400303060f1044500c2d90191010150030009000710040400c151159030041c010400020050450150310440240e9500d2500030041003005d0b085c41d080c00601016500005014408183c03205079554000c2c1c1e05207000d690751482802c00300c994240e6080025070050506061000c9002e00750085e050b00915200c41c0078500244030f080140c00c2c480c00100030000400f004903030b41036124006100d00a02c161040105940c0110100c1c641203c0d026009100800d03a141c014800a003412072140b10040c0e0307c00d0060 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 781332464 1250 781331214 781331233
    0x2011404030e2110020903061b09130b0405090705011d01020616020f070311030723090618040f0c0b130e0a020f040f0608090304120f020f0d030c050f 66
    0xa084164011455000ea102c81e4090480010340000f010391400c802029602c0d42d5662400c40300c0607500500c0664402e1140c100421b5207040c0780003101c42091484181e60b403424070038031300384004106201d1000d4500c2ea07841c1d6004569031140d01446104d140e091000d09041400e000000d050070740c00c0440041c2c0c00c02010054955660001091500b0070344188040042e4087c0004c22481d2a0407424481128014800c000041051014441040ea1011002d50b00c10503102d00e02c401098521402956540001765036900709811300c514600c0e0000c2c0d000d07245144081245500702c00e84c41c410b440481d44014500d243c1c40a001d200384450700980601c0000c80e18240441c8041d5a541049014040c02c0c01d201e000414549070241d4112010710388030024403038881c1e566106051080c1c910307204041c04100f07048001503c2c424040120b805075a02001080da0f040e003180c6440400100d0884101d0f0400f013500954080c03540d550000040c00c501c00d649220590807240f80440c03d140c00c00341d080708180d2000004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 781333714 1250 781332464 781332467
    0xb070c060c05061504090f05010c030e030c150a0b060313111815011b150b0103020a020613080409020c1e01020c0d050d0207060203010b03160504050a0909020d060608010207030201140403 82
    0x365008090301500340c40b61300c481e0000500900c0610401049404020f01c00000c00074190000841002c40740ca0800003840c2032940c1a880340315102602c0340c0c0d60401c002c1d001500002882007504003074468000202030115002103200e0742d2003680c032060315071541d489450403c410840c40d490400301c1540d0030034644070890081d00e03c0e49005003100c00079200e002250039071039228002520a801001c200b07000b8a003042d0601241018628440e07002007800c0c10011181540240201d80241910342e00030040c13a911080c81c0346030310300101001c440c007030010000080c8d9254180051f20601c101803005c2c0c070482c1850f000210342445440400000d0740d0061001c2540c40c84041035031580400e060418655484015003810b0080c4984040102124404170000c00c415201381e02444c820042000c00100603503d4101c00d403002d01031880b030581d02408181050080e582c00d42c1141c40380d5840a440c03002600440d80c0c9050a4406c95089210260760200d030781428540d090040595942021800d1441e03820720b500c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 781334964 1250 781333714 781333723
    0x309090414010e0d0509030f031207112a040c030912030c05090d0f0b0f0c0f2a0610140a06140c01050f181606030c0c060203010b070c060c05 62
    0x5050722900c880d0080000100390000c001c0048507800383d50401c0030704403026000740c01294070107000f03114181d2116010b40e4004101c607e0380341170019560050703803a190100d41948602a0510360f0b13001312010342c05501c65410380418415000d00143c40b00c43c0c59081800102c418004801e020942007840b4840400c3c80a80d10500615643c074000c2030700300c00034206903442d201d07501c031594110746600340d4401030140f542074107042c891040309900026283c80c80c076000c83c85800d448a0104960130403141a619480000501722602603400c450f900b003000c9406e01840c849140e02881007500322a0400040d40903000032440642805034801090140c400d000c03600d0125240111801d010400146406002079013050f21041c0d00160001d1280c0e20b03001300a45440d174000c2d50a4040142200c5144a003004042040d00c55440c1580c0305541c9145000400c40207410410307036501c18070003404c030b202001c10004e000a50190803000ea10540d20001850300c00061181644a2401c0119a00003a800240c001c42c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 781336214 1250 781334964 781334971
    0x71b0305011e18150207080f04030507080f19020a05040207140c0301020c0309060a0e10030903021203010e151f0905130203220203030d0f150f08150a0209030a150b0102030909 77
    0x2030300303030010f00444c84800c024428280090650b180c0800d1800c454240080240103803072164040e907101c039a40303103180c954807400138860a0594108400c1110803c0d10480082a21030008213803190741da558401180899010030002c1d503200f060403c480e04801130411150f015000e041d4000c5203000ca1080c1c50715100c0c080c942100d03100d0f01d4002000c240161280d0040c2c4010389004090012072825140c02400a102c554811809800b8041c001000c01c0d40310000e6a0403075520b0b40b0601599620500f061988035440010554069503005003042c142a0310440d06500d284143c8a0041c030a0400e4208042203a0041e41000a40c1c0100200024000520b80301c0c829030018614100010002d03100203415030180e50f02c0118051724029140b001e1040a0700020011444a0208071100c3c0c4c41381c0500b5919090b0380100c207990340c000002c00030721000c0440066800101c4000060403c0303041d0740041c0c20060b070440c080c1c40f42031b0a002036594000c030a00c0f408518000900065150190b0750011035103005d4000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 781337464 1250 781336214 781336223
    0xb0a0e0109052403270303040b060a0e01030f0213051f0b04030309180e0a23071a130f060e01020708010c081b0c060c1305030303040f0602071b0305011e18 68
    0x440400e03444550445c1d649912910040c0c0030312007004e40c00c0090b550390070881e8260f401850900c081080ca043c200314100035941246d030124416030030750b15032520080808404a0304201c540c409944455000c0c450140180380c1d6a41c8102c0c40f13802c44603040030715a055041039038402010402000003e070480b0140f0201d44440c0b40c0c2210b031840140c92203004105030400200b640c000d084034407080180041641d55590544020000f0000c10074001a91b11001c5000b010300d9080282e82d0894000e21b001d01404109512801011015460381800021610542d0000e40450040140d0300d48540e0140818070150404000803c030f82c50254400418504c40030300b040c84001043c01011601070b0f0b5400c211515810348400320392050400c8000e20000354000325481c5a82428080041050319000c02241c0c0140d801420f805640e89075602c1d460003d600080e0200d8040300d2200c00d0030075400482d1400741c0110301413800041e1828420a0302c02c10780710000600d50060f0700d0300d0141c1c041d0440c1c803911481d170141c10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 781338714 1250 781337464 781337467
    0x10c0e18041b080105160e030c1c020409050307050f030a0f0818030a020f011d0c090916031410050105090a150b0d06031403310b0a0e01090524 63
    0x354203000c401d50300000b250b82100300d55940c0100380c11105410090240204598207800d08503884001c80303d03464601c0f07444d1b81c190401802c111042c504494170b22200a00003862a030720aa6940c000380c121a441e0300100c416400c003080103010f104c0180b101c3e52450000e0390213140b03810b240c090004c1000402400315030a00200388042034807618006003082c0b24100a00c00c4035915081d042011b0760329400303100320550660a14440c42484510120040c455200d450001c0c0011045d070f40c108140c036030300101016aa0710a0380000540d080220f91a90020b5000d40d104440d119061307405139040080230160103c4950405004200c07940310742810541c440da1941e0700190402845410041100d9140c0c4420b5030550302040180b546a0150303c4901140c0c801e040301c8e00300c00680e0000603103074000d04004804031113500710101c1e5059440c1c428105620040f59500360010348540c3d0301c00b4144c002440410010324080c49405e280c0d60000079250151404941d448a58404818215010366264100c0e000c403120 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 781339964 1250 781338714 781338721
    0xf0e120a260d1e0603060b0907020f10020706230a0b040c050d051515092404120c030c0906080d022d0111040603050708010605090a051203070b0414010c0e18 69
    0x2e4000d00740720303c0c5400501c28400b1a5990600c0701c05408440f119600c01c5c070307821000c1042c09000042002d00b1003c0da4016080010120074040d00a400258041c1c81c912f0b2144501d010010003c00810150141c8031a840c9060a19412040840b401070b072100380218a001810301000d5045825107444011040c00495a655501c09580249044200254020101007086003a1141e442c1c040c040c080b0040d00c1c0c0c4c580b0030b5100d0840e400c000840c0b05425282d91003c010520140840700070302202c41e40030f40d03000c40b6815500d968044000100b6406410040e66501042c00442014040000b003642c05100900890700c000e83d0140460008108443d0700444002c50954800420b400121110048070021030311903903907003c050098102240c2c6140058504c01c000704846000b002514114000034284143e103d0500e81480050003003014007004500c001e210203400107411030a2148075600c40c140702c824001c8a80d0701103096450f0700b400e410900204042d560440d0b01e40398003150b407003040c001c00d1011986 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 781341214 1250 781339964 781339991
    0x50f090a0e011104080c01080609040b13200f040c020d081308072907080103030c1e0303090b0604091e060608060403090602070e160f0e120a260d 64
    0x50301540701e403029400c01409804a00e4603001030700c11107103007400303a6001d00210401100d4201c0100c80113903100c0a400c02190110300c04001070340d480000500341342903020301c544468018503400d81e80019070240ea511b0808141c10411200c0003101e90689051110301103219019403240601050101003140b50400203580e41c0390340d49441d41160f00481200e5403803141c0d042480030090000d584420160580c00e03500704404003460748500c940300c40c2e85c81d90141e0b425035030119848065180150346a41d10841d402c0744c01141180394544da58841e44002134240f840d45030840d00c070030b00104a50301c540d1409a104c80401d090304031f0915102179030301044800002501d0064001c1003030b40c011104038800c540802041507044a01c1da020f88040d90200c40e080c81ea100903500c3e01c1d0300101c50400d80101580240f0306094040c0d42c008000c550320b420018800d4011401045d001c039803c0080040c29803081e0045402e2082d000080400d1a6100b0000007000c1c0048070b042d0b0151086803014207116554100701c0d007a10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 781342464 1250 781341214 781341221
    0x1011030f06060910052203030f0e0105210901060f06090b09031204030c18050124020109050f010207030908030a1407030203040906030b16080f01061d04140f10050f090a 74
    0x2014000c100074524a405030004090b6001884264100e15a00301c0d400010b400003206c850032654903540324000580600d42c1105c0c071010040225062213414807181d070400c0d008903013030403030341c2e03502a1020200e1030301008050035070f15207510080070010200320034040303180d001c007000702520f60400c4481c0d9a66040004646003003041840340c0e06c24040458080100310100d2603090890340e03c04841204800e813040c4010403120284a800c14801c21814a1052600120554141040c09000000d2045010340340e80e07084c42041401e075140c80c4d44c001070400425400000300c402602c7c03004001d509055070400061301c90710f00102c00302c110208c0400e4000c10103100300304030f401503d202c0130184800c43c0d03a440d000c00e20210075154051500d05080096000a10034294a4451000c007240b02005920b4101c0035260b4240b115548010401805c06041181d240c9000d11281000c402609802d43c3c50420f0806c18204406808010020010f0104201c1c0da52809280c088620048a044100751140180030006 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 781343714 1250 781342464 781342477
    0x9110c242e06080402031002120411040207021305270d200106180c020312060405070302070f110405010b07080d02130305160807050609030316080f0316021011030f0606 74
    0x1d441506002103081580040b0950160748294200c1c0c000c0b44950010000364002c2e15021070a00f008640040c001c1104a00c100c5642140688011314000315600072448080c2c403403440541d102d854905000102c410004501003103040440150000100e0128481d1504070b0891040f00700040b00e15620a07113105600100c40c40070410008101e150350b103c00c5a805c140e074544070a001c3c0f61600078040605400441221088407000316503a12503070302c0c0300800004000c094000010164240140300010b4420030b006950381340250600e244c120301c1d45003044141c0b20141c10559404ca8140001c1d030001710b041d02525400012000c002d030300c5059602c4035000020065001800620680ea8000d041e03007013803010641981c050300c0540f0b249607166003d0112910900790440d07059401000078600c00070a1041c00c80403d407103600a01e1a003890300307404107000c0d00241c2e441c1942c514841c6080407030940400c8010318a841080061040d4541c1100340c0c0000d002c0240140b10b0b0080307a000145869075548100c850 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 781344964 1250 781343714 781343791
    0x21b040b1207060f0906020a141f05010e160815010216091a0604080d032004030507080708120306010e010c080c030909090106030804150909110c24 65
    0x2081d0900035503950b201548102c3d0b02050700400341c01d403080e2140c607121095039034980003042e102415a881d1411507030ba40036640140d02a0074031108007003240c0e8118103801047c194010506505080c07a1440c049005072a20301e00402c03003040c0101442c0c00a0055a20800c202d00b000003002c0c00c240141d00f800e04dd025003d0300e20200f8240800d803000c2c00d42c480480c49d0324213031170120055450402c3c02024400e5000d0800036600548881965600c00d0b041078100003180400308814400c5943c0c8010345030020341084a42c0c1c0c00c01c00041c42500803c100c40002440160000c160f0500002105003640c4406807445041190003003ca0095074000c01d0302c4921a984850540d5450420300403041d00d9402900b811403186071014080f4224610501421040d01c4d04984d929207400d1038051a01e043c41810520b01003404009200020781e0280c80c46880310b40e4288003c01d9a0b0707602082980c81c10200382c200304841c0014849040c40c48103095080c1c544d07000c1d900c69100304c1c0c020214003e039030740344401a15030302 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 781346214 1250 781344964 781344979
    0x4061b08070203060f090c040b030705120106050a030f03110a17030903120a0203070e03060103122001060b04060e2409210705010e01080708070e0a170718060303021b040b 75
    0x107031811600007040e200300a200c09440500d11f0306020001a25941b80c1100c3d0305901120013072020749090b442c062448003941d0000611580e403000800c6540c8903503403040e039055941c1e514030404d0503088440c44d080306580001130071004d605039554084800c10000c1d01e2003a50404000682c0d020b200f00700700e4400f61510307403441615240c50900c5078003941c8111480c1d000220301c002070f002142070000e1084c0c180e87d4003080701010000c001ba4200c4500a80c0400003407007040000e0a560320007001c1c4030342c0c0040c1980c1680e0641e141e00700b00019050352128541d081c020940340c12243e000e92809603d0704660603140c1440741c0e0329036080000828140960705804550766184260601600000038008110b6400ba01c903d9261003901e0010365005400301c4c0d4140118140d940091407080c4200105992950010181a209510340c5514034907900c060282907070581c03240200307102c2c0c030185c404c03104560805030708107114250541c1d40081d01d40744a18000c0004605502c2c0300c0401c0d585070b4020140c000390282540c0c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 781347464 1250 781346214 781346221
    0x6090206030f060a14090a0203040615030804060e0a03050c09070509040e1518030a0309080403123f050c0403061506181409090709151a04061b0807020306 68
    0x84500303450641d41c007446512440130020b080000840311940c1a070004044440a030748140c1c00302c019520041c0119a81e0b641c0322014141150349204407400340d80111500358540d4201031019240a40d071406441c45400ea0000810000300c00081c1d00300b140b401903076440b1803921808003c0d103060042c4900b01d540a400c0c02d10346200c041e400200c03690804401492030840e600e82070700b4804005804104a010303900700f00700040005000e0782001c040c140c444d0300780a15240c1c0d00d1311000300c481d103800840300002d071400b4130245a091401441da0300c403c0303080307507150b15200c650644104d01c1c2e00034401d20698031391180c0c0040c5030262502d043c0c60085800c2841030115036a80307240215a40142d02a41c0701240101d544041d80c140c04069100545005000310003144d00802c0821468000003031640710070307104c1c0b160042002061801a082e00040d66505c21900e64103081d09030600191003120340606079001e00080001d554015520004080e01000710344100b030060600c03410720300c03071b01e140030f0340600c2882c091 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 781348714 1250 781347464 781347481
    0xe0121020a0e0319030e0d17180907050d1b050414040e030a080f010e04021003111306210510060c02030703050a0803181606080702010e060f060108090303070c08070609020603 77
    0xe29014480e90741c00d03a0000000c020003050304c0c6c981c0c04c040d192301c00c5001c1c10012102d03010010010120620b0800c011005524000341240d1021544940000e101191680480c065801410071144039039001d104180300035035004185000b5440b40c4c110a9104000601054031160300074500000c8000a490f96507010242c0607000d00710640b803c00714540003c0c0001088116408464080c6a000b460100c030101841011009031215032112041440c04200c0c4224400400101c04018900c1352254078901c010200c030300c2c55591890f1041a0b0890a20301000501c2000c1c41c100015241d49041c4803c0e80250340c000f1034039281017a00000c04070700c12101641d061024a50103548554070900320b031119002078a40740c98070b0b01104103940a46142210050240a01071440036601c00d410344000560803a40c85032031860044140c6003840405005028440c4c1543e100350b0090f48104180c0040d4558208004001c04202031880c0c05002c1c00313004640076080000720781041d40710540091003a0345a0400d00c51 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 781349964 1250 781348714 781348753
    0x31b08070501061505031e0c1b0709063503270f1f0e040e011107020f0607120f030f06080c0f09011206050c0403051203070e0121020a0e03 61
    0x241a804044507800c503044c18030680c00c41c0c0c03107050080d000041041119150208400d03000e0301d04058180c05021031110010100040740c8014070725802050014034081058084401ca50403c000d0351000c603c1207500c0c0c00b8034020f244849294400d400b040c0c550042c4c4e9680c158061075070480c001c1501500c840303180390b4115100ca00c000d041111510f01c554800c10402060b10400c0c2400c8003519104445270042c64007942c1e054800c9480603001107601c00000e0240390071a250040f122404020201d01d1406509001c03010303110050003070741c03140d2800c0c1491b10740030001034161807a0010001800c603c41d25091113034100303094204c0b0540042c0512178542001d03a46910500701c01380d00684402d80300d0a00c910700500498102c810174403c102e01c5103101c1c0c6400d0060729000341581e0313103494100b100000084003002686010b40c4120207558072409d00ca0300051050b402a5002810401e4100904441c010801e400183c1c00c20240001640d0300741050084c0c3d15503600e0303910b031540350066040d400f025081d01e06 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 781351214 1250 781349964 781349969
    0x301021603031b0c0605070309060219200319020f07060918200c01110c060618060f0f01170c0309070605030c0702011404081204030b0112020d031b0807050106 70
    0x48083c080380074403564215008185040400005000a00c07030404500360341c0c070054000403245804241c00b400c0c0d448482c20b03030340038024414000340d81141c4241c0306540590114041c0030311150030194560700359034050b5240aa016102081070607000c07140e9040f8001c004690044100c0001e5550590759408003a0007540144580c44410032201c082c80c900c0c2c000c52003030030140103200e210811210444040d148040d000440411890b42d0b0751100b518102d0004005410039190910042c402460028140030312030a400c908080404182c105020003036440d0001d01903240000e03103510104045400040703441804400000320021100000e000c000031040008500c10410b45040b41d0700c0c50790720a81186c25103c01c40c0c0d0384050328002c0c45540d00642c490040c41e4103020165004170f06240c0c83c1c1d040d081c240410700008064650001400700300700086043d000340100016224084441d10580229030701d0040c0007001070802001e000701c1b034044a41d150204502e01d811030ba600c0c1c1c58642038a8014002c10260 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 781352464 1250 781351214 781351217
    0x1020304020405090d08270106090c02250b03040206210f0709050901050910030c09050402190815060307120605061e011202070503670b0301021603 65
    0x100040d5411000007170071414016180c0c0c482c6180e5a13a6095a104502c441c5416481142c0340e04280d02c0c8164240298000340142d84400900d66034005800b03860700303100a4a01c0c5040116000386400b284103503100d4012241c0300318441c1d0b40c0303aa862000540384c1c414490f000a4500e407500899190301c8420303d0b2184203c0d80007141405a8a031f60700c058640c41c03c00d10078160b2101c52400144036500f807a484107504860054031203035000f44c50f940d0f5100500c196070480410a981c035001c00c02585480c1d00600b0000c00d200d40b4040559051a0b16a038035503041504114100c0700c140040f0311075403401c00481d0010302e102a039107045490540380c4280035007425500244110310050412030f042c10f03446080e80403034a0585800c000c2e10320f07488000010790080c42081d5250301061208040850301e44401819070b21500340c0e084441d5100d882c1000d07039604140d003039035050050704800044082c08118451000301e14001c200c42951081400400900b003450324994140d400410100b01d030b01036048404203518030a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 781353714 1250 781352464 781352471
    0x4030215010f03020d021309050a110a210309080d0e1e01051902030403050d050340060f0207060b030615010f05070212070312031104030c090e0a14010203040204 71
    0x2108640c1800400a00540b100c10580c000b04000500c1e2080c4c45800716440034154400e29441c114881088440e08401a01c0340d400034220301c2d0070010011002405403904644030000765040504441c01c050030340031044c50020780c0c0b030b4103101414054116070004001c030380c2c100c1d040c0f01523a040003040c00034001782003405178449030403402c554004c035012152b071440180c3d907050407c40c000b0360f2101c1200302c01c0000ca0079800100004000302c0d5080c815242080c1c0a034551580e81c1c2030003564502d01c45004095401224203c8004d0710110034a0a0040b100c01c02d099034400780c622490601c00c000b0402c0014000015100190400c10400c0f9900321a842d80c0d41202030360156943c19113041c50740e0200a040c14000352079194045000b83c0241c001d850894005811b084500d074075000e5151820381d240d001076603510820104403d05980c980214080900401c00c440d0034285182d44a003000c9940e40a000704142d100e0b180030001210800107445071941003030070041011203c40c07016000354020741e02603000710b04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 781354964 1250 781353714 781353733
    0x7060f02070e040b1e010329103f02040c110c01031509020a0809060a140c0c01020c0718111c0f1d071401020a030206042d030206040302 60
    0x800c06a003101e5080b0040e800079030300c65507070020b0400000e054103070306008001c0366158506051201800707980300341d25955929020382c0c4880200c102100103580c0d811600340820190366086d004c4c00040300c0c00c0e03004d01c1b5083c101c0461080d00da0b6002240d008100c00c00341050903018411440b80b1443d0f18001d0390708000303001c180c0340111035004001003c0400c40d4083c0401d204907522a9029010b04d40003002c1c110b00301501c3c0e11162090764040b2410000082c000c405000024006100d415001003080504102d08a54001ca9000030400105400c003040030100365071301414000e40480314411100420381e50300c592100b00320705c6080c1804095210252610b60a020300001e41c1d000c0701d03403448031401030070300a5100c9003502c405401248003850705151071f160034080700722628006120342d1074840302a00302d240c1040400c0028050880c40c00c1d04541c0300036611000b0a03004110036402c141c100c41e09000c0c913003010007a41d03401000622040b0442d01480c803c00c05159001c00d106000b144a5802c1d50740070f60 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 781356214 1250 781354964 781354967
    0x5031f050d02011d034306080a02090409081209030a0e010c0221031e180d0f0c0b0702090901020405010c14010e070f170703050304050409020f2809020a020601030b0910050907060f 79
    0x5440041c1a000e46c2a00e40d414003040d4000c00c0c440c1e40c0f0a00c1100c000d481c02c020803007c20155101070f0303011240e4441c04200b0603000807203449007580c0503500b40c5c029801d014081c3c1004008030341030501e41e030603c91801e004c0c00c00d64440404c524450320784002c2c0c1000c100c1d900c440700d42e640c0d44210b4500c0c0c041d15041c400f60792914110350488001c0e10315050061040c00e030a5080142c0b00245141c00c80c0c41d03001001d003c00005010006000003021160706aa441e00110300521914240c000c01c0080540d2041005204507030300079190011954010840c90306290458940500600800743c202409120703c0800242c00014010000162901d071220180780d00040784c01969641100d00004000d500144828041400d01d9801291100d0008203030000796602c40001c01e20b0356403140302a030ba610840ea19100100e242c0e01c08111700610b074003d411071400b000410002d40307071401070100520700c040140100307500380c1c4100691020b10400001c10802820104d0400380d032044140302d400c010408895140b00807030f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 781357464 1250 781356214 781356313
    0xe041203021314030a0501051501030c0801051302072303090f0117041416091b020610091e0f05040302011505011403090f0d05031f050d02011d03 64
    0x8006002a001402d41080e21100c4800308501c40ca54042c480c410404012500c2405030038050b166079080d070840c8500c0c0c070000400f84e5050300300310f9061120a070010001c90301c80c0a80c0c841c1540c854400161200760f185040c0f110340307001c003504640a5140012031645140040010310102508079407040303800744a040150340704240b010804002c90840c0c00000c010401c81c201e80031898840505480307140d84802008035402c5916040f4a814556540c440c5d9410240000341412240881c00100b42e02d292070603240d9000d266a018012580e62141107110b02c03848101e21901841d1603450080c0201201000000d00421040f20250010341c2880b803081d81c2074000300c2d130140540301c045c4d58246c21805000011411540040c102d2031551184494050200301e06110242881510382e640e15a2820004100c0002e58400704060284528029081000380d50759070205c40c3c240d80c20b007807105a044a8400800510744659002031f01030280e6401c1d20041e10b15000d61004401e00343c030001d006e4981c0510b420980 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 781358714 1250 781357464 781357477
    0xf0a030503070b042a0509010f05090c1303020406030f02030136020d1a040501200a080a0908031306050a0507170903040816170c010206010909020d0b010e04120302 72
    0x2a07800401540022815103031140354010302400340f2840140502507031821705200c15000b440d080d4880c45040c000c07442c0c00d00180b40100005000350f440a418507000030401c40016060380c41540000400921003e00c500780b0a001319002803003000080da80b41004100e0b242103d03000c034801e520306425006441c802c5030251055080240400484010450414614040c10b52059a1143d00d03840f90800040035034003045019500a60348445c01d041c940b400d1825200c01000f00001031110030308820f54040840d00f039030034100441c81c000005e900d8080303442000300315240c8090404100081040b91103c0c00c0041d1080b001d204803410001903036036048180c11110269002c20008d407540908514010034a0041e581040c00d00d03003964039085e81c41c0222464a0880e00d071908081c0515801045120031418008001f0700641000d040c1d1020000e000035101c40050151400c4079669074075200a54136609080b20070181e12418030811542c580d08050300d2010104c1c2d0860b20b0800524041d03210520078000d480380c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 781359964 1250 781358714 781358723
    0x105120a0c0504180507080d18031110121d0f12040905181b0f1207060302030c0d181106070b010e0a11030a0504020a060908071e03080f0301050f0a03 66
    0x8a8504110400c0f024040f26403141c1c005402c0b034403002c400300d81c0a1043c1402421260018071060009060140400c000c81801d84c4104000390020030228814003006900d450048403412041c00310b0203010f0b605100d0310703814a5203e902d440e038071500c2e1000c01c0302401e070308590b480c044032150b0385c210b64450740e1048025190441414140820449802c1e140c2240740c101d4088201d00100401c01c005991414030a40158034050303020608c1181c80d41048622000c1182e01543d11044085108444a99030103d84c422a810154004002100c00301810155000c6034840c1c0018840c2c900108001404080005410b99510b0440d200840041c60800201d8030142d510258800c407983c43c280340c1e40800b240040c0311040658a0349800751201c1682c1004511410340c3d4800050981080e00502611300a06c0d004036041c002d4000c4244040f400c0004c81200b141d030f89a071501e00000d0012040b800c01c0c4c503158002040e150000c50b488214007040005141601c205541e1400c0e82c220380000c0042e00042d070f210142 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 781361214 1250 781359964 781359983
    0x5160207050d08310504060e15120a140c030f0703120507060f0c02074a090615061216140d0608010e010203040c0b130b120105120a 58
    0x40780c148241c0580400740920041c0b8107088002024001d80e0a08448801000007a04420b03164055000103010161209490800a2a0409154050040780035213000259201c5500700c500e256180b0701007942c01a0301c0f8054400903078261400b00c0d12020540c54840480c010702008003c02c3c14005068041210080018140c692031500d460300c4500d0110003450800c4410080040450001c0c0070f03a07001d501d250000043c00c2810f4460090410040e60080c80010102e006000b1201041c16000010a0100803203100110b0780c1c07900c882000d80464800c0f01c4550352010400518460100d074192003009a2106450880010300070490355100c1e216510000d110b261010a2401700c42000c0e412103003006041403002c480c000c2201d21100d400140e00000819240c50003480720b08028051155007110140095081d03082a5498440c608558003500802c10004a2030013402d80c0c10b0b507000c40040c50405081c039507400000d402668001001d006003801400307102c0d03200744100800200d070700c600d075000802d69 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 781362464 1250 781361214 781361219
    0x2070504050903220f0b071101080c09100c0b10050901080316030e040b1206070e010c05032d0c011a10020721060501080606011e0c0609020109030f1505160207 70
    0x441c02d0b81d1807401c07540c0c00300c9504017083c180300c160b404001038400d80d00c5264031140e442c40d21094403100e04c0500c0d4100b08566052000ea03a500c9020f440501401304c1d03c41d070007440d40d214220b612041c50440a07107501f005000388810031035001a2101940d0b819a8200728030b0780c031130421581d213105080301d1108040280310300c2d40110303101307180c1e5840c54000200040f500a20200003d442500742c845482c180d50032020500c01400d07080810807000744020300701020300500c1c68075000c0c0c6a0050b120403141c0f81c4451141d40136014403210089480456001e8116150b08012515500800300c800c0c605042242c1c40401015500d8641c442214815080d4018070080d428042c03100468000c1c0001d4400d040401c100100001328903004241c003071701800000700140d18100c0e0005200082011070304448100011074080c0c215840300c000b940c141e8000c0c4000c200600d491004989d00411540040c1c2001445400f840801c080750107440c100c0031580b04148060f80310300c0360444c1807102d40d400850150340159804c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 781363714 1250 781362464 781362487
    0x30403211709100621060209010516050d080109023907031401050c07030816050904090602070b090c0f1c0804080f1b0d060510090c050a02070504050903 67
    0xc0800c91045440c0c015803a070326000c41c90036442010341c2e0407265038129648504030752032036100306030082c03401c1d048206854003020660510342d030221001510181d0006150b0349641d0048003118a4128005002103482180c2e04100d5201e24030f40340b00c4000a4081000001e501a09000383d40c101981e0040c0813207613041200c0d036420b001420081300c446c0d0440094200051090612a000065010b8084044000e942200090031142c0092120076010002d0110300b0101f40e00c854103a0780807801c00300055250360100e1007034030380340203203c0440d600c5410640030f0410001c86801070b00c00644070300501165510303204c404607124905100c2d8550001d298142001103460020740440c1f89131418608081e50f00750603140c200d655889030300005110761004081d4220b1003820403e416100701c2008104075581c0141d0000f400110400d45d000d040c40e9110b50100e000b003003100101000414141800b04000c0710300034009440c0c2e0b002071680c3c20240c00b80707100008440c00d15010b101e1180056401861414203123501 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 781364964 1250 781363714 781363763
    0xc0105070816020f031002041d04030c080f0c01060609031101140d0b060706020d060611010510050f0102160602160503010e060a05270a02090a0212010306021608120117030403 77
    0x41a40e00c2074101c8150104c0e501c0a005208000d943d51b00d0240e51503040004890f8002d00c14105415040605010000400d42c40b114040d074540e4050244c941d0b550a90002c89954050840c44070155460329000180b04ca41240c10f1100b1240b00384802075000001c0c078010b40d01d0310340010409203610410014000c5807251640084010b900c000d210307a05203400c41d110001260807036100e142c0c03180d076039130001c0c0301c803540281e0802c540c184d120000b88418a402a0001200785191007102e014600c507503403400c0c040c1e000744000081400404003e0744501c1c4c0d40e0000a617030740750b00c031750b403110500307004a012400341010301445810303080e844010030315502c0329500c4100806005014410903405900c8940c814203004110a03070b551240c60003000301910ba0300400c4848800030b040c54a01500c1044400e1220000076480c07411240c206c0b40050315280325002420794a061584000c08400000690150b8030201c207000c40e060300d28800d808400310003241840750b40c07403190303010103001d8002c0c54038140303c08844440c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 781366214 1250 781364964 781365007
    0x6050a020c0f01120e0a110d050a061509050403030b1513030b1302091006020105070e0d141c0201020309010b0909190c05060a031b0f0f0305040501020c0304080d020c01050708 77
    0x2500404c40d0052001d00c004907045010300e0785217074000020400901c42403096010400a040301c0031100d150311070792026607178100d0501c000c0c800368076202140d05000d1040b44400040c4001041408149498a801002460245111841031031100101d0300e401040b40140e0b20004030b402c0503413a42c581152910250200000d1540c64480c148280350f10050319640003841c054104090241c85543c10203802070f003075507002003c03641000300314480610607584290b80000c02c03503000a0b958040c1e5400485aa00b40901901744551505050242a401e10b82c1503000750321501c04400200058080c1c403042250015065580c00f44591141e000d9400c3e980b41c0301001d88456200c0c0b25514011036440000ca281e50300710700410404a59078a00400768074521468030348041a0901d424125035580e954054082056600541c0825a9801c0003c081001c02d604072007102140104507611296505d8482e9580c07840700c0c02c10001401070790140015035006409071000c003a40711000300c0c00c00724081e524040c03102090 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 781367464 1250 781366214 781366217
    0xf03090a0618030807140607080c0a030b1908150903120106080a02090307030606031b0509160203070f2102190809130606050c0c03070e04060b0d0804080106060906050a020c0f01 78
    0x40b200040042c03a408010b050103403040141203818964000e926007480b04c000c0640d81400740203401c201100e9443d004a034003161076410002101c8581802140c06480928407e001d600c880d100040317003285000030581c20390f146059581d18075590360482c02e40c60740907003840e80c034000c01d084e001402440d00480c4000d03441800018018105000c0000182c9409850350059a03580d640d4041401441070364040c00310f0121504001001e01c1c1d28140100c0c02040d0010030090500d5800c10f400d120541c420700c202c5049503000041c202d9804d8042c208011505103007601038440000b0b004000da501c900104800c4050340b891101d4400d03555541d125080303654803e003d0540e11035609007101c01e110b151840790700094441035862940f0f032007908111a1801c002c8001240c0710764024017007040191801203500e0f030b005902c640007092001d10749000c200c11014007000180506000300f800301e400c58055010f10110740d1355a8807600c80690300c1006840d03500c503800c01940141c01c00c02003c2c1e00c0b0b05000103c00a4120107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 781368714 1250 781367464 781367507
    0x20c0c010c0317010b03060a06020a02030a0b070c06420522150603180203030732010b031009050307321b27070905120a02030f03090a06 60
    0x2e08031103140c3c40740981003210030540202c24410203090041c0c010015043c107000900201c41a40c001a6981c80304c000001c08080c2d03514005000302d885010455001980483d00340100c8940c8000808a4001c141a0b15441c403000c54508410802800c5c1c410200d0b00d0031070b001500541410240080e20140304e04519003000800d0282c65060b0883c80b54403a101031a010706030125090000007410354843c2d00c0768500080310521b80b01c01581d0080100d9140c9540025500c4003043c021f43da45034450b49600303000e0001007050800710b142040641090106490172001c1e10b1a03500e01783c0d0650200c078840100545654000d0101c100011940e686101c2c030401c5c03e00f8400303039101900c0c10115402c3c403c040361105a0b0403291200f4141e52003501030810691080301c07298421101040e500011110302104140c24031180000b14031b0b000d0107600c20f000074000140c84c0c01401e500741340c0110703503030010100d00f00e000e0701c0b480f50140d12282000c03050f18104100103003250f20840c41c10703501f25400c100744107641291901 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 781369964 1250 781368714 781368737
    0xf020405130509010b182e05190e01080a1e03080402060c10060b09040f020a2f030a260412180b030106020d092c190608010501150201020c0c010c03 65
    0x101c1100245501a07400e00403c6180b404c1c0d126108810b03612421800c1f4017020659511200002c400c1c420140ea03070590b02000e402940706015000c80032140e000306500c040d50000419050804191180f4280c0600c8144074020f41c0e01e8a40c00400e110f0031009000030302840c0102d8010b142c5500203110030b61461003100c41190314606a002103600984c04000b81d03000000300d840c498200fa0044910441b5804021400c1107050030029054100c003050007214143d00581d03d050740c41c0d034254080c4000a000301120349480380400d0103001140c0010031184140150200c0c40f451541401540703108513400407440055050a000540301080048102d8024100c00c0d58081000707072202010710b008004950052a4200b134126024042c54455007000a044420544000c0e1159450b407010126046100c400e0b4040d5589000359010341c4015680207000a0910800150f070502c15044141a0343c5880c1480c0c18041421400760300300e204941521003d038001c003a54010302e60041d2051440d0b03034007a04003681e0015 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 781371214 1250 781369964 781369969
    0x80706020c0d0906020d0305040f020913050102040e040201140a0c06050c0408120307080f1302012f010b0108090a1703040201140a0807020705010c2303041205030301090f020405130509010b 83
    0x3070b0b0186800105054401c1001c01e074104041c51403500503041c10819814180c0300c1100c403041c03c41c0d010b4096400c5402080300c1d070125111180c000e43e0040001c54941d03440741c903007091003441a035059000408043c080d21100d01c07140700b01c8503018000d880e001402c125664070704e005064014200d417070341041440300143c0b605090003065180000d641206540385080d50000d4926000941003001903d900c2c0c040124242d61400d10407549502403c180c01d103c18031a0301d4040280c0d09901d0005002c0040c100c5030b991150541044548440980300d01a090ba924441c4582d1210320388006081d40d101c82d40c079160801c100d580110f4220740107150070000c407802c0d925884107550082140310002540c5800b0450303170643c18440c00c3c024000900c1c00c2100d04490b9101c5d5007001b81e01010811031540c042071020800c500410840e4000c04c400d5443d009200c69504005459400034070a140c01d071410315060034200d40441c801c84042d1038000384641e1011000e250180003e06000b8800d0344290358800341c840041e03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 781372464 1250 781371214 781371223
    0x30315120709020d14010303081308040510020f0f1b0f06070203061e070c0b071209020a080a0308130c1203052502040b040b09070f0c0f0318081603080706020c 70
    0x1080708002c00b6076107204a038034038022036666444c2900b10310010401400002c1d80b00400d590807415482c1a11004c00482c10131295521580d800f00c2d503c0b54a0190b070030f516a401080354400041d44106441001440010058841e01c444000405020024000c01ea140c54030b42070007001c48402901703c500f00040355004c6440c200c0281d60b8001401082051840050704c0b12205644c03268084c603140e01410a9542e559002c4180540500b0501941c40a2007503044e8071a030108200c0781c0c00902d10758000c1e54030ba04003601c582c132441081c1c00107107407200014007002400c0d26820308150f20120b0401440d10f80480c50f0049210400118101b000030003c07500d00101000ca03170030380c1008031041a40c601078140b04100807a0344070030b801d5018a0074100c50078116511380701d146134081c0050a2071041c5101c000c0040b40c0e070403104c6030b000b071403050100d1401003410f03070040450310380130305c0016510f504070386503914103a42d110300c00740f04100a46c1c2c0c82c20600004541e0320280c00014420702c0b02604288400020fa03091 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 781373714 1250 781372464 781372469
    0x606030203180c0d2a091b02010e060103030302280512220b13080c0304030611272706090c1e2104121701080303151207 53
    0xa5004800d10402040e141038500302848007000401d4000403840120703403c0300701000060880101401c0c0e0700d40141092680c3c424528902d600685095207030601c82e03000705130840c00b424030140188003403007141d80144030340d40090f100140100010ba05e182d9045001c1d521000100c0c8259905500c54041d1548030b91044849001c140c50300d9403508800b00f6810900035000701600069040e0401c608260001c004d410026144c100e460101c9079603500d440320f0701240d070041006154120020f8100101c65010000c0c2013034901c1402d060040304a03d21360380c100d500441d006460007149441424400340b00a1f0030142c5007070f101500100c3c8040c107210550a07003102185001c01c42c12030810402156103025604154000d800031210b80c10145108600c150790320540d00400020f0038005180588650b45220814090850040728400740c9803510b405040e60103000d40c940040350407911409600d042101000b8142d543c924011829945d501010140f100c180803c1c641c1c111118050300b0103146014003040d000b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 781374964 1250 781373714 781373717
    0x703020904110d0f08040504050c03011203030c02011b0c0c05090f0a05070224070207060f1704050c090c0406031103071e120c0315081c080a0b0301020a0c0615060912150606 76
    0x81b604e1905040c03006954004094005076007040005004101c0780c4100c5003001070300761400040d14210918264010074680c450340c4a498481e100e140010780e40101a000e91a10526000600c10380c2c031030502c0102c010507111030b02c00407514030000b6503030600d41d48255030106140c4115209203100650440118a100803171500c1e20350120100094103404120100c0207241c145400c2e000c0c10703114813000342140308800105042d860802c02180c2801400c219924081400501c0017800e42428038a00c4202d510078441d000100b41885002080c285002055a01c00c40598490702c1c003810340110300311840040c000c1c984040c4003c40402d807140c00058403030b0001c4500c19407000225151060b4400d14110b46170b034813074241ca034000021842d090321a40c8091090307003074504164445032038080c420005400720600c0103030590b202140306000682d0121040c00d0050207460108818407031994030000c1c0c100b030780c010039002c00c0381404100b2182d00900d24810006008204d104d0b0369016648800b0f0940e42c042c1e01000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 781376214 1250 781374964 781374967
    0x130b03040f1a070e19080102031303110705012a061b09050f03120901200102130b190e01050d240f03050c040f090f0f03110703020904110d0f08 63
    0xc006414408140e003000012414402d864102d10080c200001d200e8694081c008001320506091022611309019000b52002592607150214079410040506142540020452040c8803104080801c86034180c50040e95040c004045072a21105c403402100800800403412099401c040340071486080c00c28400c1000744a09005100401003801185d82c00c2030380b14903141e440b000083d680004401c21404074800c0f40c1525100307401e0050742e01858292402c80e43c3c1d508410020340c442010740c001c0c1000034203041413601c01520b5504400160043c0c103003c56011a000c002c5880c40e502920104440131014500340e80783c0f2607e80c0c80380091390940d66008182e05542401d900c00c4101d106680c801400c2c14400c0c1c441c1d010b00c1c41e01ca05a8504500c800d0303034050b50b612803490b581d0101c44d8001469840c3c00c202c03141c07403802984c40d0070312010320910010f0300050f060000418141c0e00200d5042c0032280c008026035003c2d210744d00c1d0108055400c001d2264080c10701c2a554000604004100008902845070039 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 781377464 1250 781376214 781376243
    0x2010c02120a0312060b0a08060d0201020708060405032503020309090c04210b0c0c070e0603120c06061207060c030302090f220b06130b0a02072411070b040b130b0304 73
    0x100391a41508042000c400500508400c7c40d485845554048012984102d01e410140010303400d01240340c103d100240124000c00040c0a8000020140581c0c2d038003807001ea0000340845000c2c45080202d008006070020003809200f0710340f00304050b07041b0300315054851410341d4404090700040200016042c80b2014008a43c0030300003400c542c5940404403290181c5802075006c205c984030780690103500ca08401200114146890800c0841201c40a04088955660075010035a50340c11044880901c500f45d40c07220340d03042400205843c1d04480041d100c03408441c00300c0c0d4080d00a504112200e0b03400c0800d041c48003034155250700d4500c08580e20b102401a00b00c403a614440103840c2801c15090045a0800c05500d200300b104220030304403604048510f89a58181c0d20490503e04554425549140f5601c00c5000016501d031102d6041c2c4442e4a940b008007032110005030701e54030b0300d00c0340c14002c200600042001c4d0150301c00800d001481d150b10071441507180d420880390b0b50815141580c1e21a001005ca = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 781378714 1250 781377464 781377497
    0x1d03061504050c040b0f0304050102070501110903010e1c0e040207150e070905040816060b0928050411091f0f030209340e090c031b0406080402010c02120a03 69
    0x5154009a580214618141c103218150801b48242407201254507030000015051103029030584e01c580d03921000902034001c0942c4800c13116003043c00070754825480e01c1015601000005000200e501041c005103001c01942c9100307a4180310007115680e0003c0d000c100910004510203180f4407041060000018030070030041680e407a183c40c1e6041a40c1c0e03603142c00244400318988070151810782e01589888465a426844d008002d1300800c40f03070f640c2002e510002d100b40a800d100b140c103509050708020300301100710307140d4032000d840081c0e9014060028072030000c0200d0400b030a42c9580041c40c204141d102d60b0080311940d1501e205680580c0c05420132040a208600d4180301d510341251031070368050111400031444220500d01c0e400b11410903140002d0075035145010b02880382d0400d0300104440058a0030303462000d03880e0310031078525208803c0a03809240551603107007a0750650b80c45a13600e001a603915401920a00300c120b1051340c1c44001108102c07074007030013040f4814000d44255195000d52010300c54 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 781379964 1250 781378714 781378721
    0x4020907360f080303090307020607020d020909281a060a080a0b16170610090503010221100621020d020d0207061d0307020d020402090306010b1210030807031d03061504 74
    0x400c0f120340d0020814040902400000d850b89160100e03551566030003035100240f0070951814000390040141c80c2040b503c0d80000c2104180c0c4403915003003021500380784400c0b201d003000e000b80090040401642060b02ca1242e00c2c1841c2e4440c0003c1c0c5201c56281e11410050301d0942455000c03100013002c0340030040050f003001541400e10800c0c1c00c0103100c8903202c80c1600018440200001c1c003403503219504004440c0f04903400b070000d010140c02199a4020103820a07004500c7c442821210950000460307121385400c0b40300c2040b2034141d034410a501c081c0d040400c3e820090004d0010043d502444000744907131a602c0104003000103414016614803162801e03509851401c0c00e681c00628080702a0304140c1004411102c0c050340c11540205030180f40d01c005002402009080742d0588604000400c41c10448001880c0360310070309003224000e039111078181c01d4420040c000145001028040c0c0c000290050404d00c000c48030705403034445184a0400403a00e030060072145204407400003400b060482c1010f20 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 781381214 1250 781379964 781379969
    0x100f0509060603011401032403021c080f0a0c0c0603060e0702010c20010207060912180515030711011407120b0d14070905280504020907360f 62
    0x44a900481c64030344000b800314001446036402d00c0350000812080ca82c401d43c0b18400e2146e413480d0780c880300080e036902d806a0650601007240508005c9841c48626a80040500112a07201d45002c0c0307012a20b07810100641c1080b07020743d061200340c500a000040c030314001d6030003400082d0380c001021454400341c00c9082202600950135a49002341c00094158000354104601c0d0340c0c2c0304a000d816401c01d462900a01c16481c026020520340900c03881040303080d200c000e01ca400203544245001e24120b40480014603603104450f8814941c0e401880f0f815844405544e11110505120036403800f40d20300142540c6603942c50300112805101080061074104082d50401036003580c00300941c03a841c2e4041081d18042d444040c0440b6987c4088110048041107480c029114540d010b2010f07050100c00202c45210600c10039204e40b100c1100116039100610480784a40d030010003125035034a0301c90701038030007280d1094500c1c12141c020050464007481100384061403074034400c0c001c40c150310748100302040300d180c4e8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 781382464 1250 781381214 781381219
    0x1216080619090b0609091207110108091203010513020705030307020705040e030a02120f04150207030618032102130b19020a050703060c020712120201110a090308160b100f05 76
    0x144000011900030f10090b0b80c80f1800f42c807100604d0b01c0f07030082c5a240462402c00c68144480004641c41004030303803800c20a41580a8a486101d51510483d072a1202c0c95008100c94800082c0010442443c1c010380102483c04113481c01468a2032589402d4119401200c661000d80d03c010003c11240c14140701d03600940000c1e401840c20b002c81d00134020b403038032036a60980c04c0000340814484201001881103600812404c5900a4502c003280d030040c1d141d04071403000382c0e00e82c1d261488210b0003410040e60050240d51650352244604041d4044010b0841000700100300580d0a104109440d0040240c0c031000d0007102c00001d8440401c00002c01541c0c2d074a40ba80c0e03046400c6601d004c0300040d4000383d080d0507254007203004102d0365032418089281c01e070755503c000c1700080e0b40301056081c04104015000320744815802481400448808a40e0030302c6400300030340016021070700070401f00b50700c00050f02000d01c080042d0f4224072510f0301e40c0e50100200340d8201130000101c00d0b040140c0c0007c059104002d110a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 781383714 1250 781382464 781382471
    0x90603050f0c04060f05011202090d12020d030218100306051005091306060203030c1b16060f0f080105040903021009030503010e0703140601031d0a080d0f02040803091216080619 78
    0x40030448202c1c0e82d106c0c407440f0b0500107440b0030580d480082d03030145c460a020141c000342d01245a800c100d60001c00681200015010301c80950356481e01c64000c40c0c4011011101e00c0718841080018040d1180c40d001201c0d040695420020595541c2d01125014074642c0769109521810854100104c1d241d480c07450442140c82d10764100241c940102c140d0390310241c2081a951540d85172814007595403601050380b0b0107402060500e1065840d02d40d0803000361048da0343c403080380c10b1202d44d058130400b020003040000300b036a85004100c1440d01e6085040418400c0c41910580c507413800f421019655155411804180c1c0031005106400700d81c100654030484600d01800241c0c488000b140544d14050310403030405840baa600103007000c0c03040015140d02007540417a005d50130075081013922500400c480601c2070b800e2402e00014122180291815503024002446c0b50030750b0301c02040503505076170084034150b01801d01c40358100340101a07074400414014015154510740504404e0078441600d401000c1e041c035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 781384964 1250 781383714 781383719
    0x50403050c040902060d1e050f041a09121b250605280c0516081207170301090603030f03020f030402090604020d09080403020a0608060d03050a0504090603050f0c0406 73
    0x144440456a0580b000140600c041c00860054450440301c010070a040000384484400540380c440c0c000d2101030070030030003a128820410740112083d503002e03084207000f1040000c12800f1300b02c4e142e0000c48010882d030340c070b41050002c20180c1d00840107003028644040c0702c18400c410140400c144414500a0b803a00158041021106901c024010003080040200d401800c084020208124048079900c1c04c20321044840002400580c114030201c8030303809190354496000c030310340e00403c003a100c180d4083c24034a0b040010324402c03034225603026503040e030740f40c4c803065071100c0e07034400640c040c104040e0045189407e50901030100c5881910ba001010701c1003040c02d001c2e0030a9001d60780c11507412114078541e512100f00080280c09400901901146801003072410048128010030842c1e109a03001c4814507600c02042e030f18003e0842e20903410501d07001c60140000d20400c020501c0c0030792800c0190519455035140740c1101c0c00c5030012242c65114000045007508108010a40c6403c1250180020f90 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 781386214 1250 781384964 781384973
    0x610030e120a02100e0109060608011a0913060c0903050f2107060f0507031a03030c0d0c06110d090302010b0915220906060e1303050406080402130c020303070906050403 74
    0x4640c81070716411038101041100a1a03c00e000180707928880d12400d1185280f00000c00d402003003d180210ba800e480d0620009001c0310600074a044442c43d00d03103882d0701c5610036041c00725130200204524005040c1c1c21004c40050058880c0700058285941d448000074110303c0c00c1da2038520000d01d84039440e40181c08031004403200c070a218100c08040c0007120b17282d24586c6040c0014000800f02c00741e2442c02d0400300034000d0380c0f40d0b01c00035000f010101c4008036908194203140c0c980c800d00710807400710b400881c1121b40f10f03030040080c0d60625210f6040000c00b440302018802503500010a1a240c4030307141d0045805142d8240101082d1800c12030b0010400e08000001015100502c85030364001c80c001c070025000700b4031818003440c002c00d9040d070511100c015440e054000f07080c0c600984030040002404100059414103c2018043d03060715880c0c980f6003006c4c1e081d00e90f04002002261b22401c40c6a801242d244140240081050160000d50703da0030203500c00b525200307440d00000e0400409010400229 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 781387464 1250 781386214 781386223
    0xe0121142d040c03021302070506330901030602090a0b0d0b040e0c09160332070504032a1d01060e0f1f05070203030f0c01050709080d03320610030e 65
    0x21307541112100c65655404191744041d0050990240550050401700401c80c0c0945c8510420b460120b10707038034104112040b10713070918501e1440082d0400c181034010b0001450030f500421070305600600301d007541d60b62601c601d502507101c0a030100003140c4482080d140c40c101070181c8140c428040d0b024000800081c00410020300e0700800440009100d54120481d01c0d0180e40f1003240d14106000c80b541086407e0840940709501c0000710140005581c00115000d1080080c3c40c140c0383d0100310380740b03040c4516102d9100e0f40300384408044c0040f440344000a1031407107000c40ca000c1d8101d8400c0e00e895580b40c0f14001e41030301c01d00044240980da4080b020422540d489071000203028150113000c40352541c5c550211418061490000d40500c00000c0607030440b20180e002c0c00b2000c0010b0001e1100d5a561241110303020041e04c0769050700ea01aa00200b041402a0400300c142118103c030b45014a2101c0c9824104d0406840c4221101c030f0700300d00b80a00d41c2040801200d1800d070780d08050120718001454103680d03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 781388714 1250 781387464 781387469
    0x121109010c030e120a0831031103120a08150306010b0f0d1503050a0506010503030a1e0c0209010b0a030f051501110309060d0c0806010e0121142d040c 66
    0x100b1907455150005551111030348109031840c44101c0c1c44c0c0e07100506d0310080703e038803955640c00c00c1c5118814085001d0b1410802d400300a0081d401550003600e950740d0240c10200e071103191a414000c5c1422500720712151000341c40b03007903007075903499105041c442d90840c04110021146402500040014030107044202d04542d5515030344458203540320302c0040e0010042c035a51040c6a00d00c030f005080007082c0003001071045102d0340100141c803816680c410406680b4410400b07603c0114000744841d1140c60f000d240c40002c14041402c00400442840d400206491001d0f040303e9441317240401d00d0354102d54140f02c3e80302030155a94042080f401c00264050b60b06600e801a241042909a02e079000d040040c015030764094400b401240c0c5a180001c001e001a000e42d165010003d044000082d15a610805603500c82240c182c541d551000c2c000c03400309030189d40c00003061442a84400c9001c0c008920488110b229800381003960342800d0030004045410b03607144a402c191800c0240078070012503042c030102800c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 781389964 1250 781388714 781388717
    0x307090312030605061c0b180f0f0603060402060c030c060901020a03060b120a090312020324091e150303070f0b0f3105030a18082e0207020a06121109010c03 69
    0x1500070014141000e040140c1f01140c11103043d000d40b40545810b201014010312059100b0360303583e40d450a900302d86840032240b190b0b05600040c0802c5c0581044c0700241010103200c400d0b85d1801140700306c89850110155014400b44c1e50000f107071400c1550600c0b950015003081c0011a00d020700b0500011900c1c54003074180c1c9501642c3e03040e4001014004c6040122171015042e00359105d15012400815a402d400e215411a41c88100010218908100218412060310a6007210200140521072200b00000c0a0023a003044041240000e59001c0000d0442544518001e40c4615800c1c9482581082d001d81040c200049034018426802c0807220291070400740103890003a024442c0d42007441c400c05041c4054010700000490380d5480340c2c0080c040c1655043c1d5104c10b6406907444540369903401d02107828050b40015000003540c00200c1216102c3c01c00c40d008000341c10101a600060105032456200760b0108a00ca244908110014003601c17007150350a251503824044090000380004554000003070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 781391214 1250 781389964 781389997
    0xb090a0209090723030f070f08060a0506010c06051b0403080421081c02040f090c021b030c0d050c03120c010b1503060d06060906090b1206070f0c0611030709031203060506 75
    0x4c84c01d4400b0410003030322510000468258950b156554403940100c0d0003610a58082c65000801481d100d0003460700404060703507084140851500c0c1e10009000c0035061a15540401080415851400300908059030260a100d55103d10702541b100c1c051008041ca000545416584c04012441142c245c072608811041403584409201c0c040070002d11407a00b05031040740103a04d021912000360350100c084581d554084032085601441d076211248450140280c2c50745c03007000e81242c0c82c10b00d00f5005409a00c10821074071009003280009040c1710300002d400038090720101e1103042d0981c0034010121842400d4917032a4124903900882c42c05803000800c05400381400c03821402c200080356005034000c2c020000704100c40c640750f0032850007034460000711500c507298940c0345200d02c24001c140217000702c180d41c59641080841081c207540001010100740c81e440d035200d14801e00c40a40304010f610598036a070700d44034000d0552030302d10340099802c00da00e400c0604e00801802151030300021243e0496204c102c80 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 781392464 1250 781391214 781391279
    0x1e02070b0a0e060304030903030810030213020d0b1305070215060a0303031a030703080301061725023415020606060f091e040b090705040b160b090a02090907 69
    0x2d031003100001c0301030707608080000100802d15a002c0050000d483c425a02c941c4a40c464044600503240e060001039030000c9084010016001d8641c02062104142500840d2511000000070746208050505000300e03a2594200400585d042c00050700320501d10b060704d40c4905154010405900349404020185985c2e101014a5042008070709140c00000404940a41d9281d140002003a0802c0c440c0901003200145807a51922140c01c8584c030800702d1005507582314003c022900620107155161200390702403d8095682580154408d92042143d800510307101c444110240d800c20391035910807410380705506030300c0c04515808150540c2101044400316241c010014080000b441003241076907005440001d0081c0c2c21042a0403600d00f440125030070807910000c03a050100d00039040f0307104070005808203c00d0100d40144c50191200012045060340d4026480e610020350480c180d41840d0154042070341e01c400c5107440403003154400c18071400b40c40200d1400081079080c840b41c1700d00000111024002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 781393714 1250 781392464 781392467
    0x50c06070314130801060f030203121602060c0304060f03050601120c091d09071202090f0714030f0411040e070315110a0f0908070e15030a020a151e02070b0a 69
    0xb55901e42c04002c145030b6954005030f05000201024801e8815550820100285011002c0c1038041101e80143c040c0480090306241e0301d00d564000490b400700b80030341030403000c05610780c0b40c0039021101d0311000a603035850908001600c11a01d4101c00010181003a00b008082c1c0d9002c018101d601c00c40c0080410100c000ca141074403280259001090101000d00401000a400c10b41c424060ba14007010744da00e441e145c1000c02c0e0452500c0b800a9004035420340070502c110180200c072035001c4034620305150740d051042d000007000d40c800d42d070070040010041c05001c00d0101e242e0100310502d60403038082014142e0b0f0450f050700d4040c0f0344005404000800240b44040e11650081c81c0b03a43c00f00d03035005544203140381003d0412400c002010001400700080810b9104001603808151200d8401c82030955582c0380861035000c24841c0030302d406000322251030707006880f0306010f4400340c45030005820601c2c255030300c0140070050100c070303040310322441500001d10b594020804105a0303204002d400c0d13540c20060b40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 781394964 1250 781393714 781393727
    0x618060312030702010207060e0a05030a0807090f030311100501050306150d0b01060306030c0608070e090405010b130b12060f0708131e0b0708090c0f04090807111c050c060703 77
    0x8044071909000000c100c0c01a50640c01880c1c45440f070380d02080304203a44d190103030340c5214140c80204951700422141407400d00036040c032584600c0a2400f290420303107540a0302c1c9101003d034000c034007143c008051340f01030071424044e12115580c00b00303041066625101c00280e036142c0290a0314910444420b6200742c40e02c7d8203042e980381580040b41c00c010303540c2d00c00e401401455584025a81750781015800f2074101c2c820301c0c0310340c0501100d5a520004200b420f04114114501400840f142d65031550000c4242d01c401c0b14003001d85500e030304000b81241c005030911641ca4201c81050000ba040441080001c2c40c0324800550000344a25001c80a96900122019100c41840010b080c508243e201c55107011910300041d40790900c580000303652500c0f01d03a4180c5000c0001d541c480e8041e0403002c0040142d0900d9816900140c2d0f000707101054002c616224591268010f060641e805c0d148001c0b0403140e41040360b162141d5030307900c2d0801100c4415907110541c58034100c03044244107c2000408401341442601d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 781396214 1250 781394964 781394983
    0x50717071b3218090d030507140712050409050403080613060605070605060a180c18060e09040219090e010b030706051602190b09012c09041e050f010b060306180603 72
    0x525540c49013408545541c1e101160070140380001e09010000301d10501c038900318040012004451030a2103056540c01c2d82d038041011080f020044103110000b14884107006041c02107000e500d0310462414104140001c0121602d0035038101c40c00c021040101a07444801c440d14a030f0416000181034030740400203400940268811000e500100780c0b80600350450b0352107148400d101d92a408140d18850101d1500b8000030b22486011035100450000c960030444074503648148001c00032501c1c403104003480e5580c11804d41054150541e00c00e50750392070040074419880c1c000400c0f8010002c01c1e10744000100700d4400e041554403440b14240344401192100d558014400c111420351540d0151a080c40c003416801640d9118000703030710b5030309910303011980c81c0042d9010314100440b0b481108400050005e100300140048501d00e05200504401a20701c110303a8070000e200d18094240c041d410607085003990309600440f071042404005202d0a5034030502840080024903194100595400300064240208103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 781397464 1250 781396214 781396249
    0x250c12051e1803030c030a03060f05090c0c010b03010e0706090902041a070309030c03080a0305150616082107120c0903030e040209040903030204051003020c0607050717071b32 77
    0x45445c030111400030002d03010f42c600d0350390700b000059614806080c0d1031890744a62a0004a82800316036414a424002d00b04a9029800840c80b1b0029501003801c445881b001e003030042e00403407000d01030b0980c002641c1c801001184070a6041904050141085e80029203055200701e00c006a000101802a00c03003038021500500091401652401c21100c941d010f06c41050000749002c00242d6102001007103211005000341900342088505020780c9401c0c6a902e4040c0d94054052212108015640300103021600000c07650b003820381403444015223400010b110001009040c480125406c560010b2103200f103a8040c1380c02c1c00c960208030080740c003c1c03190f519510381042c20003106006148d0107800800840e40161041c0518001036a811402c81c010701403410000c1e08020f011aa0f003034810700103880740c24000c5101c11460215007145090b15803013201d086811403401c1e03140c2481c0c0c2d50b00c80070100040c081210008500c100000c565000380e000000710700310300d0122400364001030321401e4201c1a45d0802 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 781398714 1250 781397464 781397467
    0x12030507090f090212180601051e06040909060b120a080a20010e0c19050d2d061b12050c0c240703061a03250c12051e180303 55
    0x19103c01201135031140218608424014001c28002c58510803041c089046007401ba100990071310082007030022442c0b1121103040c25500c0400c015507120401880100030b02000003518120701c0c6000c5040e10180742005200346a00548054003a401082d034002385a8014801c1d0781c3c03246500019a001c42130700201944607031841801d9010420150f11a003611988201103800603240d2800300030b404460f803a0f5001207083c4175501084182400c00040b500248940305603100c040c8184184032089135114080c1e1403400d4070031105014404a88124610240b10349034040c074a0205200203007900e11100d0f1403036400c40e5030b04000b40d07012140c1001c2e070320b458400006544506182510030b1110002420004810040500c017150580d4081e120721011074012951010603d0005c035002c2802e80c01c010413001d91034041c014601e660300d4401540c0140c80f442030b00e0b160403622980c18200d0048052440080901a0412417880200d841503080888501c2001c1c0c1d00759141401c40c01c03101d055a03100c480c46d415100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 781399964 1250 781398714 781398719
    0x5011107032d111305091002030c0405060c0d0924080a060503011112010b040501141e0d06150207030201020606041802030610230a0311030a151d030712030507090f 72
    0x4540c3e501044500c101c0c0c031258407900c92034074541207410558840c0300650080c8032001041a0b25005035601020f0b1501181c103080c1c0d46d0001c121580d00000344004070350840b01d400625160000341040181130214240c1a0121090400c040c210081c11006c0091051000c00140f42052540020025280250007800104000c00541546802100c010b017a40318125002146200038182034608845059441c0c11044103034201140c12a8080c00110b00c3c9807a80340300200003240c002006080340314980100107030070b9103001c2408a454550850030030442d08414070800140c2c1c0d00043c6241c01c02012a000500d41000900101700f40c60707080d00007901809000204028100107070303101d0044883e10b4130300800fa9101400701c010301554021005600164044041c00840e401c0e02c0070001c0d510002d4121003041c0f00c66181c0c4d80000c1c210030303c21509540c84840d5580e40c0a070014050700e020003840004d45c10b007045592155000f40424201c603040540e41c10020b21020320a5502d00d00500030111031581243c1c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 781401214 1250 781399964 781399973
    0x304150e0a150b010806091605191d01050c150c0d060b0310050a0602100f0e160306061505030a0207020621040c0512031c0b040e06010503010605011107032d 69
    0x320700c1c41080c59080d251420081070340d4010700171a44900002006803120351399048080c0000180a000302007082000c0c00301c08544030040c03c0000e12200365840e510a010305018810280c8d201d9109a10304202083c41002c520510014540010400d11802907284d13558440080409001e200c0b641800340b400c0400000d00518804011400f407800c0b5101803912580710741c00c4c4481c215640c0300f51001640308180845c052001a80452606446604046036202585030300c6840c000c4c820509143d461511a001c00400200d88070b030310014048650041514480307401c0140031804002d10429006400090281c1150342c2c14080307980300c1402000c1c0003940309103449003400000d404c840445210a642c2000700310351400b03940d007184850181c070041d49462508050350325000044032018de409a100c000301c4129949501a1141c2c007c03a4200410a81d85440205400c1d50780650040341072007500c010340000350501050407426070f60030900303a00d101c100751500c00c00011302a050394200035503058031020401 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 781402464 1250 781401214 781401233
    0xd140103020f0306010303050a0c150911030d030e030a0c0606031b080601060905060a050d141602190c17030412060603050607080f06010e01090e041b060201060b0304150e0a 76
    0x324002c2d034103801c01c18045010305035620700a00014002c9001407003000b40062041d01c0c0c4e030015901c55600b07001820312805a09003a1603080d03204a4010b00f0403110b0a8503403c04000075015407110789802d01c802c03e5401c80454492042650410800440101110a202e09508000011544001c40d25030714110654944a0352405019918403030103a8000028400d01c20401c0b40203071200180b400b4513140302e018050320158018114802044d1701c4041440d00e652603400018401d0041c2c507242a0280081c800c000d0400d1182510803200780e80041c0d0600100364a441c51310240c0b00d90032400200107910100c0e0324075600560340144181d0034203420480070004103400c594116440386080b5a502d0315080c1d01035802e5901202d5640d03501101200141003507100c0e0301c540c42c4250703060400900b2035440e008011003034241200c0a4492240000003400001d4400c03003c4402800e580c03000300495070621030600d00d1448090000f92884443c03088008800200740d000740e4a0424440c1110340117a414035007903280c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 781403714 1250 781402464 781402469
    0x1512020f0d050610050c06070e0315090309030d032703020313091401050d02010c1b0b1308060c0708070605070e04090308161d0d1a0f1506190c0501020d1401 69
    0x280c04c081c1074a0ba40f05004a0030b81e240542503d0283c6210340c1c52143c2102d10200944d00c0c1075052041000e103484c1040f4601c1003900916442e409550349034410000d01d80340000403000b20341010701c1c9c041c0c020044050010150460205602441c00384001c0f82012480c500400c51801400312103040002042c01031548584015080300035544070903130742c0e24100b04508602a202a001c5104c400e180000102045040da80341148004c0140c6440e869880708203140e0030184000d55032030404001804822000c1003219403200001044a01d040810b659491160046810060400d0380340d001160282c0d00030501c88030040f01c05081007090040038240100030203026203240d02182a8240b034104660700c074124101c00d15024280b203485010400c010b20200f890340c1e1b41c040e15040405241210350401d01d00c2d585028011000d0048181c0c2001d4501c0483c06590141c001e00c0f4090800c80001c4659414059407044001070070000c0c1c4080550414601a02c42d1508600c180780c0b42402580c807036410101f28505 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 781404964 1250 781403714 781403719
    0x6151f050306030d09120213060f0311040e0a0201021c030b06071515050a1710020c0304030302070b03070807030c021e030a0801050609010903080a0509090a050405060708011512020f0d0506 83
    0x1801310f43d400060b03441e62090b0007001d18202e00e000d406005410b0020030403070903001c214400070784103a881142a9403040107070400c0f101e880100740800c0040c50503004a4614080d944081c2130500d0740c9a00103981c440111003130510042210a0f282e184601030f5000150491014141e01c0e80c5840b2443d000f051200c062202142032440c2003140c8110090094100d030a451700501000c52544c1012007041502444c002a40b0b42ca01c41d810001c08107080900284c00603541c130400440d00e0780d04514001c2e08103501d54211510340350043c820000007940c82034410341c00185034100004c1c000c0303c500c022814601e00c1c03d5a4107400c00403105000045038000018580030200d030703542801a98a420801005115034201c090001c0c0380c0c4002440421185401487c4900460500c0c6140044800c040740b00035030300b2a80c0c51400b40e41d540400051001c14024590300c505c00d80f500044640c14425540d419290302260041004090340f88c04034075291684c12501912480e840103030311180311120090251104403030060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 781406214 1250 781404964 781404973
    0x3020309012405060f0409060f050a091e0b062b0b01080103021528080406050c0909070f05070b04050109020a06080702060604020310050402121f030506151f05030603 73
    0x1280042c0c1d4a8840c501c54008009250940785088100010f5411014940d80380c1d00b42000000350a0f50a8030500c0000d02c441d00902110300d1811080081003516940150310170380c00c1c0710100102c0038002c81440904400c05100044192203100828014050b2000c450210500703507032035848107440080c440b000300d0143c210038005510030b04c004565000084c40006d41202404450107944403620014285a0110742d40d6000e10300103122100f4a010f0b4200403060100303506e1002c1c8014000c0714001c0395440a9540740710f529004011010440801c001405401000744084011720741358420340485d82e1094108615400e20305150402a00908104908a00c074010404001800c54041c8a0b002d208032402e402030151540d4020500000c2e40c0010000c0c040a903085c980401c16903918030180003502c02c03204020307142c2d1a04048010740c13022082d01000a07c041000c04000103040002d002d903003d4007124107008000c140c3e00100d2034184041c402507648000d082c188842095100018500c00c420440484 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 781407464 1250 781406214 781406231
    0x9070c060c02030405220917071703060d02040b0a0b04030804180b0109030605040305090907020c0f030115030303240303080a051f06050304020a320f010e0111030d020a0302030901 79
    0x82c1d941e13102c1d40c0300c2d070b0360072030ba400c01e030b59400040d00e00b61030340402518103000c41c40c2070043d40c03580b0210743c08107400d8004400105006060000168881400c9481960b0880c41c40c2000c1340003414480c1c05c0320000f0320641d201d900c122003c1e20b81c0210140200302c0340800320b40303458580c5010700154003e402a416104090011944d1208036401046061841a19014076950454541201401c0300078001c0e0103022040002d017642d92a460241482142c1550242c94a44c48200401001d1024916054401e80c10203600d0100c020b000d2502c0403c6a0f81030800040406009041c8a070b00b580c6491030154040d0040b8000080c0354121840c0c1303105c1c442d00241080a583d5003140847e10764601c06600c240101034100910459002d18000d540090005118041c0c003640c80c1645070403013030b1410030929068118103d0307140382110860b00040301c4d601250858004641600000e0900340503220303140c104680f202008400310014000c0740c4a44104540c2550748045240019010b5402900c0d203010715072a10422 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 781408714 1250 781407464 781407467
    0xe070503010f05100b030403020a020d0b0105031501030203031b07090204030f150905060406090809040c032c060c0a09030506130b090d0e060904020c0105100312090e160504030209070c060c 83
    0x410f44a1100d021301c10100e03e042c44008080d40d080180210305522880c0054009070f507601c3c00010313480784180c043d080c42d903042105050914007521030414500d22240300600050398044159440085400c0f051080d0b8103222420600e001c0e002e074080b200c0e2501c006400300903c8000380f03103008018054105d420050014003601c2040314002c000290032604980003140000b042c64004074007041c0601d000c0da0420305030100207402c440452401101103503445c41e0360500c1402813040c81c0049003406000b4442c00140c040126111038004080d01102e540000350403181c0e5003d940d1000103541c00000f22680c1d880c00300c07a00888603085003801e4400c50490800298810b42c000740500c40c802a50740c0d4408074180e41c43c20b024060b0404241d1a40c040c1c1c0a00c40344c81815800d00c25079200f20f45c6805403141c01451402d0550f24031240e015214100904200305100907264000e04503004071680c0440030451000c80422122806144c100079440f200403801d01c10580e500c49402c616080c0180420040001c03000030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 781409964 1250 781408714 781408721
    0x70507050604060e010807050702040510031115040e28060f0515070201200d030b0f121902180903070c051207141302070321090b06040515040e070503010f 68
    0x14860004d01048013090030355214001c0d103604851642089810641140d0005090f19000c4030042c10b280c0400c0c90420600542010103080d0b50720176a5032030700301080442117881d548618040ea0140700307858404900b80c02000c00744000044030201c91800001d48070300811018110038814807042c26a911400b04191802c1e05c00d2444804000c0d90051400100340d00640305421040e041603d900341a11204540e44803c0c840040c10b2265544c00090300f51440c010800301c01c251150650250210040000400e0000245200e07520042282c03500618098800207000f1032188840440c21f41d204014492650030010207071100b2407145030072400103501c880074820070100b5040c26201070780c400c03071040104403110342c01000241d202800c4014150840340265050381e00c5900c00320b0014005028030f0142c591800c018a4000302d049205000c942000d81320755404140c0540303124443c544d00c1020640704042d0460010604401030400c0c07210406904c4000d454020922030300e4040c2d400c021000c90003007064407 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 781411214 1250 781409964 781409969
    0x40b09060c0703030e0703020307060f02060a02030c0304031428170408160305041a0702120c132a090810110316021002070b01140628200102070507050604 68
    0x8001d401c140032034400302d000e84000c004085160044417404000342c3c5007801120081c100f03542741c00f041d13001d0800000340340440080001c500548103105000c4071038072140403640c101d9010318210241044054061203e48030b011841d091020b4900403000f408c1030840014045c2c00a55150041a1f0800780280b07000c641040b5002001004104048400c000d810402a020a800f0745403103420162114138400e9100051004d00703400190125154085141031008440b080803a20050300b0306035507040205107440d984520b003210464076070f1113810b10003505420950442c0034041001d01d4283c4c22810203800e2050b0360088a1450042c0e1611226480c01030144190195907458514030b5961100855455520340352034040c11030103034403031a1031103006a00160010500500d118030307865140140400d1456560701195000b11000e0140352000e54841c068180541c1d8207200c40810120160400c07200c006040c0d200070606030250941400c429015030141000c588600d08583d105902c50081046500552 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 781412464 1250 781411214 781411231
    0x50f011202031e1203010801050f1303080601050a050906030a050106021014040206070212030a1e090302130902060f1b0d0c05030406031125030207050f1302161a040b0906 75
    0x35943c81d2010905482481000304001c0035a5076821904024000729803007a40320820030383d140d40c1405450001c100c01150403440741f050146003141241da02502001000f0003080c14444046014099580180100c454046008181e42d60f0307407401825160003484280203250041c810400d03503250150892250918100b50351003014a150748550800c403da6100300c00c12a001068030109403d03111040002d005070080da0740b100001c1a041094060f11294004040c0c01001400c0f1810400350b21801e015030301028440e60013040d5a417007030011541502c03c0c0340c04400c060100203450450102000c1403d0300c440303201401d0300c1c0c0003480008116840e480c22400908036030403c11007081058040e40c41b42424103901e1000301d00f880f001d034003008660541000c01041d4041d050b203518081541c1072045d440582812070f181078500d4031001c0403456010348040c1c2456500c0d400554030900c02501d03140d00542590112001161040442d240f010700f400546048400d04403103004101d58440c00b159941c4a0102c6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 781413714 1250 781412464 781412473
    0x60f020301081005062b0b09160b0c011415040608010203060604050603041e030c03080a050709060f050408070b070b07020106031a0a150b0a0e01030b0d170409020d050f01120203 78
    0xfa01180402800d0103062141d2006141400040105031511828084004050140c0791303180c40b4144559900001032000e981500044104151007400e001e2040039242203190407501c4940b100403a5005120a040c001c0b2082c4410301000290003d030403034551442c0d4195002e0040e19652800035080c1e010075034030603520001c188810b0000d0b04120300038641c480d020380c0761800910211000d42644560034541500040d040300e500006060b044580300f6040406c40c50200404d1078100c1d0002c0c01007905020300c40410a005202103803a501c0b94040e10003074088402503452160355000c8810f11540101000c81e0740041000008900798010300c43c850840340c2188541d003210303909410320303034a0305801042810b1465444202c148003c04d41d0100802070520320403055902c611111014042000041885042505200d46200c00b42c6549e800ca004440d841201c00242c4c507a002c2070703a01c1e18000c98004060092020a080c0540166a00441d024001580c0da4540d243d0f200c03000c0e11002042e8040107501030b4003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 781414964 1250 781413714 781413733
    0x80c040204030510091a090d030e06040f031101140f0103060b0a030b0118060e0a050603010b0a0b12040303060b13050a060906170a1e14060f010c080d11070f060f02030108 75
    0x85034104c401da8910502000f00b46c3c0c025286800449101540c01c1c550079400036007194511501441035001040d50302d00100200e140540e10710303031890140e0700c004042000c0d0325448002500c0035080580c41003520003420540345030460304081d4001c0300b4427085d221282402040c3c0e0720750400d251207d0640b40c00c200342c0c3c170440c0c5c01c140c03143c2148d403640c000740c11405681d02c0001460900445209000d441190800700d09428000c04140c00d4802c0104d4043c82002c40800801c0401c8010003121506085000c1a09080e9210708041d801080743c0c3d48021825107000a1180750302d5818400308040c0c0341c2c00c176034192540e03407201421500040c01e4014440400e81d0b400507100301034421142030768404078544010604048040b103014400c07141c05581c5280c41d488418a92419070001c0c881c9a00c9101901d004940b071002ca00022701c417079540e136009000c607000010040b030350102075080021118291492695030b055a032a000e05411107204055035a18901880c01c22041001c1c02202d0480750060024413035000e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 781416214 1250 781414964 781414993
    0x305030115050f030103080304140f0705130f14041a01060504170a150e0f1506090709050d0b04030e01020a0309090213120605341b05010510080c0402040305 69
    0x30341d0480381c000d010060040e118442d03042002103010314843c0704900e4482c1446e2601903910b03400e080c0220b1950300f2040014041c400006041c070304031142115000e4030342000c448100010700e40c0280007000c660400c40d4125240c4510400d041c0207a220381c0b1075001c010341d003030050b140c0300e04203005204c0007d000304000c011406803807580721042c9000f8415503654403940c5d6175041108080200e10302c6965119100d9881d1030401b441989800c0008401a25603041402038148029034024502d61180541c038010640c85403003142c422000e064080c02c81c0c01f10040038100350b0100d54040f0390481c00141c0180016995510129003082902c2d81078845208841c10461214040d421049264100a1240070009000d55402c080120b84030302900c0c0c0001d060800d10005070050000480d101016007420300125810703400241d45081e0100c00b4900105060180380c64500702142d5070401400313641c2420306105030404204055000c41d02d1200032a81c03e440480140005d9000750305c00904203420803144800342c072 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 781417464 1250 781416214 781416239
    0x607200a0f060e011a0f010503090307061e02070f0b012301030507180f08061e060f040209030307050d030617060a0203060d0c0e01090f060e1519080a020a050d03050301 74
    0x40e11580000c0b43c01080003803210308580c04c8900501d10344140010190a0782410341020500100030702e803452461402400d031036928880e000001f8981359072621b003238248610020341429605035200c0150741c0d030280f608001d541e11002d054103581568040c00002200240c000900544203181d07804020042c1081005400400300207190500f8490707414403a40d52803450195240140941080d014601400d295040e49001402003540e942c140032070003102c0e00c08120411055001008641a11010f084000418043d00070013070b086400d4400440c002c01007001c0440c0b5205c800082e42c2c0d003045420790f03038458500b00240c94001c09045401035008101c01c40540d4000307641c00100544074003403004040c2e440d500700d10041d82c0124091031410f80180400f42c142d000310002d04945620501c070803410302000c15011100078040c2d800704100a03041000030303204c080c21080c01c001d0002040c1c41e55555081e0b402e45580444104030f10402c6260000f169500e4400300c4101e400350541c0c1c500f0305680c2411440c5135103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 781418714 1250 781417464 781417493
    0x706030f1a1915050c06010b0c190f150207020f03060c0d0f0605060406020304090b010305160c020301060902160b010b070f2d0c0602010b012c0607050307050607200a 73
    0x1080b03960103d1540420180c00c44407140f2a0754007550b400c90030f50300604140d011b802c10b01e402001044408551500040c20300300c000c01681c460301c45042146040512000f14410003003040210100f40140c2ea0a254040c014440c001c0d039801e10540070201c105902d40404131201d00344c3d1403050080000d0800300e503000b15040f5200a40016100d9218000a0010341080e80608010380c0002400e02003111503014124007ea42802e084c006418496000c422000d82ca80d43ca000300a2121034040665509412510040c4030103c000c43d80c894546241070710080c11514143c0d201c1424000000b46100006c7c21558056000082c2d81e00300809a652034010440101489240c1c0b011541880f54183e2031500d9603c24a100314030300f00800d480d001c806030075594034003400c0303050110040d010003542e511400c103c2c49002c2d8210302001800c6440d000039400f40280000500148404a0340c90200540015050300440c0ca58480c1e03420005079016451080400032118000303504084400d400080c09100007110 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 781419964 1250 781418714 781418749
    0x9080d1107020414040c08070302060910021911100215060d14150412050901090e070302040801020d02030f130507060c110301021602120106031e03050f0406020706030f1a 75
    0x742400c10740000b42540d200050149141d00c4003400c0c001000500076102000700101d101400c1c880386141c00003105030148440703040c0030320520100342d840c891090003016003410280d19108010070440c1084a04d0705080306c4280d0007410138800c0c640c13440b8000501c01c0a901002c6000d00c1d00b41d03452006100c0718010f03800341200c0d01101100d42080a1600b0700c0052240b10300402801d81628150a10511601c882c00ca50b6040c45000c010280099034001b054105440d803076110701c005505c8a480481c004c0c0b00e5a1700c00990307540f000c10030004c2030400f60000e600804103219680865101d0b8520802060506180100243e01040342046424045c2d41056401c5000d44120b048002700c030f401280c2682d100743d01c0300103500c4603151510114a0102010310b01040410002c0204a0442d958001510091b2100f0880c0e249010b00d0f88082501c1170044071100003400d0350071611a40d481f0800703962480107014400100741031400c500071065a503c10407031891041c0100321000000c140500401e805190203c19 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 781421214 1250 781419964 781419967
    0x1404050706020f2a0103110a0806040507030c0206070c03020f191202010b0d061a04061e0602030a2a061d010b0321073008090d08010303140c0105010611010f09080d11 73
    0x1000343c12030b4040d000c8c07190147c8032020203240c864100030071610010240401d051a201030040266800546244e000720b06084c40c14091200f410b05a14001444154003046d104034490303048082240c1910a08031403044001110381a0320800607800d0f204200d81407600442d103481c1041c003098140d003150500c0a000290109408803a00105054520300e81041c1c0303140001840003900780d400b19088000a00d0180f01460500005d81070040085403912520984c0c0345440781c0484858203111481291241c0c050300c1001b220600b4111003040340349802c00f08185502c1c0840080c1c684c2030200c2c40455500d04454607240095602c04176502a0b004542d095441c0d86280c6003031188000c9404144907800846901d241c982c04103614001c042040051110341140c010b0301c80311b5140d83d00486103606503641410030031040e010300c02e034500080c001e05074881015030030072000180154005035008468201c80000344100240341c014031007502c442a00080c08000c0400c851850381200354442c005041c180c81c1942d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 781422464 1250 781421214 781421231
    0x50c1e0405010605041508040305030c0a021005100f0611150702010b0a080610050a08120c1219080a0e06010614040302030f10140108070501030209041404050706020f2a0103 76
    0x3400c480098014a0108100007010b000d03180209840303240c41011032078528514509550002c14500020b01031800e801e80100b10003659500030701000448100911041140e4a02400c01001c4000d0601c1540d8a000300311002080a034440c113500040d42c2c0c0f0000090900c00844443d078000c0700c0004201c4002c40d542c480d0310440c29504c203a0700070003c120f038800402441c240448036201e401601e601c014032034803000c4010844e614000c540002c03400b4054039010b0b00d8000c540340280c200005a0282885c401000480c5204000e8807410410440c400ba61400c0e030540e501e07143e22003120960325944109500002c0100311840c13050010503a114100c15040c0c0c01d03d5501e6000ca494210001c0d110030ba1a081044002e10840040c0b0a14a602c0c1c0c00500480c0c00303500d0640c100c0c0e1607150500820381010b0700011004441d80390340d04080e0031b103070200f0701030805468a41810340d210b0001d4020301c401400380c1c400707568640c140014906075801c82c0d024081d0710707901c2c010645075100c80c00000c0c0505240d15015072 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 781423714 1250 781422464 781422469
    0x50d08150306090109060c09060e12070e010305100c0c23030408030a020601150c03050f160c1805071d0d051c080a0f05011202130b0604090e0601050904050c1e 70
    0x142405080203c2c004180203210380740100958140044150410603130381410000ea66101d0001c03035590105079250300c840710007040224204620394100c85a4a05400000410030900145400a05030201d404020f003c000a008540c1c6004100014064442803003d4880208250840f000703c00b060004407882c0555600300305045401c200c101342c1c00758000000403c02891a444460103443e094642110096010354026004e0f0140706c03201c03008840d0100701086603030387c501000e491441d0481c086503c025039469050640402a1485120007070900c030101c0c920600600280580d03143c0f02d101440b81100d14014080e440a45040542c1e00c0e10a504140d41d1604403403c4840f1810001c0d07580001c5441c1081d00707401620480d8160750f4050780343c44010010070a4000c2c0d60442254100d03409180300039503000305805088010034065115800107400180c001c550f6100c111a510800f080e910140c0c2d84804124100000b15406011031300203444076000c510b05003041b2070040303044c001d61098215903a0f01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 781424964 1250 781423714 781423723
    0x1715010903050d0c110303031e090115090608010c0c02130e10020a0c030212030903041406090306090d03151a2a06060901090b010e04020a050903190c0b07050d081503 73
    0x260400444c00c12200d071414004c40d0030f00403544030710035002580703981000c05c2802c0217017280501e0100c8001c4c092001c44d018480c00c2d0007035400080da10b0186c0810686842e0380000812492052454030340c81c140c03113903031001d0040048000d4160000c1014003900c00018402018080c1c40080c503504d070080751890404681e292004d840e814420340d55031841c14a041c50084e10700303d401c1c2d0403489800400e10400c54102030010865080e6020070f01e40000300c10140c00441c5190042d0b1949960500800e010451401c1e00042c50b6090581d20380d50510160a11109106000d038035030085500115134421a17207260858140100000a025613a0720030aa0010414180c8a0401d10441100342c200d5000e201091400c60314090140c2820707481040030340002c8001a26840b00648580e0185401003804001b0030300078419240c2c4450054241d960954181070b100c0b0980000e000101c80e40c555056020130007200c03a000343c44481e903100000f400c0c0308142400c02d0720642c00042004540a4205894041ca07807810700 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 781426214 1250 781424964 781424983
    0x3100302041a090903070f11120307050c150a270b0301030309050102010b06091f0201150e0a0c020601080703030302070819030c020c010e0117040c080303070c030f171501090305 78
    0x20031004089070b600042202079100074013880a2030f80180442008a00c1c044e441c1d00320b4a0340305007034140c0303d81028040703404424030107904800b41c00040f40304000d11601040d80c5003c904101c0b034242c00b16080c03600002c038a0045401000c0000e40035081107014421156150980c44000545034049555580c0d030030881d940240c104400080061004008650b024041c0d40102402114a603040103400e20100f2250b4000a501c400c0c1d40e200c00c50100d2200e4000e40c050387d0800541d0f600c3d4207a841d11a0b8902a0a1805591000b561440d201c00c902500f0710208110781070340e880d100030744000703451a2002c4004e0341100310151070b10141000150260007200c1501d604003009500d0210300030211220190a00c0180c800c0b10f4180700c12002d0740402c03a80d0281e00c5404603401c40d00700d02c0312174460b403d200c0301d05407030380d04120803074400007041c0304095400c030910088142c441c0c0da5080301c050010700101c03000282920b078a4010031842c00419407151072140410a0407906142c03005009175240c035010b00e00203184 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 781427464 1250 781426214 781426241
    0x90b1b01091416030807030305071107140108240108190c2a080a030e1c0e090709121202012d06060309020625050f03030a0e010c140310030204 63
    0x51040700b40031081c00040300c1c81c0c070001d07110b91410b891a25005010311071101c0003000c050340e82d0000744206005542568007200d60100304c901240d00c45003000101205140c546010810007800100d4018810407150b400d50541c0d002d00001c2030b05100152034801e000b400312032802001c4003858100705110721441c1c0c1062540e6640c407407009040c0031191211038a83c3c41403c1c18441141c0510041224041103c4030240a4a00083c95555a80540e8103180a0005007c0241420030704545503540c8142c1c100920102100c8a141070388959105a4130f00d0850720507003100d04540500a00814107a03101c0c10708000070b5000225124060303600b869058008480d41001120ba079440c4503000601d1803107504050415810104002c4501f500045d40300c5c001c00c50041c4801c041801440d03200ca80c081d07401b40c10039910000705e800303601c1c0003d1143d803070750800ca43c1000968640480d106c55260140030301c2c4c406211030b4440c03006c5140911100003c0740e000404000700f00b5804031000006071600c1c49119129140d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 781428714 1250 781427464 781427483
    0x20703150b012606060d060b03010b18092a040e090105101d01030f050708070e04050d1b0b070e1302041d191802090406050f010f06090b1b0109 63
    0x710300c000f40550805401c0300b00d10b2198420311110401034080407a80009040300c001ea121003507a8a004040c20150304207124031a4040300004d0b0400c030364006411012503002450030312042c64000d0001540040b41d906948580243c00080c210103540c4202d8807000c1c10003240e0385400c4e211002c5410042064a0f030441d10f039998010044c04140862004002c1d0400e100e114000040c0892801e1030700742c0c18080a80702030f811080100c03c01400b00900801098513038159403241c1d40e01c0c890813145020454080da014041c02c03d401c0d40482c03040c0d43c1d01110003880051040d440340c01d901c0d43e560b21600142094180038445000050643d81c0f0a003e11880108080241e5180e040ca9134620142c034141c0f048090f600c00c48018844250601d0031251941e40003060001000c07102e900e240d000d000c01c41c0704041e400c5a40b03042403209002c40398100d180300751180302056080703990f2030900300c45121032b911503000002c140010601c06100540c0c000c0040840601c005460340580103915802c50b030550408803003c90b00b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 781429964 1250 781428714 781428731
    0xd0f0821010e0f0a11040b03220b0718060c150902191707061b05120a0507021906050906130302090a09200f10031409160b0306030a060c02070315 64
    0xf0700342d03102d55100e0300300e10082c8903102c41c0d080384506900882c018814840310110000e0407015041d84c0511500140301402901d5000da810012002e036410f503420740c00a9654044900007607222000c8400b20b4445d0b40d9000601f16032503d03a103502c181c645c602000e62035243d804100250b0b0351741e500a0100c5a01c90110a0314914000040d944403030300520151003500455801c0000c00d4220302040f40b000240c103451090f48165103426400e002c9603100050036000c0c0400c200c202c40f540b1002801e04c2500c00d40f05400381080c80a12240901031521a51000600800002c202401c002d00600342c80780b42c8100e801035041d1242d00240c0303c001c0c1111016403a50341d6101304800d011008003480104051404107000a800c03013004200b0a0044d00321641c065032144000300141da01c2980400c1c4100120307080c00995003882d1a03081c1e00c0342c011070b4010041c44a003074804a20794940c04102da0280000900404010066590301805030020b09080b03030641c000d45500001095407080042c01a189002c0300055041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 781431214 1250 781429964 781429981
    0x6020303070e09060d1103030c0319090e04050d200a050a02100903030e04200a02010b12120d0c090308160203190209040321060605180d0f0821010e 65
    0x540104039140f10b001600d092000540b00d1940c860b407001d811801c02e1429054800101e80f5500c074a850313904841c44002200382c02e40c010300e41440120b030034070b6581c08805503586820600c0307220181e9002d003042d00180d00074205513000f0b100146602011031010001c052101a2540c01d010441d48280c5070707034000b012000b0843c40d244031215803942031420980181c0e42141c8000344032040c1007954500550b5500c400001d407607084080742200200010b104d036075800b0f5081c0028041c003a500840c6000304070317071135412801c1d07400403a24480c0380c0d01d400010b90070000034000641c0544807889a0070b051110410000c0b0128400000a169080ca15a05604003101070b06c140761501103010380300080701421510060040c3d8442101c140c000e509880d1150088030941450b45546100320031150341e0398504500000d190345c101c0064190130092000903070300c01c0000c40a03c040d9400244005010245003064035000480980c040c28900a0742d980500c0c6500b03040b901201e1307140c0d080e0007840050200200f000f1000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 781432464 1250 781431214 781431227
    0xc031406030607080a091104090503090103050109020f1c0f02030112050d020102160b04020a0503030d09031205071b03050d090b0a0509010b10030b1909020a020d021b0d020111070602030307 83
    0xc102640200141e1420300301c01007a401024240048550303c51301014207221100c00100b014240040c01085036981c54902540c1c2c0303903c442202801710b410080005909890380c8244c4208146801c101490400140c1d500703004865400000004103940300c01e020000c62451001d98040c3c004c0c031407000d19050445c18240d00c0c048084000c3d20071607004000c0e5000103a13a81d00000704140c1e0007100001141c0b902e02c0010901107150b00100c0d0507100c0071581d810303541300c250402a1141c0c06600e034030840c5640c0816460940d08111b42d400c0218010780c000341c00c003110503c10101e45500901d00541004a0b401040081c1c99000005840095441c1d0038041000780c0751081e980c20600040080000c440350001140200201045440c1896500c08034084117407509000d101550401d038105203103660b10741c085d4200941200c88880c0041c450101a110498000542114031810b80c42d805403800d8291f004004100b032001c031080741000315000011010aa0401040000e0300d1507802035500c030303c2c1904005000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 781433714 1250 781432464 781432471
    0x50607081b040f05090a0905010e03031e04021005071b090b04110901080105090703060305100204031a0906010902030a06030f120e06090f090c0f0705010c0f09030b0720010c0314 78
    0x10400070441040b2000302050740104443d030030b48a20f122035842c003003040c00401f2502c0c005429542000d100160078140030008500c00c1c41d05600c400c00304070298040b82e0fa4501c040b54000d404c103080c0c0780c003050301501031400f91512500ca9001d0407030307885c2e00385044624034509034010140303a500e441c0084d9840c43c050007550b0b03102050401c114140401000001c106040610802d4015180a8003240c88035100c0c1d04000061a08202182c6901000c80c501d84000c0d0701910080d5852a041e05140f0706182c10121040d0007010400b000b055581d00705580000254005000c0002d2a0380e15980000060a804409130310240500303509090781212810140901c0080308090340325110801144420b86e03101100300d41901815031b800d1081c0d58a02d80c82c05618441e03003050b1640c8000200f065810028150040c8282da0608e94500e2505e22034403405465003040b0307010060125150f24000748000b4421382c81c1c0440c20710040744070340d0510013103010282152a81200900003d440d101448000000b00e68003580 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 781434964 1250 781433714 781433761
    0xb090a060503070c020d050c0a03111305010b0304140c0a06020d09061b030c0224180102011b0305040c0f081e0a0b07080a1e0209120a240905060708 65
    0x40c5243c40c52008100d0b1840c200001c0c4100700240428091117410400001c41c1d1b4400f610001610b42c903410500384400ea86180c0c1c9100704010841424910050300036181242e09007000b840c06d54807560f45036030003140410242c0c10b840c45500c0c0c002c1645e6403078040f0000100b03119009040990704020300242036000b590091024001803041d650502c40c580f440388000c0f10b40520f40210f20320400c0c80064100c2030003a4608080c2c0c003a0032090747d03074400c010000f080c5400070a40c4c201081c020010059081c0c80951800e8000350b0403180c082c0e550b89000b03400181e400fa11414906003580e450340d6058a5034541900001c42d240e000820b44042d01c1c0800940f480d000503160018102503000d0f90303031406001402030216081100340004901c0c1040c494004620320360510065410301d4420840c400025004003524511402e10018000524000440c0c6a004940c11412000d4142410f004183e07107240c00248641c0b1943e502c40090f00810320501012740200099550b17120b41e4200780d01003c49481e80b446400c02c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 781436214 1250 781434964 781434967
    0x71a070e0411031b040b030c041811040504050612010507030f2d0b0a090609090c0611100b030a050f0109030905030610060c02060c0604060606110d1d04150b090a0605 73
    0xa00c07040b0756080e60352080c0c840109128241d01502002c00c10300480c2c0c8074454545000c02844004000e03080074000743c0341e40308861010039218400f200261421a038000f080820100000d101b54189038000a50100003c2c1c10381d51071506e81d005d03240c03c540003190003400095135070b42c910b030300301225005207002d0383c141244401c0050040102c90a44024048400303c03060782e9001030141c6500c690030071030018503440e0800c101d6107a68145a030050b1483e20000c0300c1307400b520f800200300d00b40111018000707054400000c040392000c0d510300300b0007441d16904172076040c0b180f1132982d00041c0040120312008410074002081014562034003506004164101354402c0d0049001c00001c02540f885030f10440755145001c051000715400440c1c1148075000700900203000310390411041c043c15400010851304a559640c0c14680d01c021155200c0c1202070f20203002841d0544156422400d4420f000c10400008000050740104140380c070f0603011555000e81034040011416100c2440c085540600508940c14482d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 781437464 1250 781436214 781436231
    0x5071a040e010b0f041220100512090a1407080114090d0f030b0d05010225053301061707050901050d020f040803070c06111b010c1a010b0c100c0c17071a070e04 70
    0x89d02c01e000b001d15501078806204000340c0c00c1c007c00c1088515507030300001118840807011482c03648070707846401009103942c20a842d526046000925241c81030034500090000e515042c03074100c401c2030707403200c0400405031a5440b014040d074500e501d0a00b064400c80005964655024540b074030494100340351502045001c128101082c004070f03140721020141c4006000031820007031840200311070118260900c40d104000456411b811620f0740c035018107921480106584c03600d0044400b8466103050078002403082c44091000540e580240c034460500042d183e0074161a0513401e46140c11030042502c22000c50041000740e0303600004e0510302c0e03142980140c0310260600140089030f5a0080380541000410070fa04814809114410f00092040c000d1000c0c43d56540d000f003140c281c0bc9420703842041d010b40964030303400c41403e01c2041490311080d113034203281d20307102c0c1c807200c0c04070000800030107061200f0001d103000a5900350098120b010040302d1100c2e1400c28400003400c110404503120b0140e4601402c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 781438714 1250 781437464 781437467
    0x81f09021b1915200702011818020a02030f0f03040b1e16030f06090c02070506070c0b03090f12071103160902090d060905071a040e010b0f04122010 65
    0x4402c2250802c15896111042e281e6420040005031041000200c146043d03600d200000b10040a1150003607132103c00080c010500b24001019601c101040107001202811481c0d403660080c00882c0c01b0350055030f003080d54036001c040940e80000c02c1401034260000c02c02040091450105400119202400712903401014110314601c4000e04800180e000e00040030662902c01d42000c0e038540035030001480984c0d0341d043c0700005001a4000030000d03001d030410114060074440d003079607072064025207410b19440c0744ca085807100c0e0384040c016040e503015022004140c1c00040103065001103541d40c0c03041e076070740041c1400840101c00f01180d0303200303030040c49480f810381080b20340341ca080e11001035005988003040740014840d0f6020703140c010300d010301f400e02c00f8081c410040f0701d15044410000b0441e80c0042c04104c0c080152289010b9080e807040454018010f41d0120006070005003104180949441d031901c68901c1e110740154421182c24803d0840a81c090602c0012410300f200c0030356401c0c2c180180d40a0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 781439964 1250 781438714 781438753
    0x201060b0711060d0f090b060901090e0a200928090203030316030b0d03080a05150a030f020a2409150507030c110616060b031b01081f09021b 62
    0xd046100f5000840c030214209629070059201000010741003042c0c10305441c0c0b8140300b40f811280588214890300002aa5286078040c002c076041a1101811541403150b130b40d4006104480ca061800c0d8502c024020f05688a4090450060348210207480d007443c02c182c40b20820142080b01c100c03143d418880e54a0058400005581c0c10843c0c1d03408864548020340c9080700281030358009182d002c6001082ca0781496080604140a030240c0a401c0c0507565410203030540100d00800c0340f54121061711010400320390084130001215100030110113050399164544001078460500740303040fa01003640000301c0a40c020610800411030b54041e180c8800384803071b010f40117021341000907041c8142490f90404209000306c0c5c2001300d50b0003d10b10f41d04c400480c035190850304142401194194902085800340d40b42c00107a220500c0f07130b80003000c1c00c5442080011150550050700404a81000d00100e0461a00c51101640070f0301c150400182c654503031003076402c1c45904c00019005a500110003500800b100c1d1507 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 781441214 1250 781439964 781439993
    0x212010317090901152a1a0412050d0905031809060108090303010b09040905010606170903090d080d0f1a040606080c04030f020d0605010b070c090506031c2d0201060b07 74
    0x10700240812000140aa0340c6c1c5000c1c0d414861401802008142400d9640c00da026a0500854403146100d600f408010001c9a060350090140c0c0c0502100d5082d1031710030340041c90300c0043c003100802d100c892940c515113960891001c0a900300317400c420f8800107040034500c15901441c240707004010360601e5041c1a07100d200600608800c40c10000b5805683d855580080c620554044020401070b0340d1b03090014a40d61148020155404a04000c208501c4001007500d10b40c3c0c90040c20510020b12035a591801c7e603101c6510351841300d48540712005409114404d0102c00e00341c60940720000d01c04001004111440b40d0403020500000c40d007030082808140c4203860079207501500c0e0304882c00503800090500410154002d003441d042c4400400d58800c660007800c10317544100070b003035600c54440d015901a07407021070388035403d54494032707020140a1151141919180381d5040020000c1d501684c0e154032414001c6d901a200c0410f0103402140580c244940c40042c6111031015080c98202e40c2e80780940a000c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 781442464 1250 781441214 781441229
    0xb030126060f0a0b0111070f1e150c03030b040f0e06090a110f03010e030c0c1801030201050915040503100921050a180f030f17040605040302060c030403060212010317090901 76
    0x2c004071944d0713074002c03049002d030a1030744405c44e4131659850104c245070120301e004140c441d85411a400500310322200c07003042a41c1150380b0050350704000c407004481040c81c0000c2501050f48a80c81001e06803107902c561810405281008a120103201c00b0803494440003400d14003c40d404285424086035003007495442c280f404440710002c450b41c0c4400203024184031080c246040c0070024405400542c0000d81c2600c0410585913001016a1401d10b1342034400c0911004c1d011a80070454520706290402d4856030b101c0080582a00345502c13500407a00d0241c4c42c100852489545074105014401d40b10742620301e01e002c002e03409045828000c002883c60103540851000c0c4034007051061070b44940406400050140d102c00c0800c00b66407410722000180c8034180a40f411544d52210f00294160350382107400303582e42c07501e0303d618040c69a42806550b070701002c801011404103000100002e14940010543c0c0300d00e1341c00c11180343d4150300345a01c2000207511840d071054010001c91246440c0c1034a0f1a04480a6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 781443714 1250 781442464 781442471
    0x4120f020a0b130b1c05010e0415200702010c060501180501090501060f050d06030b070c120f09061107030204050a0b030f0606130f090c0305210903031608040b030126060f0a 76
    0x45d6503d6810b00b0a080072804207050400d000801c1040742c2d034003030358440d0f405101103040140109042008a07508400340750306081d01c0c0d5821800c100d24900040c41c03542e2040c5005c1519100316120700c0d04640c07080c0c010740f58505192241140102090040c030340900000d210801495140010150881003281203140c14000c0106950010034040e030b21007001150800303041d5442d460300e0000184500aa00c90490b99150001c00310500d1521503c40c2030307031003010b54440c0c0c000d8604154094800410019040ea85807084135000701c016180c1e805201c1c06900b41550106a41036035004050411046420320303403550b07101d0f004024407179403408201d03009130114010004007400c1120511000d03098000000e0000000c0040010801c5000a60450015070440f1030854001d82c0810031038a511405d0400e5616030301c148480115004a41940980c80b40300d80c100318a0326070f81d01c1d20303040180c0007680542400c50160802400595014020344092540540901750340d281420702880c00d940b010701503a0f002e555 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 781444964 1250 781443714 781443727
    0xb130b0a050a0c0302270a0312020a17070209180a05011d2a010309060603020402030f040b06010e030312091903090f0b2722020910020a020312090604120f020a0b130b 73
    0x1205101c00d8088d582224020070300c580e1408000c3d642e2020b041045482c06e080701c1d0481c04ca03030942c109481d0115030040c40c0200589602124482012040c500c40a0501624402c08001131091203102ca01c0030040920340d072140810115542400720303940350f0701d14000035502021348030040e10101080c05242403d000030804130038106540102010f402c000d4100e0300c00000e00c00380d80718008440b4400e40c032419100c02266525001100c030700741c0c40c0000a41583c004d100280c124041c1c049896880142e510890b4907210440c591040301080c884015000700b59950411300840091003d00c6c0b0241c900e04140c180340841141c020340361141c191001100203070100400c40d0309540c50304081184c022501c0c8000c0303c2c0c8112160000000d501c9414610700c03800e41071800d410701c240042100b01c03090342c00501030000380c1c11940c190804c80e8084182035503c01010400420303094090000301a103140034142c0305450031071620500c40000c150b600490a801414840b42c0d000c441140c001c4800d6400e040f03881605ea24 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 781446214 1250 781444964 781444969
    0x910020a02120a03091718060c01091a1006030204060c061509020d0e1b15030403030b10170609060a090b0a0b070803060312160b130b0a050a0c030227 66
    0x30b503507201d0208850000a5102c0b01070b62540002c030065010316092008a081c21480408a1103030804502c0107040c410300d00c0041c1d20b41705014003030604c00e40d400440c80314401e030b84038286003590300d10b1021159045401c0c032100000c80071401010307000e94102180382c0b0b07082000180000a00410040015840725031259041030b00003000b1004002d414400e41d254203200c542c1c41d01400d05034840034a544503105640003a103000ca18251100600580041962101c00000e8240b40e880104190705050322410700d5030042c0c89050526228011a42d61290428444407850765100c8000d41a148591403403000d1241c6542c0f8030b800ca41c104d585191000840702c020b6004103a580482da40035049218020440c41c1c14001c11000441c0701c3c030000c03002da034400442c8003d241442d0044030805684009241458000255902c2c1c0258104000a41c40b9500310410361301c0c881560021200c0b03800407601c0c4c1003405440761541c041c0040c00002414107504281080505444001403000310041904402c08100700c00d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 781447464 1250 781446214 781446223
    0x1e0405092205072403091a0c040b0a05250b0a1d1902040612200f09190b03030418151e080613151109030f010e0c01080910020a02 57
    0x591000941e001a61382e80d141c0301c40044842c0c01d40c0c545805407101c2020391480b034462200718651280d1001245615510107411806000f030002c5074841c0b080101203080804036001d86813200e05503035060390b241c4d02403425400d02000380c4055041008103d90000c0090030b4280c1341d541c070000315240098240c00080e83c1c03602c1110310044003165405009030780f042241d103003c0c40d07403c1d0900980f01407100c655551044030b4a804d00340800342071204da909000c07041c069003020942d0f018078018400c01341c6e034a802c0d0000c0c3d00034000781e5094492090101e807141f0141c1c8a4020031a02d0002100614106423034542401c0c00c001c0030328107a0018680d1040301141c0e5242500d000c001070004880000b00c60020f01a801c00c81d802e00f405451424460b0b880003aa0144881c000010326903840000c1020008030007807500301510100d803403400074070000d201c1000b41d9180ac01050310020850310011070144000044c19040510394603504c4d040011002c01c104c2e400900044102200d01a0302005a0b40d03c80c040040b41072 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 781448714 1250 781447464 781447531
    0x150405040905070e090309010c030c050703020a120501050c0901020a080c15070203040e09011107020f15130e0f07020303130c050301140105030d030606022a04050901021e040509 78
    0x1241c500020310042c03200004007442940d00c0181100c071141c80702080c0c50b989000d044207481c0040c50742607103007000a00ca0590380300700f20702c500c0884124070b0701d0340c0c0000d174103165030380010a040c09400541c1080c02000d02032543c0010072181d1080ca02003101c0300003034031400807440241641200142c0c0541d403031030401030760140c181d441d143e003501401c00c901c3c000c2d126032091041a03280079180b070200c0c868070350606c506e0413040b00c40b03010985000159801e000e10180c148040c80d501030710881c4980b804101c101e0003481c0c040d60700c4c5240c4640130704051604507002c03c05440100f070918040100880350303800008491304400c00600c02494282e0034a0301001c1070b0120303002a034240d42454003d00410980c01e2915061b40c00c200c040e2561270741c010104500301c030094420b0800503848a009501d111f864003c1d0120301d80511040b1840d00001c110120b07061b641c060360341000c1c0346e50026415181040c5c0e0202c1440c2401d04e45a5285441c0c0b07010300141d0310800241528404440403450407445022413000c0060 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 781449964 1250 781448714 781448719
    0xb150405191802090306070207060909050c0c0d110d1b0204021c0c0c06180507060806030c0604030f17030f0708130b04030806090105061c020a020115030506010929150405 75
    0x100b070040700b11019400685400d4002d12031600840c044d180003003044010707a007403582e0b0700340900d2070150034001800000d8042c10740c1600c10400030703001e41414050180710f800b0688581014110300c203103803460002105031540411400c071100d2130702107100781d1903001c10315012140940c80310f6500c0740341d0a07124001841c0200e034602e0004d82c0702007103400c0a031104041e400384d02e0802510070210300c10b81074984208402000c6802c840303000d102a0f80504003003a0001406001c41e0410303110000450a50750003a002541c4074202d0521517020004207985124140703c5900c140c80c00c5040c000c6900403400006800f6038103000c041c80c0001e04003006c4102c001d40c03c6030041111812801c007414090700941043d900d03140221841d100126036401c01c50b04664048104290b41240c100180007184001e4001050303030b10845d5210b0201d9244403800917001e0018600900c050a165458407100c03008a540c04400401d01d0350f0140050143c0c0d10303000c3d108941041090342e2a0b02624180d25400c062031240350001369 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 781451214 1250 781449964 781449989
    0x2102040e06010905060a0501030b01211e0905010e030f04090e15010e1e1504050411370302060403110d0507062114181c050a02010b15040519 62
    0x1a03d46807078000c0c41c0210341c1524900c44a984034401103007902c480110250100d50b500c02441010404041c41451040d005040000c0a0300680c503001088500c0d030f64451001901d4071019000d210081c89082c40090803c0000c41ca4120487c40386a02c0d0b010310b20620001503564004034496440501a0021041120a0007140c035a1500311b1500100b005440d00200030b41c0d065402092049189103090213080310f84c04040180c2c0e1074000b044040c00700200212800380355501c42418980b11058089003001238480e00701d0013034200d040110b194100390081603115188030442080940c4800d402c0301d003a00c4d08141c01a50000a1a020071000140e04900809034411610f0000b52241d01141004400c0c031208000c454502600a004040e83d04d4514102d01000c1040302140700141c444540c100502d444000707858840d000440ca110082c4411310681001c614002020381c0b6503582841410051603049980e01e6102040041d0300c3c1c00c5001c1c0d80501d5000c0d040428980b400c074103c1801200c01400142e4005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 781452464 1250 781451214 781451219
    0x70311100f050f073c02070e160c1401021b01020c1e030307082805010518070807030c0306050406301e0c0302121e072102040e0601 58
    0x10003030007100071280301249000c2c0498142103082c81e07181c2c040e044503510300405e111100c1e00c150b10700500c41c117400010080138031210200e0f000d5001c10a030410a42d009816140d2400152000e02d0800030032114002d6418400740c0c2d911504401c01464032504100015821205510554028481c1c0312004070030200030380c0c0701042e5030320540041002c00082c4050301e4000030001d40c0311110342c49a400202094009100141c4014428907555078028214420792040102c0384441e880d00001c101444450180c890340180f00c5030030003400f00c051118650700303203020600e4155001406601c02904a000701621444c0c024001031080e08400701501e4000c0c03080010507074031554240096801d1624000b103440e107600d02c0742413240e100411090700760007011403850414a048138000d001000c03003049036240e1800341c0110160b16010002d40d0380001c038000600e4846561565a900c54080e02140601c40d4007200c01800000001154038000020f87c1c0c0c0005c601d80795a20020307014008068840ea00b030310655000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 781453714 1250 781452464 781452493
    0x3061706090c1c0f050717010e060f190507200f010627090611270906030a030e041b09150813110d0203030c100608060403080c070311 59
    0x400340240e01080444046680441c28828510b915000039075100c04640310f240007040c80412a5841d151003281601e002c41d0b1203451800701424040c0c0d841c0001d80d500c5940c205c40318010049543c02000c1503401d0926403030f108083e00c110100800b82030021684610108200600408880307880350310514001c8070710740342070310b000759030b0814410b810f8119030900e0400181c241717900070050f00c5412040004602010240d481e4405484540421a1400c1d80d4403051000400031501070100d18840603601208001628201c1204002c0321903964440d50f2240c01707121055400041020038641d2504164407091903e40001e401010010304826201660800c03504296521400d100190f40942000710030440070340004881200c002c0f03412254502c44000850302040d00340981c0da5410b40000d00c0308c030080400398042030030350b042040c0490b800d0f8061140075940000c51b005042c09486881d00420192a050703c00405101c0d0243c0040c001c1d04000410782d082c0343c842c0c1004d40f0030a080008948588150151 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 781454964 1250 781453714 781453723
    0xa150e0a0b0420251502070605060a0e06040c0e09010f080d031406040905010b100206190e0303040803091501410f040f052d070c060c030617 62
    0x4514032075440c1000034680070091140d08010100c0f20703080e00c3e091400020502c030141507200380c90000900740c0d814540014041d0000d15021030703452040540c5400d00c510b012416034001070851442800075500030300c2402e801c204c0c46e036804442200c001ca00b403a18400c0a50b02d18020074030003a003102541e4000307d03203040029804c4045580308001c440c034503001030134128100e0362542d550503040c10000d80030032a02d1400e5001100c034540248000204201004001039001500c0f01600c009a084801000220702c103483c4520403c1982c08030601c1000383d00750020b6103d120041001303151880c00300110307070780710410043e0b01140105040c0b00d0002c3d5860b2807405000d0072800010344500320805045000582c0341003d03103000c00300d00346030f4150401d14170420007601c1510700c0c901c01d4209030342c0d045112338030350342e405501e010f414000c5492040c6c65848110a440100121000c6055013907841441a86903001480e501d09a410030700010303e042103958103e0140c10558003250711000c1d01c11803403820a40228 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 781456214 1250 781454964 781454981
    0x210f07060b012303060f0604091b23070209040f0506010b1c020703020a0f02031f0603021905010203040612151409160c0305030901020d1104080c010c0b0a150e0a 71
    0xca40440541e195002200710400c5800500b200490134008039a03203003000d10780c0c0140d001009206070b042a849841500440d42b9031290b09000c00340010b1141c00705a0031000211030301c1c0014000b0000d0f0211804d1000913403003801c0340240564a000d00241c1071211030b0400c0e15a80368010140c03007480d41e54041d48002c42d04030400801100010300b910010112661088594155058000d0032a804d4a502e801d0840488441d040e6090300461a01200700c0d44c0c0d2261a10074040355100019540d8154011320184146a80603050420f074400401e02042c0e800000790740031070b0024a0258500c0c00120a140094500d90760131b12100d1b0580072010895801b00e410041c030034101610200c43d5582c0c1d440c85940c81203c0580b980c2c01180600d0b50210200c2d106400031548200d420b0005403910001100c501d08943c1d03e01b208040400700030605128021044c401211036550918200341d120005898120000c0341c0544198030701aa034a404141003203040349107400800d22070903490040c0c64450310301d0707000c1c0c003010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 781457464 1250 781456214 781456217
    0x40302010b090f13060902030124090203010e0c0a1403071d0f060a050c070305060103030f0f18140102011e020310050a03050c090402032506091205210f07060b01 71
    0x2011100e0305081800c2c000d8420b07400c280681005032038041c0b08800c0c20030103210603200e06485801200c05030700c1c2401052855145641c00c0301e91024a8004100340c0c403060740100310791030700401c0100010706081c0e40d440c5e00300038130004480d620800c0b61804d0710206c074003281600c44240f01204112410750407803540b440b04020004548014090b28081004ca00d502c2c00c1400d522040600c40c20301700600c10009401860b42186c01c49020a89a44480303140c03840980c006c40000e035000c085400d401e0313800003000d40544100e0421090100d0300c0c081a072900c1c5c416004502c41c000070030b0304080850f80700750001c0410701402e4419642000c54811040043c2d03000729218503010300c503000000f80d0350406080f1b02c001c0700d801c10081d04400e0104d0040000c0c002005e002030f81d06d4070800c490280003a01100c009500d010140b0120700001c1e18105001d040300301d45601843d80503826250807800f141d4049202e0a4107034a4103104a80b095a0005200c214000c50001c480c0705180864002d00304461075014140c0e21009 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 781458714 1250 781457464 781457471
    0x60306140d173007110318010e1f0f020705100509060d02070b0901090c090c020d0c080c03070f05060c030105130c0e040509010c080601020715140409021204030201 72
    0x401080c400d0012001000400070581050050b4002420001a0607005001890206411088641041c051020003003a204001c1001e0034003403801d82100f6000310454414000e14108a50108200e807403440489a00341881402c0d80b10900307580ea04c01600d082c6045030000800c03540314400e07004160b4001b800c040c0b0054490100040780a28040c403035000b8005665a5007858400d04500340706054001c141c1d404421030702801341800040552100794802d009080000504080c2402c0011810405900100e5a18039100d400ea074103a5000c1498232910046042c00c0408041f01d14000030540304621406843e0f0002003100d0702000b80e82c0b40c015081c103000302c3c2212425112810031201c50710003803040e20b40c03018000405034142c81950308010810081ca09100d0f40e040da240010500703440040b54544041c1c1d41d2000b00440c7c0c6a008003240745c000030283300801d80303241400645c508180c4141c104c507040c08082424040039a01c0c1c4011980074240e203410a644541c16880b1ba4000100280c030110055402c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 781459964 1250 781458714 781458749
    0xc050d060e04111f0e0f030a05150c040302090708060a050a180531050c1e12010603020f060c0a12020601030510020715050618160e090c09010e060705010501060306 72
    0x30000f00008058802040c50365400780844c0040c0d40c0221104003c0f42c221a4504050800e66002d02248048074003074009000c55100034054480d036410000c160994094041c07105002580714041a0740c3d0110090400000907203038440010219240340e400710750710454003080492803540e450305500d145016080300740b040ea140c1603a40d10b0003410802440000e1984000c15850b40c42540031107030341d02800340c02900e000344000713400701e080030300004c44e60032410b841c0350381c01065400d101c542102c84c800c801008000050039940094426403c81800b24030401d1302050b00c14a4403400e100c4c98000c80d5110003450b180c0540d407100079407586800d1000b0380f0075010300601286031444034004c03949010350043e500b01c450b002c00e496180c0180300103050550851643e07010a2a540c0601c60342034016042019800a20192217200409858400042c107004050349030500c02484c003042c0940d0703442c0c402420700c058411030035404900d1030300580c0f001030050760a1600001d0525090360090040e240928403600703000c0d0303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 781461214 1250 781459964 781459969
    0xf07240b0604080c1009090e0d0f0809100f02040e04050a05071d0118060b070311061e0a09052d120c030d05061c0606360c050d060e0411 60
    0x42c0d1280c682a5004258000c4084c5010345036000c0038403180c01c040c0c00d2a6125418002104d04d102c2800170181d00003151a0041500421a200190102d1420851610300700d50010745074103c3c048170b59481a02c521070182c2544058040d00e02420003403207035920070b01c0c02c2e040155880380040d60540701703400f4000011854070841d0881c00320010012401103856480c0c041d6860403c11041c2c88210301903a5000f010440800341002041014002e030b42d500102c0041c902c205052407000327005045150104e8039918981e02d080311034160b0181d000036001602240a0a210b41001110102082d000c40c06a8607040b481c20520780c01102c50200d541103442600900016600c20700c10703142010034a500601c012244880c080d08096801400034106039000300c0e90000001d0b0602d201d80d01200c260b07071a0305092040e411012810641c2c01c98180f003041c2000715040c10000b4400101c161030300c085480f5110004018014030031200b4264110500300003003546c0d01101200200103480c2181c80300c00b1301480c0c040e03a1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 781462464 1250 781461214 781461217
    0x91c080613060f03030503040305210a0614151e0a090e090d0507110d050f0f060901020a050f0d0209060d0b01021b01020c2b05070608070c1104020f07240b06 69
    0x30303400c1840106000b415602c043d5515040200209c0800c0400c100d100c0c1300700c06090f4144408001080c201d511800d21412800644202e6000380d90301c000380f40302c42e445580d44c403103004100b03045440b4220f40e42c00c1c1e00303444051074010036541003c6070ba10001b00903681c02d0b8041288011625403400a1180d074440f2001e05031220102403c03500021003d014201c0403c0d011760608054102c000c1c40c1c3e006490302a40d403981403043c1e4008200b003640110b2040c1490700c1052080c568408195002181303030540124006c0d00b28025070410090b802c401292a130101480c0b90b048900940c8010081d54a070007076418a40080c0c408415298018040c50b08011003440c41c040c0010b240c0001600a4803109112340c3c1801040d03000019000c0109440c86c404c9400c40602c10710198a4602403005003035010705288019144d00d001910317010810116a1500e4041360342081402c08190003100d01513629a6a4071240d000b034040c0000c0034001c03003401346103030302c0107001d510001d074414404441c140001440c040030401b45 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 781463714 1250 781462464 781462469
    0x20102120d020c070f0819080a030209030c09041b05030f070620071814060a05060309011d01021306050301030b0106050313141005070e03150a110301120b130812091c08061306 77
    0x490030600071800c27054042c0d005401d00c07043c05411940130840301c800103280c141058506441000c8a001100301c0c400e01c0c40310100140030141e00034503049020240c400e690f28003900c074080400c8005242000011410482801845901c1e000c8071044c0e82c44401c034040540103141142101881c081151900d242100041072041d1802006034940d10710384000e10070160f20007040c5102e03555a508c0303215004101120390456a0509800041e1035200c8840100c02d0707801d460300712609101c0305000420014450032140b9042d2042c520f0a661251100e0b01704031446210440001c020796a1158020f180d5080010f0413450305480100a00a40d140e5070001e60340071200340520b903019003000c07102009002c025003010350400e059403c001060154584800e01c035400c01c0e04542d41441c2100c181000b80304007500c00d5500003001d034504008680305a0740c1c0300c17550f2144020b0482c41140c4034000a1100500b40000308094600c801103640740815000000c090700c0c0101c945a2050340240101c8050801521a820a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 781464964 1250 781463714 781463723
    0x3030a0507091d1f0b090d03050412150605030118060c022410060906090e0405150c0a020d02150112021f09051207050a230d0303091a04020102120d020c070f0819 71
    0x1e00403d480c10f00072847c4407800c0030b505002d1f04010008404490310620b41215001d1b55100c0c900c0742c0080218401e81300c0f554040c5109030705000c81c1d01349403440f10460340f0f000d983c030800009112108140503030178070121510300401403198100540203942000c0206d072244d007811004d8100e0a484540980d40d40c0a41c2c043c9800140d1000d10a01c0815804404990801c1c010000c5905444081d010210200f40494240030700180200d0309a142c9034040201c81c0d0060345a0001d0810421501100d80c0030b220141b08401090600084000a43d01c403c4a40740d01c4020089a418002c0c905600180a0710610700c00d0324040d0540000240765030700702094190030303540000c01e015034503440c0c20300e4443c0020500b51203600340010803c01500c290f4480c3c1c411042c0741e200781ca0100b83c107155801c003040c9001703245102100c1503201c0d204010040c0e034041901c20015255078809612011544088002401454440b8150784108140440d000d414445104110351008048030701052810312000442e0009120040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 781466214 1250 781464964 781464967
    0x30f090703260f03010f05030d02010513120e040905010203010503070f15080c0f0d140a05060901051212040e0f090706050d1a0d030c020109140303030a0507091d1f0b 73
    0x2580c19851080341042003040d440031803e164501e40000c0c0540d1007a4802290720315000802c004604050085d1502c0da2001d00080005250a0050952107142c1640c01880f100005189062050144c400303506400c101501c20400d61400e032410034001d520a0060038483d100c0c0c1480014030781e8206040c3ca069500e40080c612410f4034100c020b8540d00c502400310191140d05202c49103c002003007014010b0b01120000100d11504605c1c130740c0d03a01020103072405406509000420080382c4445141d2411200183c2d2620100c560590340c007030034800c0541246625400c00070700000d09010412816005040d4000c3c4800c440e118244041d03500c0c102c41c414800498000c6c404610f45010b90341c0103088008070036020951002d00c60002a6012400b4102140840ea40710800c0c41076507070011182015103542100c940203d40800c5c0000d680c5c1c003005084090300e075110700010344451b104a03404030050004520100c0000703800c1c0400041400101c824400c4115444034403160035080c021148111295000c501e03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 781467464 1250 781466214 781466243
    0xb0712110a1104050610271d07030609020a051b070b04030c080f030319090203190501020d063008070204020703090303080a1404080a0c0c0b07140105060a0b16080f030f090703 77
    0x581c0b80380c40400f00c8261004901f00009400840f10422031130028200108401c185084000982103c01c69003141482c148144000c405694200b0120f44800c10724034192602005c031001410b113061100d403c54030f50b282d40030800104019400c0942c800382c0f055181a1825940304424142d500d000071a4900741c41e00c4400e030744a45c003c00c6603209200305800070f4191003420303000c0c103400d501d141e00e9000c046407980c2d0300192480a0003c1441180d0242c00050b5405100d425100e00b0619000d801d07510940c03110800a040200b0003140d10103c2d4012035020700159220782003800e01503c0c200d03c1d0300c4281d000c54500400565850f400d40304900343c0c8088401c1c0070505894075250241603402c20005502401040d81804011485000e1502c0040c020f10901903a82c1c042803401e05903003421584250310580c14842800300c1e99585041d000107540341e00994a0f20307003100302980200000f02d01009420a14001900d110320510703080258400c0851350b1840c1d52549844038096620802444040c0c006400350990 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 781468714 1250 781467464 781467497
    0xc04110901081602010e01021801020f062a070204060306020a120902090a0b01200f0f010e07090902010210020c07061b0f08091201051509100b0712110a1104050610 72
    0x5002c98400b6910001031b014192001e00703400c9a0151000c2401e215409007101e01a41c0e04001602c00c0e840c024002d0081d42c2400d0a8900c80000d0410304050000049000100c0801508040c2d46903980c005000740400c554030b043c0f01000794002c5e00c00200182e5440803400764081580694500c10768090010581e66541d400303041d0007051068507041c108902008a0760001a040e040103042e20303107100150074407108881e0102d01d803002407280200d05906200f80d0f0040250041000c200f211b0002c08081000c4445200403400d01185caa44040c8480c40880d5000200c80002910001d48442e0b031650445001d442e036040c0c0301d52580e80b030024100c81800c4c0859000409a0025101d125400340849501003140f204241c03c0d58821181221502015000b00f8030b40d00e026501d0741d40000d51341c092030503140d0402d401d54800d1711503540301a0642030861201d0340c0c65032107220003602c409407080684100c4513452900b50609100011302d43c0c03081d0304003004248180344c01200000180e0894452214002c0888035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 781469964 1250 781468714 781468741
    0xf130b0a020d05040c08070501020a0809040b0111030328090b0712020c0f0615010903030c12090f081c02030f121306020c0a0b0106181e0b0c0c0411090108 68
    0x104035060790244000700c041002c80c095207005078400c1c4075003040e00c0d08142c4690b207000415440541154403084128002c01c900c1c10071502c00103403e480105011480000503036000c080020000320030320001003046030100ca65000d091031180f19100c0c2c0100100d07170b501e00d00141e400d00c26003d4981000b0b100410303d840d00031255111403c7c08100d0140c148102d0000c1306041429903003e00125400810070000c2c6107240c41c03a0031120301402d003080303c5140e00315207008100300555000245203840507085881d480b40036254110050417825000a811900d600c01c25031103403070040302c2036010038041410195641c000b1040e1107007815100040d5042c4441d214088199500c083e101401c80120411048003041b80f41c001011081c40d400000c0c100408945001000d2400503070040040105800341040f075501e000007814100e0303c8062030400300001140071414a1034a079486004244000100d24490030b10100e040d202c070b810308580800002c02201c08994151103140c034000c0c0007482c1800096402c0c9000380 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 781471214 1250 781469964 781469971
    0xf050a031e0b0102070b0708030c071b091d0d0219020f0301060803090109120c030609030e030a050c03011a0f0103020f041a030f061804062d020a0201050f130b 70
    0x600814414055001c01100e21140200540c000b6214080d281d00382d601008164011700381070840906d0010252285100707030202078054450b50800080d85818400141807940106882e540031143c60740d030390305091000300340e407c81d110004000d640e402e820704140403c010300140800d4016059002c800d000c1079003070940c0e204040381c0c00f030710b0300c3c0040265450900c211030190914900441d40da04103200051b10304107195100c2ca540e40c2d600110540000e052021410849070f0180000c20814803034a41038034504039002541d50188901c01858061001c00503040303001c888241d00800c20701ca0030780f203c20094140490025008030024481c0c1180d94401c2d07006048548003030b6403490520b5254418024a00700f40355107004010404000e00814044080d5800e070020012a10307500e1003188080c982446980051001d0816666403c0094021031801d0036071130007000c00024550201c002e0501200250000c91102c4015803900c80003807080d0f0250101c1ca4004d89400c4010948551666110b100016004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 781472464 1250 781471214 781471217
    0x16030b03100b0112020f04081c0f0f110a03020a0b0c160f02150412020a12030c1704080102040e0406050a050402090f0907090f0903030b06090a0506070204020405030a031101050c0301060f050a 84
    0x1c0100c0149134449102a24601c590035103000c1d0b40718600360216190419079810b12404004404003041190740114803036201d88042e0515604040d00c096082c2e604110718200700702c19000b841c84c1c180c20950301241c95600c0c54418180300c5d0303007502c07816440d4403940100f408840c940d82102710424040380c0c0c0395110111707851000342141d4a2041c1e6140c594140e030400c0c0c0c40320b2952110f040d500b00862901103000409070070140c1d500000e512064030000c194035032034100640802c044103c2000b8400c06041220043c20b400c0c002556907550755000780001000444080d640c05203800d01040320880035009a901594005010072402d8032154100881a400030b0010484e5114201c0c2c0000c0b003030018003036840c00480c186400030f8030034924203003d015500000d048621075030b02042008900e903900c1209105599040d900e01340c0342d003081e101080003440b90380c100310343c94490301c202e8a040681c03002c0401d0200844a0082c4116210744200c540c1c14002801000c1c042240403000312240c80c81800600a0443d0030f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 781473714 1250 781472464 781472477
    0xd1107170c0d03090e0703020f040b0c070308040f090e030c06070809160b04080d1404090f240f06110a020d1b03080c150907053616030b03100b01 64
    0x80e900042d000d02801072044001c104680810000a0000f038481d41c3c0c4007446003401d501d4000c5182980005100c1ca02500600d4480030410042201c410070101010315807101403a0780e550313110820040d40e1303039032032048035404e50800f0301540d043c0001000351180d0700304000003003a01d5200c0c40415594908000c110380082d10826600300d41060003011180002c2c2441000d0f55550b42c20401300d00e060003807944c0c20100b0b002e100030084007055509402c40302100c5640f400086d0240c21820681c028200e13094099100340c054001c200440b0407001c08040480300d04107001c900140e070780c0400b41e40340c03903202031400020303004420b842000d4140708c2d540b021102c0c800c011528480030b081400700c0a03044190426105d5003c0070480040998003003081a86110724004805000e01c0d2141000c1e0b5202c200b03025080c0540c2d2000200e0949031481c0413600180700c4c01510003001161440340030a0072280803500340881c40a07c1072648126802032041060812000e400f41038804910200e0202611070b181a10303040100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 781474820 1106 781473714 781473733
    0x6020f1e0901120b1e010c08300405030403062007060f06050f0a0b0a050f160b060a181a0409030903060506061603120f0c050c0d110717 60
    0x1005800d40c800f1521800040310021400e007c02044440d0102e002c8807416000030400c80d000420400c4140d05010b001072008002000356000341c2950020003087c8045500c503001191a0b00c2d504499000ca5035461941c22259404204180e901540d542100700d40d440060056400070031084681c001d91101c0301c00025003207140c500c981001d4960004012800f14042d1090f1400940c1140002d9100d44c00c0c000488040140745600b291003001c0e807400a011f038507100454000780c402c003410a00c03414182042d14001081134080030103035121965040031560382c40b4081c04000500c01c0d0340b40a0142e24601d084070690344060301c424486e602c2440f5280500c41c040c0c2c0156040354041c50311401c104010404c80b00182018078800b192241000d84903510141c1000040400b91805022101498024a4100c40411400880301030382d8201039802c022550214000700d904091103801e40d0034090 = true := by decide +kernel

theorem cover : BRFrame.Cov 781294964 781474820 := by
  have h0 := BRFrame.cov_init 781294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 781294964 ≤ n) (h2 : n < 781474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
