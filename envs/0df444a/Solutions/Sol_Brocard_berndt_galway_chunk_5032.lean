-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5032
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:31:30.372385+00:00
-- url     : https://prove2.me/submissions/a739b3c8-6c16-4fae-aa62-ebfd56e24f43

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 904856115 ≤ n < 905035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 904857365 1250 904856115 904856129
    0x10218090408070203031207030b0102010b031b0102150703020301050a080601080a0206071a180c030615010c080c07031b0905040f02040218030f0d02160617060a15081006050403020307 81
    0x400c81e65503040100c1e0742c0c421400000c0d450301001980c088030b500342e0340c002c501071171003a9402c0040d2240300005900701d0b22559012503043c0d00140a0903400717150009101461103041c41503c001c894a0306604404800640b00b00010980203c014066800c0101c1b810b002441040003c00e055454454000c0e22004034000207805840005046020710130702c2c5a100c10801c0304139001c1e00203450480721900c0d12048003520f0214500901584c000726103000076900340120303103444100c0c003120070074001544d0140c201e0000f1500c1038014450103110401c1844804003c50207810600e104a14117031801030502131640000d40118900700c1400003158804c2441200564180c400595801580781c08055401000201d5075040c4104080303003410040c0801d04070340500355a0210340740300104910b004412912030060000043d001a40c00c08055460445140c00c01d0025010190187d100c40d0360903480001e4043c40c0c00420300d0b82080c4440040701c012420700a1441d031070704904017421940040c0d1144950700c1507035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 904858615 1250 904857365 904857379
    0x312020c03163b190606270e0405030306010305100b03070e190605120c160b06180c0a0f0315141306120b0c090a12240f0e010218 57
    0x20f1070841d10700e0804400b002c50105086002c2c0300300030300700d031004200310703012091080071000d002448440360162001ba218541c0b40d082c400c001c9962054540512680c81c1812031410718400038001c000002c10700d01580c014006103070381c4e251920014007910303800b500868100e060307410f00300070506c00c14050702c7d0010f2061401c16001d020410000384001c068241120315019804d60008005401c00024138407801060703101300180d614502c4072905409403503540c0200c8404110040b0000f2a0b020003254801c8004100303080d487d000c10340f42142c030300044401c04400d880010f42540240d40008001006001c04c0c079091080003854034001904115a105024202d0580324020141e560751340404003024000c00d0341085002d0b5505960415404582000e45046903003501043c262142d070421101040c1c3c001d0001402d95141081560541c603491a00b0740c0d0706681d810700301e2445000005142d0300081c05003004148003514440341411108203040b264001d80c030412038034405030740d0100b00010a1500700c0d40700c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 904859865 1250 904858615 904858649
    0x2070e07111e0307050c06040e0403081012080c0606030601420513062604080c0a0606080d090f060809160602011a0607020a0308220312020c0316 64
    0x807500d8441c07044880da40c20111003005440d03111000002d050900d00540840e0001c0d8041005d100d0980301c0d0b40200480300d078002000501080c0150b03c155007003515152055510365440c044000709040300001180c8040780007a141404071020003602d6001802100a45000c1d45840140a00201c82106125242c01c400f103e018a0740c0b0181480440411211a40c0d01c8840400e04002c00c070394422007007044070348100070300459101d104035090003024600303031100c1c030440740c511907140f2001e07000400480300100100031402003203a0038082c45010520074000801d6150400c082035040500c0039410341d08102207840d0804c00400f04004034400c44019007040c10664840c2540ca0b810501080c285000f4040c40352070002d1b0310f6a0540c0010507440c04445102d24199403007040084500c2000c401a5120f002c240d02071000c03a00c00001818035402d5200451181480c0543c424880d208a5100381c8601d60580d103050304460301401007a000c40b038110068205040e20584c0b060b2117180f54090090920030815107 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 904861115 1250 904859865 904859897
    0x20061605250201020717190c090f05160516080904060b12090c09010302030a0b480f0d0902060f12090c060c0a0f081b030703020d02070e07 61
    0x44401e40300c9040d4507081480c090300c5203a0000400100102d0051044550000e04044102d200e2a403211064014140c10000107551541584c0d81d900f050324000041c03840000e060340036100c0d10a50b600d00c072801040902d40700c2c001030030207038a50344c40c5424001c0c1045203001d11115040c141e07040035840182c00e92120340c0880400c3c0100344c240c1005074401000544002d81031a018a07075440b48803a24105d8000c48401c00c2030041246080c84000c3d00743e80208001c500150b42400501e03486110103211070b04500c00541036210920b18040c00640440c1d00d01b60aa403aa03884e40400031138000401203035403074200c00384404441449818810a210f90381c681d403240441d5034070011920b030441210708043e1580141c030313605072080200b074030706070101c1c03184e02d01e036041d1070a041e4140d914100800c00540001460703910340341412024454100d841c41420401c14524601d10084a0111517207400155180d50107450042d1600d0400d1070141c0665000701401c009504c200494107502c400c3c180b41080401a000d02 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 904862365 1250 904861115 904861117
    0x90a060504020c1c0c02010e09420306010e04021201060e0f01060e0d2f04060906060906030209060d0b2106072c060c07030b130320061605 61
    0x8426070041c0000b41c201d880d41c0001800c0c5000014008290341102e00424041c3d80f4220401300080c041214001c40600710b1400200c01da9220a0300b1000301300b04000ca0f12050802000102c01e4000c40389001711203000405001d18410304c011044d402403c2035414280c8045107908004d05c000d204103401d81c4544100842900f000e0002c014174441c1c800b040c1001e100c0c1c0c00c0d05c1402406404001106041d0310111890a0701a403400c0b19003101003003040000800e116460841940d4440420740c41000d00d00059407224803c56009194492000803100d00745000141520455807001c41014014004100701c0c0c0d8468003244d04403030004900140310f074240780c04a0030000d403400280e000c2159002c11505070020201c0c2051190136141d4030350001c1d200381d100c000031a6010901400280d00301c0b0b030510442d03051490007051350328000ca04a03440c03c0c0d41d175660f00108681c03c40d18160041d0300b41c40c2d2a010190000107200750050840280d615410555080310380d1a0401003160038950540e01440c04082c0c0260 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 904863615 1250 904862365 904862369
    0x10f06080a0807020a081506130c0c0204020d06030c080607081609050108060103140f061002011104030b060312030108010e01060504020a05091003020903010606171320040f020414010f110c090a06 86
    0x1019165070510030303661f01c804ca01c03044072150b01079601d0070022104010a071140b04031100035a140c4460364a156024400250441102000b516907503020100110745000000c01c01403460300d00400891401a000820903200130f840703a15028212890101c159800500741c06c11341d6020f103804c0c0002e68950b00100c0c00b610b0740c1080501090001d8003807054a00381c06800e14881e803400d80d02000c0111980508078200e5500f01c80b1076400307180900003400099a0008075030b4020350000c0803242001c0103143d1442c003a41c000ea01c00f0820781c3d500c80740c1a401240a020b207400404089030114280000c40402900d1071145804840c4141d03050145e60000320301030381c103032140c041c0c0240003044126200c003005007883c46d60451300083e05884d80e001848107000f002c800c0030059881456131800045210401d009440c0880c49258415210700c0c2d101c0411b03a071480a00001c140c01288422100d20000000d4509220140c8100420a091907030a100d4030700054842c0185c0f01c00d807500b281596440350044018106a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 904864865 1250 904863615 904863629
    0x3020409090302030703030c0516080f22080d0203031605130305010f0c08100b2706030a0c0e0a031101050a020a05010504081c02030f0103021c0f0b0108010f06080a0807020a 76
    0x400806002e250340000074001c40b512940701000000b030300c140c003030307459009040740704014030314000050001515010150403951050714030349e4280100b9650380c1009021b6013451010140b0340c0201000168020070000030440c0441c0065880c0d81440d060001d0141e0401d400b0030f061080004140e00694001000e020040d60400000c00808030745090000241c03800b200e4100c001009240859075040078118030100b02c481e4103003010724140c0c90302d4428680d0030b100f4100010200c00c03441c0a2040d501d48800071031281c0c1001c0d07800101109101c501400265401c540540904100360082c0001b0f02c007240e000760301c07540900b8043e03120491020124a4000440360041503075082805200411102c02e000c0c0c0004503010380d04107103809110441c002240011125201700e08140c00040015060511000e40d0803448060f140070340604a8940858210900c002101e03031881d280c004019011007031103034000992500f001802000e2805408070303514140034130043c0c410040040c0140444d9217031801c4a00030910 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 904866115 1250 904864865 904864871
    0x2010c050607030e0c0a0f0909020d1a060a06020c1339020c100215041403120f0c0a08011a040e070c23030a030e0c1824030a03050a03020409 62
    0x210800601802c844c00501d075041c17082c07442c640e0603480c00c0545001602d1181c0c40700017140b4606180a805408110010703030300030340e10180301c9011a0001c488500c01400030090b41c44c40c4e081045c20f002000302039a02c0031046410243c10000c240c0d40700c3c0320031f040342004c0101c0414000c060300c0180012141d116a0300940901035030000306640601a4000310b03000c010b0302038807101d46092050100e05e803607040c452401070300940c1c90705004090004200743c215001d9508078900b603400310491441c40e44054403030b015420300801080004503401101560050500003042e09002d1181c00280041e1010b01178078003000b070903c041e020310246000c2070320700900885811034a02d0524100c05050505e44450680c0e442c0300c80f860407c45410596443e06100c82c580c80114a400c048440c124010107a0301044149030064048059059031440507941d20928a07624a10320390801903d4025280e0020f0900c1740d200c1c01484002d0804d54012038180145609400c00d15a1041e28a030f0440c020b109640000440b545 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 904867365 1250 904866115 904866121
    0x2040b0301020c0f12070506010b0307051603050c01050630030d150f1e180e030309031312030203030f0c090418050607090b0a030903050403020402031e24010c02010c0506 75
    0x3c0009a105028540c8900f520480c1c1c03071228842d00380c1e104031280907142d43c1c00303040100919130180340199488540c9152071401c00204d00c60201d02000441c1c000c5d40003c10100310f14400707007803e01c61141c004404440e924110030320440b1b09a851001001c000d018100c6090007a881c1e980305000300c070081d621004c2c0400c5401d50a003040303110703200603008002c40441100c40100340c03030720980400c0c510b10001a0840b03840c185868030040c0880f5480c182821559280e52010550fa40c1c10000385000d0b00202018680b16a001c2810001440c650382c0b02844d450440035402e0f01080d004012290041049106d07040e06030f49280149141d480380c4004190028034140d0303041d400011450f00d1681491003001076030795648440200700e4055500e8000d40034002c03420490422183d00941c8132110796072003403c2c420b04082e0b6940020f000c0343c2044651b2540b00310000d40989001d0b04c03140c1b026600900d41840441d0b44540d620104040d80d00c03406112f41031040203060401503a0060f880c0c4640e0590001c02c03500c15103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 904868615 1250 904867365 904867387
    0x403020d121e02031801090c091107050618010b01090b0a08040c030c030f12111e0a0b0c0414030d0210050a1d0c09010f0305101d0a08070b0610080a050402040b030102 73
    0xd8005c45010716030204840700702c0e1000320706020701100d40381c01030160141141082c0742a80200020a00c00b00d00700400c1003240e0009206100251140c400c6006100c6031122551450b800c0d21840000d0354108401c020003403021681650554428413154501192a82e0380d40c0380148038140c0d25000900340322511f24000040100941e00610f04c40e208040814000030600002d0301c24464602c50300b1500d400c001c40000c4005206860344020110b042e0481d12035418541321020959430585446041d4800081c050201c4c0c0302d4039218280c10308055000700000e104c50f440c000d46031403002e901e506940e41c5440200c0d8002c64260048100048880d0080404020407040070769980c3c010a0f455000390b91b03480001681c40101c0c2c195208503508407010700000c406985200c401060300080c15841907012007049401e2131401c102a8503958480d4200c47d5969800741420111050b000b01010f1191800d01c00f94080141d0041607560401211500440c5a031a00e00c0080c0c05170500c0500150190b2011980348044 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 904869865 1250 904868615 904868617
    0x31209030f050706090e0c1c1b02010b030c0109061209030c150c0314010501050a113d02040513021305031002120a1413030309021003090b0f0403020d121e02 69
    0x413000b98841c2084203540d5042860760440450b0213a84140040c0b0404031403100130300d01c00d0365a8441c0c0720005070040b40f00c0e05601e500e420a9034000d006030340d0b5201c241c05c242030400c0164004002420072002c554039000d0000c051803403400c0341802e160b4a0b0408001018007404001d2601d550003984044d81802c0325104000600d20100301c60300081c2030009400f20031103641c1c281c506071001a0f540502e0030003001415164100501d00040192103803140c807542500c2102d034036044108035108502c0e40b0000480c009100080e02d07844071040140704000c00c000035600ea10400c60444542c00c005626030a82d41e005c1c1051141c40d030f00141d014080c01250302c0303880d5000e9009014000c0f0880b001091500d4000140040f2440800c1406801d650000400c0c010076074000020030b00c0e403003481d01217081501a80030542c001d0310035140d04003007525082a00200310020348460f51200844041c6080f924058400035601e400441e406000d0180b0030810081d81c000b5500800c0c036581c1d1a4a8641078410000005002 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 904871115 1250 904869865 904869869
    0x414031201230a0e0142021002121b12271507030504081902030703030e15040320030301081b03071811040e070305040525031209030f0507 61
    0x4180400d090000c0946402030040c0184c0c4c41101e8040700c980e003040d10021003907400c859210712002d903a03008145c1c00c884150f1702d0f8a00344c80070f400c01008160100406803605520114039045140184a02c28549007032104055105207c091036818242540c4c0d10f0741c809200d03080404c4031010100041000a00341c0c040d0350042c5000c6142c00c07080c044440408a62514114694580e45400d00e4006c01c015502c02d420041c0c00ca805520f400e89025016503000d02403015040c0194096080442c1c1201455018811044070811810140500400d81d1031121541c0c1e400070001001d02c1746190301c000c08040003460130925101345600301c0e5500d5840b41500350307680100705501c2d001003e511564901d10300340401c40b401110b0000380e4040c110b40b10041c0c808040c005040e400c038403c007000e000000c0c48004401c601d60041e030f502d40b8001703061b003030a041a03401c01c0b102803043c88001007018018500f00040742264000c50790015040303c2c1000074000200ca1501e6140e1025121050b02503114003400404203210007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 904872365 1250 904871115 904871159
    0x6020310170a0305030f090f030a2601150804060b0307080c04060812030406020a030915091709010507031b0c0e0708090c06190225060e0d0b0414031201 67
    0x100003124816101d036502c40040b4000c000650034000300c0d20302130300c6240540c3c204080e0402d81d012100003d401600d181c018401c2040000e9903040c08101214580c00c180380c1d0400e4440358000103606068910a4004c1001041d40402c10b04000080a20606030b01900145030002c041d16403060b5182c2c90301d50340f1940d000307480744914644038000480d5003000a04040d00c010000300c1a0550f41c0d90345030f050081d041078000d0020315456883c1e81001076600d1810200b070138030f1654005400401340c104003552401480134008400410010105240c1c0c11405444640d941407401e00c0e4145040d03c3c402000344003e100c0142041928680415280303001c490705c6101c0e040a03503030172005640b50300c2d00c25a211480b40300160402400c1200c001c041c9c10550300a448207d880c01110f4070040c00d211100d06042c44408203142c81c00b29114288102e030361180c40f00c90703000d03000c8613940c04950306071716101c141601c00750008001da0350700c031166100b4040600035266800044e5030111920f603518611300300305503004c0d20464 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 904873615 1250 904872365 904872389
    0xc05060d1413020f01080c1e041e0b091e03030c0309011106100b0a0e0a1502011802090c25080d0b01081317040513060504060509150103020d0906020310 67
    0x26034a080980341c018802c640051104030079061043c015a01d8801c064020003160710f0030000264007000b6500321092642c07254403d40e80e950320708805034140d0303400808030350001c40d100c58040142c04400d0050740c20505003282d2401c2d1500d148403140d0500b08601c02d50b1609400701140305000f0b954080007a1a246400780c0343d000d49210289041034440e030048030019004900780000703000d01000440506440045800c050540d103103071200103104012107900c205070f41d0040e2280034113001e41c20300584103103c601c82030706011251541e001801d05840100740e800000380101e1482d191007400c001d14025041880000c5494060303d080040c116403082c102c840c2d00500b080091103640d40300e00c1d081ca201d500005040204100c159841060b401c403600307a1009900400d20002c00c050341e031903516400380300074003c0000b1450302e400240015552964003991091009500b0800c00d00b10420841113406000d1034016a114003001c0ba0308000c140b20301c3c000c0c1030f41d032020040100c0c160020211a0681d03510950325 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 904874865 1250 904873615 904873621
    0xe0103062313030c0809040e0a0c08032b0b0d0c0306180308040209071119110409151517010903120b062b0504030203370c0c05060d14 59
    0x101c05040302698011042c03003888a01c200864130414000071454402e0141d18a8852040001419103010b501d0141454210701e0300c040c1040030b050440c2009141020103142061500c00d0340541c050701501c0750711403000e101c802d2005908000d50101800d140021300f080e090000609128074420300750f0000300c400c540740040c600c11041d001112041620751660703440005907516800d1103175042c1e000d0102c2c42404042d0350003d0341400c1c02d105a030301052540b4a031180804107802c8c00130b146201d61681d140500d15081140003c10440b802c0d02c96003440e80a40812160601014917a01c00210b80c8615031601c024040c80e070340320394190040b80030030707000b0380c0c441c07010881d114403090840d00c0d65007045501c02030800004008528031142544625590202c0c80900640a64440300340c1f030f0211012030040c0c000152440c55520456440a080f01c0c1910243d000300050340f01403811700c6101d11070300052201682ca030404002c08017083e0006010054406901c0710000440786002d000c0b01c0c070340701d903141d00c0c02400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 904876115 1250 904874865 904874921
    0x12110904080f0d0e010204090f0f060609060807090801090303020c060a1a0f0303160c0302090f010506030a020f0705100615170106052206080402010806220509070e010306 75
    0x1268096034001c1c0c007162030004850007045150f8000124000c1c0c054854041d0b500b80320007031000e0402040703074620104103052484a410100d074000d000715584507140200910100d81e1000d07003e42541c4440c109010140c49044003035610380c02d0342d80315080315800c000c2c0050400d5415006000c500703800004550310380d15440c2c4d010060f568040709010700060201d40301041464140458210100080e050328070b0404940000f50100d06448025205150245020011400c1100302140d01422030030700440194145000125075100140a01b000140c002c10640079600d0214222485180e1020481e0074a8059280050141c2454031604c0070070b101114906100c6070242d90480300c1031340002c010300100c0e13080104c15280ca40120002c0a86407041c00f0090018008680403000030f01500e454005a074501840010446400103142500542680b19541c03002494250b0482e224403d1500200d416600c800303000740703404a80d0b801140c407442c4d41c400001c240a4154082c44c40c0741d600400141c182c1c1a50310b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 904877365 1250 904876115 904876129
    0x1204050304180c020d0516050a0609020a060507080703050904110d0c030c02010e0307290a0b043813020f03090d02162304020c0f100e1b0a0806011211 66
    0x100040940c021040e44100b580c03140000703095031f5102c0d40202c00c6030a86900e0300c51902c5030b1510100c401381c1d5074040c0c80c003d6161000518000f0b108610701a46010120380c0c40540178040d840c00102405000300309000c0c603555682044071855102090980c075440301140704005401c001d102480442e10301550444060f1040c0501000c0c009100000c601c0c024540d61b440714aa1103102502d490817481d9a541030344425100f4400303008140440d8045100e007183c01c10001103608001010080d0b04440d060030030070381d940b521101c03407140c41140b10340600e0188001140404e40c58010300002e4520025926480c2c5411380040d40c050b044041c2166001d070030380002a641c40030f1a00b80c04804090b01071041000c8035603078008251115031a00d0306078180143e40045420313078100d80d40c070540e176800c00d2000f41c000000030052020f070b10541e0711060040e2018283e449403144906a11310f04030781e698568542d00303070b21049400e80080440004403580340da0f5455014102819840045400c40e061101c2804d413480e0140b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 904878615 1250 904877365 904877381
    0x101701050111150a06050402032a070209040b1506030a020a0e0d0b16030b1806010f0804150c05070f23060405060109050402191509080a0b01030611120405030418 71
    0xc00800d00f044801c01e6202d011540203000d01c10380c070b48522000c900c0d501c95002450294107c800f848110520f0804040b02000c0c0c040790805005106200c50310260b0781d040c2e980c580040e006a01c051961301d4043c940b10508145c0441c4582043c0004140a1007816a5004260b241d0860b40e50821480601c0104440302e20044070140c0045030742004903041c1428600c0d00100703905941000a418188100441c2022551000d00000000d80c10104140c658210050b081004598030f8103a0452802d99140c0e00d15951001c1c006d52960b94812540540502444c225031940d60800ca102c03d00c1d80b414500310341d18550508402c00c01721603100341100e290000040c514002c603132050240006a0030072450071300030803000f0400da1303002c2241162681c1120b46048141c010b0300d040d800050464111500141c41d1007401e5000f42444d074404400da5022440b031081e40d40c19280c0c807420215100c1c0c10400030400c140681e803405044900044140000c001c1e00100030700454441100b01c030368014048198100300e5201c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 904879865 1250 904878615 904878647
    0x907090506130b010c050f01020a0914130b0406030b2a131202010516050f0c011b08030c04050a1203020610050904031107080d080a0b03030304020607110402091017010501 75
    0x900d940c00041400754120f502e01490600d428107000c10304d030f244c05240004070300c0001c52596000a10040080e440380c17494015207201d41c00300740c0510a46002c20341c048281c0c00800c03216a910040207a441d0b49641091004517003000c00380c2c0940c1045102c1401001103c03801055080e1a1108030340c06040c0541a2003140801e01101c2208501d4000b400078882c654900c01c90400c4810401c586220060085201304d05001d403008215820220707005c20301e800b6281d4802030600101e05042c5030f01540b0804a2410550300000c40d913266211010501c1d290301403608400da0020601c94040b4488021401c103000c03480c000d030300300d51071a290307012140310340030b41805100e4000c0b4000000a001c01d00869040c1e13540352078001210701641e03881e1720366401d04100c40c01c8007001551280c1485034644050190b290a42e5084025500c0d50400f6800108684101c540003041a080c0300502a1640e650340d050f19042b41002d081840c1d203030003000c40101002c0f1103000c031000c1c40ca01c100020440b035119150103000a095 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 904881115 1250 904879865 904879879
    0x60f06050d170307021f09030e01020c130b041b0228110603041103030c070e36070302030102160311010e070519031e170a0819150e0907090506 63
    0x402c4400366071030b0710082c412002d40c424210f88000501203140781024050030b8040c0014525414038005111000311a40c080c110360200d042030415640d4101400c3c1e1a8042080000b16040d180c03011070040c00c00500710b40310018549820303a040a8011608902901e00641203503400030004000d411504100f88002c1d109182190019030a8101500107542260040c19203000c50040c1130000b034a1030b4850b4092050941161500308601c1d500788280d56041041c40f00b120740e400100c1d54140707000c0201426042d00050701903e150301c0441080c0f00c2603000e150090029507440c0c1d030b03850b10301c5401544094114002460224454090f00c2d041c420311011822000150240515050810000003960b070501c06043d60904c02c0000017030040d0311481903071560400541c40031101400c0852004030782489410304510100045120a07078002046a030069184000c02544014042c1000050450644a4824800075500804c03110b43ca5154907124140100499007200e07100c401e07090507100c00380ca4003904840 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 904882365 1250 904881115 904881143
    0x7060c08040303030b010e0409120201060b090315041e050c09060f1003021e30100308131806090c1704020f0303070b010605120703090b06042403060f06050d 69
    0x200c40c0e0884020b5003130500d4400d04047c0a64002011150f00c0c5208a80d24994103011174035554081c040c04000b00100011309041920f000e0100b0f0312204225040720940a8200c0000e003000207000c5c82d50800452412101d0540c009490015030702d1310014001d0b17100d10100c000140f038919120780a000384000c088e10f00c00c2c14440f011002d44c0603401448080c0c207180101c920110f00e0306a41d0018240c03031004144000c10000c503c00405a55850a80300f070402e080030581041003102250b01d0300170480c1c2d84a10f44a81d1041c42c003a480c00400c07650340100740003107001c2d2405202d505858102d40181c0701422400c11000e01801002d451200c1720f420150004c00c210700005015140060b0a00603000740038041d28034045d16a920201c5451b0242c0240d0003250011501e41c41c00b080080c03161b40d201c1e180c0e0408101c081c01036282c0440980004040610442d1a0700d8004041429079202c40000c0e84003510b030001c52a01c900d0202c01400b600c132a0682c0343ca25040d000505443d0801c0300340e00654001c000203428003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 904883615 1250 904882365 904882367
    0x6031e07050c01020a1220192c01080105010206071409040212010e0f0a0203220c090e070303020111031005010f021504032f030a050a0e0604120507060c08040303 71
    0x1000415a00910805110404a8940038002030617900040d996401e0315200400d20382003202c2190300440b04000c440c0d105c0c0541468107000b11400c0700004040c100590040c0b0800301d41203554900c0d1105c0c90014540c3c03030340081d110368500820620090b210900c1d641e0701c480049a80341e500300c680e0340004000b296808070a1b05100000d01e12150013a0000d881c0a0085254981d414020392110a2401e03091003041460441e101c0000e8028680c0301081d455420940380034031001c0901401c00c1c3c0e441c41054000400c0040e4040300c0f900815222906005170310242d043e4a0711001103100a4025500b0074041c00000d61045088a10440b0400e200612181c104001100c40c420302c80245c00952191500b00b115106078005a0341c41035100760f543d000c8502c0709007030301c6042030443e045106103d1140041c1c0480440702105030b440e0380c1c00c0d42c6045c0340c0345e03000d11008503809042c01014907001040050003042c0e00001c8000706590a000d43e0854000c2981c0d800212110203420001901424051105000203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 904884865 1250 904883615 904883671
    0xf12091f02091c11011b08040305030c0616050405220e03031e09071401050705030d061a1305040b180c0c071502030703053601090902040501140703031d06060f0603 72
    0xb0008140c9000440e146d030750b200b80c0345902640003541c06a20114203c0f4080d00100040f0b6402000c860701e4181d83d4001d49000742403030086014117440381071860b044048480d1101d41c41d150300f2410f21014010054400e01d015180d030b10645852000b0b502e08404040015800101680280ca2000007445031b14686038080ca45280d1501c041e030f04001d0b040020350003045e0200060304510110120010382946415104041a815000000f00842f002d101600d248888900403501701c0e2000d68001c03450600342c0307000a03080e800a806822000d280e800510172500760102c09461203800c001c3c00ca030526a10f401c180d00307403104800c4690700141c0c4100500d50019200354080c01804641c03400b00020001c60b80783d51504942c404c42d0344441003000b61079074071096a000c481a0000c0c841c1e20170461030b0908220000741b0507515640543e9024000084081c1010712030f5101213001d1a000e00c000313818001038043c90b501da14080c0c0e905485030321000303661100383c605801168098480054051400410100300141c2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 904886115 1250 904884865 904884887
    0x6031303030e07060e0906010804080d090203010b04241202060403170d06030f060c080108100b06090312070c050a06080708100305030a0203040f08030f12091f02091c1101 75
    0x20540c5400b41c01502503010420040600300d079440744403010307000700140306485000802050401c1011400d100205402d20b04079807038454202004640c1c1d60560002c2800341034030a0006400a103860701c041c01090740341030810241c2c0c40f115581c45c941565103c068105201c044006588260104400c0000074500d0900050f0460111561400c0540d142070f127400f150030aa20643d0a0940da001401c1041401c2c031030688412030130f080042055041650300740e070f2400740314103051800b65600c407285600e2ba140401e0714081d10300201100c421802c800009410758200d5042100c416085010115031403400c03132100c83c00c0d43d009540d4007010741c4c1c8810b02240d107014041c11075210220404808008140706100815052071540c006507030312450b081c0c1e40b44202c00c43d680180555041030010301d0246041c0811100420704e00c81d20b051141d2582140076050051449245012071720141c035131081d0b02020b40142900320b0381264819008050703041c0307030901100b18850003030410201096094240d80a0304251038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 904887365 1250 904886115 904886117
    0x1061808213001080f0a050705010f140a0905010f080603101a18100906030f060221100317130510030b030f071502071503110d230c040506031303 64
    0x81c0342d8811046250800003460348400c1400007400140081130f0200700569103400084020007160704651515525852039000301030400c00ca443c103110440c0c6c420031131071f1414800045416901d00d0054405064040c480c81a41d001c00c06000c04611442d02800d01203205140c06000b40070903c0400300c056000302b1951a00c9012021485e54a400704e4440b2002c1c40100362606004041c1c07070a0074138210001d401c8541c0407000d410b00300a42840024621044180d1842c1d22050241e1141056440d0742100700403a0410090030304000b00304040709100304c5541c400c5900524034015421841e0456496521541c0102d0342c1404507184200214202000102010960381c07500084494102e00000e00700050045109401c3d482450281300040c1101d81d401610600c5000034100e06240005200d22207106440c42c4083c159107006030421030360040219101c4100190382045544003a461500d00c2c0980703100e03010b6420700828001001071004104903000c1c0e4800905050850b41c800c0c62401155588010880c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 904888615 1250 904887365 904887397
    0x30519030512070c0b09070b070803060303071208070f05090609131b050c06060f09180703080f0c1b030a0f050a14030d1a0901030308040f05060106180821 68
    0x1882c2e11003440d1156000710300581d9806206907082c00c160603010b5014025045d1500b1204041088500040484400c01d512842c169125a641d00000c1e056014a00003d415110f588418212407075015240310f20038280e035111005020000001221036000c1c015105400c4881000080c1c00c45c03400e1a1900c00002c1e29080208881c18403010300c40800720301c201041c020480c00b00710110700d41020700c4580d6020f142a604000805000800a80762080181c0252802200390886169440c02402614043d50700801c520350b58004600040c0d03000c0d448516190300c40e00410058082c40c21440040300d5100c14000d0040c0040d2030a9280d10b034446000400803140c030b1107401075010000b95413004003050a41110301640d250004024080107030b81d003100031002d0b00840c010f45081e81d90744203401141960740619214640d5565841c01055440c0d0021014026109100c00010f00320b0307000b2841180544855410382d182c41e90381300281e5460814041d14100010600e807880041c1c0c032640060441405821901 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 904889865 1250 904888615 904888627
    0x14031908060a0b0f0405150306030706050d06080a11040b010f0f440c04060504030f03051c050604061710200c0d03060509040b0703020f0f0d090201090f0305190305 72
    0xf001a1320041c81c40c00b040710b001c20104a280341401d4105801c850002d042859072030a980080c0e211a80d074001e04052010124402241100682c4204040d144002c00c0306c441c00c005003415640e0b403401c00d401e07501c10f90803d1245050781d48500108800c1c003803d601d94640c0708050b000d040d40d85405071030305000e0300c00038039440411030804104c801440d02d4030b05030040380541c4148000b00c070841c40101081c02c0a1010401000403030390100442d000c03250400d020b08a1041c00d031404445501c01d026480707a07000c1c1c044040c80001c8819a2180b4055081198204441c680da078805080c07281c0d0100504803107400ca20070b200d100010710f0f0480076000071003407150703182107442001c0700e030981d002264a90300c29484642c03a02e40c00c541600c141006041c08803000200e61405680f013080c4010014800c108141d008900c40d5001c911460a0f203541f03524081000f038031030310061000b000600c400c6100707900244d040c1100140f040300d011000019241c2000281001320070f410f24040d85040d210f2812402c00c1010080 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 904891115 1250 904889865 904889879
    0xc0b061201051302010305010b030c0409020f07060f051f06020c190503070806010e010b2b02090a0b0d050109020702091b04050901090c02010509030f0421050a080714031908060a 78
    0x81911440003d80340411048843c00010100c0300141c1052080d003c041061114408684040d101280c4e520705000daa01d00301c41ca4a207006003d01038000b0540c0381009000e000c0f000107600403512401c825074251188402103041c12000c501c1512413140907801c26204042d0b0344c1040c0024a0080a08406079080c0c00c2d42e0f180400d1600c0c0e8503070b0043c1c455400240041c4101158a0102c43c01007030b00f84030352802c015407440c05100109060080350443d1210315a40c006450858064490350f100080c06804401c0c0d0703a502042c0c0340d52124074880c840038075000012070b80d500c0c18801c0c1c481040c0c001d40f80440c01d03604c00c03951085400f000c545000d1452428000020aa6602042c10703000e4903101c08089010b00c18000044e007521400b6281014580092180100c11030280c810342e0b040b2224240f4045501d14044100001d080640501810901075441100103002d1218001c2200768495000c060a203080d0200c01912405201c1900c055401e030010904d441c40d10451059800010050150082d917940303001c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 904892365 1250 904891115 904891121
    0xe19080c01110c06040302010f1407050714010c0309060509060705030112050c040c031a0a0b1804091a0115030b090105040507050d241208040e040f06020c010204170109030c0b061201 80
    0x100e11045034031131020801099030a00031800d40003a6103c0500c5640401182a140401c2c0240f89404201c0007244010074054500e000a2404803088020080016143c00040180c41006410780714941000d012540749003000410171f00c12031286c3d98087c1144d080c48801103003002c80c40c109680318802c210302a49139680714071410b010080d0a827800583c010503566030140c0070302d501c21f807507206800011b010802000440110307122903450007000b001c0041d21600141c02800038040192218a5100d080031703a5022901016050f1010618801c0402c6800c030022000d44200e0103100d6007000080b401002039042c25045242c1007061400d0030390510720b12594001c100d0341b80e1001645010403250200750900c00003221200a030040c20742e80306a21860ba00c92069911552040b03412403a0348500003814440e403280e501c100c09522070025940e03004482002c6000c0d410a026007202c11111070102203440505106186116526850b000402d00c16a124003400c44030042042d42c020110b4907080203124803e00c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 904893615 1250 904892365 904892377
    0x120f27030304030c08191806050702031509150a0603140609280807110a05010c0506060f011e03060503011505010c030305040813080322030f08091f0201020d0e19080c0111 75
    0x603860302c030001c07d1003002040080c0d40e94480c00904c070b02003000340d0258401080f21402d000ca4420b000e130f010340f02c5155207450800d08807451004c81c20344d00103001c0c1c030742480d030040000c5070300a0001000b00941c001145407142e0003074a00502540c088100c83c8002840200d003035060304003048852984640a0300c3d0b859150b405418121a401402d401e0143c16242003010344015100030310b041c120b0581540c3c1c410b030b42c2c1c0d01e021f030141d8030559843d8500c00301030f8481d4203010207480b0103207000000c0640110b00500a020180103d501c40d5080c80300e003203250082d4403a1242100d505075150241d4034040c0e203082e401440040c0040c0ca010400300201900303004001400401841e03014020b640c1d0f0b030343e6001d0140098106a0b01041000341a0000b00701240820b8103c0912580094a0640d00d050340400150149100c0e42000c90303600c07014425050306501940038060034007a0030320500c4482144011261116090252503031100760011004010510340000342401c044501c0c00040c850304c1c40140c18542d50400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 904894865 1250 904893615 904893617
    0x60726030117010e070f12022e0201110901080a0c11120a02070e040809060a0507050106030c0608090d020d0507020301090f0f031b0c0506090402120f27030304030c0819 74
    0x3400107803220000d1013504a8510703080054901d450414441040f901e440d84540300940005000010540d96040c2d00b0b66140d8150301d08580d491031141030705071703052610541118095442d0052028000341d522046501d4200305948031009070392009034200090545030707415400c0020604065401e0102004141030005075500040c0d103a8175030580091400c0c8594100c08098a07807c014800010041025601c2c0e11108803030301519440000e0045405001d002c20207071044d03081201c00418494070030030f003400350b64544c0d88540e03466440d084d0103903403807604060039001603010000e075140b040c1c410005442c00a10040000c10850390f2034903411812150040b042c1c803210a50f10000081640024410b02c40e0340311049a001300e4140b50312401d952a03101e100e080d00aa40c000b07000c03507503680c5550440d8100c0d4502ca001d01494100150a480340c088201c401c05503d1074a06000043c2c099848568102060801700561842c0d41d01c1e45c088460826500c011038074400d051041d0014221360f0307060a1741ca2046 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 904896115 1250 904894865 904894889
    0x5090f3d0b13240503060112090b01181404060e0c031b2103040504020f0d05070f03180c1701111207022e09080c0102070609021306050607260301 64
    0x15010701c10040c859264000c540d540310b039010ba02c0605451040d10010b1801c0c3c3e042407a1281e0b03a0a00607161483c543c4a2200d04c14a413048110030002c0700320b04a4140c801c4041c001c2c2c0c91590015240d0202c60310f069140d0003120010000400085c5560007651000040740c0a1300d807200d200101080c58140301d03c1d8013840b0340310241100d54003810805d00b243c55404292400c0228008040c0c2219120302c114005c0780d02480d000075145004488110454a0324600c1c50300030030213403400d01001894240031122040001e401d006048400caa1184080d15055030800d1049001501d8171b0080380310b801c030390b0321034407850354031141c40c1003c61910030060455000d14000c0204540b40104009040214440c0404401120400c0c109001048108030160740c1c0384034a0000b40c00c5115091034031480c0070340f205d0b04035190300000300342003040419081f901021388241c0d01100c5181c0040b880b101070b9107041c050203402c0f0100340701d04401b240b01c1c000407040e403106015884074a00d014584814890b4000d8115086c0750328 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 904897365 1250 904896115 904896127
    0x40e030a05040e060a06053f06040b09090d0c020f03062e230a051002010605150a0f120b03061518060109170312040b0105090f3d0b 58
    0x2039040005a000308200e5121001d0343c2000800350071402000003108030743d0081c0f100c0c81c88a06260313030007030885549008c2002429095002d10b401c0d400040b030f03540307000702e0400c08601c480b030411840c02e6000d8481e24000d00081a810300c4100e503031107036118050f0fa1100c01400c0d80368083d10240007403402079501104c42c640e40000400b0107000688a00b141e0001d07401e83e600e080045000c03005201240745094054290550820000503c50402c7c5420031a4841c2850446503903039601503106078104e5a054440e0340394644a00791000c12802000c40e510049036103d805035403111301c194011520380070002c000240d5a01c405000c41d24119040781c208102c8600a0f243c5102854140d84001c945080d41e2a035488514066000908400b0b0b0381c03107020b858902080c00101c160b031051042e581c20701340c19402002546000e0a01c1d516000003880703002d01030f00055021900b40800308400c90302c1080580b0081d450140c070b084906d655681103040050010849900340306a403803c42e11080f0041c5000e001b500e03100c007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 904898615 1250 904897365 904897379
    0x70e090303040519080406141c060501030c021203070516050a0809010e12070509100e0a200415050f040e090619180b090106050a09061811090d02040e030a0504 70
    0x7000d00341003a40c0d8424500d0751000203800c0c0302c103c0d800e0b100180360080e50b401700e54084005502403102c09e0345890300846089801c03404598041c2c4110780d0266018098621110026600e0303000d0341903543d400303070002c00000310507500480080858030140c1480c4200d241007501c46d24204540d010f8200d1351441c5c000368030455903a01200380a92410221008000f122101c11120381d00c99041c03042e140580e881a0014441003140ca4040004210300960400381d8034010001d44010103040440841d1082200d81d0342288008034011b85003a0b4400c011141d05698415000395090740042a25001c0c5c400300300804600c1c820044c1a0703030301615010004184600f8441107034800b00180c0307174146605510707101d890301707031100c4044a03030300d141d500311034008026125104454054240d03500015000180c414000450f0030750740d48000211120501d9204013107050004500030b9070300300742c010b6800d00e8046c0284525454004528078815100800005081001c09503550450f00205002e501003003010900700000303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 904899865 1250 904898615 904898623
    0x30d0504030e0a140f0102010b1009052e08040c12110909011a150d140f1f091802090106050903010e070305060f0717040807050c09010302010f050903070e0903030405 73
    0x9444100c032412029801c1820521300356031807108240c41015103424580099000703600020614030042d0220079004100d46020b403c080c43c61044031300400001200c1402c41c90130345810504400c8441c00d0b042a10042441210b0011025009076400703250010001481170910354001200392041d142c20800c07000d80000c100322550300034000c4045034105440c0a10940404004a070240d10446817000e6424040d03842c0103042c0a40302d50441c02919218003e01e807445101c0c04988600c5030007192907100d0744c802800c1044100c0e290390a064180106c0d2041c0301605881d0404008800013031a030800b42c03600750700010b0b14074100fa4005c0c40410400151108036040038015040040da84100803c1100e2466840c165245001080a4011031036400401c85891207030401c1100c4500c4208410590f00b028113040c8143d62000700b0444a41c403c068541020307040c4440c82e81c1c12640c050315005d07010100500300340e40d103500c008001a8540a942004541071241000a0307010b820014021a100c1c03906242061034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 904901115 1250 904899865 904899887
    0x181803191803080d0f0605040c020303180c18070512190b1f140705030f120105030d0c06050c16050f210403060903110118060516021e030903030d050403 67
    0x200e86051107041c00411050b204890000c54840c0b00000d03000000307407044000b080c90ba00059070150516003051003a070b6002000e1070007400d204440e6507050006041c0540c0d42c1035001c5a00b03421000010741d0401401110603040e41c860300a0400a150014401141102c06000c07582c0d22500c051225030059070030080d10036150300700f808ae102c414451040207490018006048441001c00110091402c0448100c0d010759801c80d502c001141e844d0320704e1092003205500000310024410340202e00002d240d15000555013141c620319180c0749640c00054480101411000f4000d80c2881010070541004980040f50101b03075600070340c06041c131124000c0444e0300340000760f00c1000031181650102c2c2e0351100b0070b2080301c0407070744e00080000300316240b0b02d001c0c0d98040c038440d207001407546400d2260400b6800148004141485190100115030b1802d040710520070301105500010307440b2110b001040d007844101e03c100510720804480c10300923450002440d5a1244041c001840d803031f4000d01c42055017001c110f0361 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 904902365 1250 904901115 904901147
    0xf1f08180f0f0618060a0506011103030903030103210f08090c030a0b0901060b0a050301060e0a180b1003050910200c160f0b091e0402160c05040b18180319 68
    0x7401301c000300e601580c1c60401410a40c0c00682e03c80c041502d5a0081c91000004402442900e4407807400c0c9440039101d8000344010f40314140900b0003084441151102c590302d0990f03039112110b5140d070400003142c40321401440041e0500c14411003100c141d404201d999a0180300c1d0400f07107130340c0ca01540450709560095022010700e070012311450082a81181c2581d0569440c1d29296070803045140c0084c1c0b140e006039016804406041800d0000c4035043e42150309042c03c2500c242c01c0c0010f40017412400c54078101c03180030705500003640a40c00341045030011100c020300c81114507070121807072401e102c042d03219000d44603682c0e002544504c41496418503c10050548810501046150071030b4207040d882100c0c000b9208140c41c0c02a040201c2e03107040340c02210074020f0021500e406244040b10842d401c800016100c00700e04030710004641c5014028282680303809408000144241e000e03004c501c82024050b812001c0c44c0f0415a001140c0030006811000284118a100307801c0c3c000024142e5510900d99003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 904903615 1250 904902365 904902391
    0xf06030103030c0f0c0b1b010b0904020307120609050d030509060108060403081306180602041a031308030601020304211a040302070b0915040803090f1f08180f0f06 72
    0x101094101440c10f00150300100030501c40b003054604055858035980140991000214000042040051524a0f0000c0c544005c010741c50b600320400c80c407030f0760403100258583e0200c2c0d401c0c00b480361a074100e640c14502c200000301d4079030120b0391010304100704a0030b54000266036008110441c01d04018180c0182404005401d03181002d0300d00808583e4020b10f601c903c40413002100c410009c20364050700c04111070340d0034219083c10b14500103001c2e5100303129a202150303100203122100103110007224040c4c0101c203000494a400766580c0082c0d50001000181035020900000904042c080d011a8407101248584502c07680780745050344201d404000b00040280700c600c2003100003600007a20f02c00382c800402c022070311b42422500162001d00d54030710720000e00402080010710f0000010103490225002c59400100c03801110070300504078400140141d14881d401d10340000a4001d141ca2030f006140000442440c0c01680340e0726107000c0c41c101c01340000f07234400800c0351002442030100359005100c5200003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 904904865 1250 904903615 904903619
    0x40204060510080402060304030c021206040308070f08040219033302030c0d0b030106170105090606040216061e1b0e010216090e0316051e0d090303030518100b0f060301 74
    0x9002d00f500420081c043c600c0040071500345070191101c201c84940c0107080c210140300a08a590320b41030b00382c4046011510b884d01203041d02d402034000c40802f003003690355200b00b50758680811440290b52684c2a07002c081d0001c5c0480414100000702141c9200006a9070400d4a4104001007007034820121510491052080c4040441001c003107850b0311044840204500318900c2c0003030b004043d60f62005548a031035809001d10f0f401306411071441601d455042d20f4150340d46e082844182d00c207a844c941e90720356038920800d001071001d41c4a01120b000703040d00b030403e5804054407442114001441c081e0300e00c000a41c2c2e464880d0344007a0b20203040d0000c0c030281c0350403a0525031350170b443c50940c002e00346c0300d43c0c0301c4070801001c0400b042a107660640b854050701c04410982406502c507003030540d817a18511140240800150800190b011641c41c8070395568039030506d036450880c01040c0c060301c9030031401e40c60700700c5c0c0003906810800d64212100440300003d00e43c0c1001c080001c108011000640121018001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 904906115 1250 904904865 904904867
    0x18010b0301140f0a27060611151303110309060d0207110a030b0109090203010e0d030e061506180f0a140a05040b06030a11070803042301051006051803010212040204060510 75
    0x180200c0d258003440d4804c070301111141d1400750058940400701785c0d03d0035000282c411303440002d0404030079444090703070360000c180304114109010440c1c2c3c403515180c3d030512440c006441500b1124103d0301d41000c0d642480c800320002001544031a121040458011035180107118103041c080a400c40304544000e0844e145a480100301709051040c5020300d0364841d491010b540f820f40042c40402482415948080c10b02503000d001403989000d0780000c1d201c2c510005c0c40c105c03d5507141050b0104c0041805007031407903058810b018004012941c6e40c001125107444541134a5802c442006030522501c0127024403807034014040000b000354002e902c13079800e00d098803001d0388482040301d40211500e4800b1a650000c0c40741100315100760480100001c4002042109202c0e4960034071102c9440500040300400c00054001c0c01d07a42c0c2a00c3c0c619844640030400c02c8114011001006401c0390786110042845050700004d003241c214680400302164080c040100314580780c80350002400080f01c0c5240810a0140 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 904907365 1250 904906115 904906129
    0x30e03120402060c0a080f0d1401120206090a0b0726041809020114031e011a09010320040306140c0a02120f04090501030f14030c0a1118010b0301140f 66
    0x44060b00550f00010b109421100901c0004003180d0401c1c005a030f41d50b4000e40c1d0000c10340c4002d40400d00702d0318203003980100040d9009041d0480d076001603141070021070b9408000c03041d44003040b82580312841e900300003511402c644c05022194000e4083c44644820523100b103001d0050144010000e5804010a008010041c2d1221045444600002440c21401c4c401a1000701e88440c03c0510101c0c00720403c01101f50111450380440fa0801600f402070340e0311021401ca400d081140c2c0882c0c142d0501003040076500c2a440344131118610419109400c8000700400c4650b03201e60001da9180d9140c2e10340080300a00d50822642142d07c3e0407846e840d06400c203400075241e08507880c640101c0e800000305040e0385d0514600780e030007502602c081004196900e2038000908020a98215120405d068100164000c04003d8880940d01c030006844441c1041d5549503045002000c4164401c403c481c003c6a01c00040b858240a0702c2c2748040d06589504103101c030304020122118035441a614020600d20b1922204 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 904908615 1250 904907365 904907371
    0x131101020d09060503150306010f08150411300a020103150620010e0312071b050705150706020307031d01060b0d0c030902040912140f1605030712020607030e0312 71
    0x450113586946445010700036200c2c039000116418880d101c004513908400e20021822911510203d84000742e1046608440d02002c84002e80501141500c40403181444120388014507440314000d90380246803c4115946d810300e0010314001e03130240c03449504558143c801d0704102c59038107004c002094074144004111a00301403d030036a20451b64100301c540142500183c1c400c6508400752078840024804094450200700d034042c000400181c52100d0252050918890868101003d410124148010306c62480b0014180d2070102404010bd080072410b140302842c0613441690f804100008120030207070200e0011031130403000b41d14200c0d0070810780401004032001e1000c11203001c52501c0300c0780000d0f0005e00301203001075005420440480100003038200c650359005080d89030b101e40a501c0080044a50145c5940540c10181c1005204202180d86202c0a00305110310100d81c605145942e5148a1540805000e00980c1c006c90a100803541c240c014103140074401320041d170a14644011038000c050003d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 904909865 1250 904908615 904908617
    0x5070f08130e091609021e0c0307080412020907021612020111060f1605160b10031406011a270a09060b03160215040b0604020909131101020d0906 64
    0xc05801c08000440c0110091540b0b071500c01d50303894541901c80c0c0f10b203041c40c04e108060b51441d0f408508604a40300395424880c00b00303002004140c0000e85034105038800f0308210754078031080c40208005041500100042c00889948180c2221203105002022001414250564110b00035456806543c1000b0f5412516200004d1400c0c9040e4001654801181e09051105000d100f0402c000101810405401282544e20910305224082d40032107040c0102380e078031844170014040090210b40c00408880d004248080e5136118540e403941c1e294508203c0c002015450f411200c0100046c40900d40c0000030043c942645603e0083d280d40c4640003140c1d12212071550000e581e44030543e41d210046860040e00a4100401c41561219015155500221500c00010741e0541801d11003610110396035807111070000f1002c3c03190f12156560058104001c05e40b58105a0a0040e10300741c4d521101c4650180342c1851000d00e101441c0e061201c840075443d0000c1e415036200b520b8000c40681d214034103074102c0f2a1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 904911115 1250 904909865 904909867
    0x30f090f091909030309080a0c0201140a0504030602090a1e06020c0a0f050105180402030702070311030a0b0705071a040b0105010810141005130305030a2d1b051f0c05070f08 76
    0x43e034901500100401040030301140030114041d040f1301d40240c014580b00307000740c1324201700c00100b94114181d403040d0341c1d05800082040c842000020491340141039011070041180c0805a19211030f01840100e03810070340c0d45941a020100145601031241200c0714505941e450b58417403c0151032a040e04043c42000e0401000140c400c50904407424240740d5054018000d541e00e041c5480003d40d1071240d4041a03803201000c440302c201500c0c0c00101208141d81c4140c0750f5035203a03106201030f141a00a0881940c01200c100b03410a01d030242e0120083c410b611422464515504040c0010444000145004071f100c00c412070138091410040c000c5003c2c0e030422510000210010441100c1d507016160160309001340e9144007004014020015141241c10355869640856070b0110b0f04000380c480f60868045600c3c42c26410181c18400c0e403034888441140710004800f12031513520702d8548912072a541600d0b950501100200100ba4050601c620b100c9151080c10400c658880240b4000d07808001421814 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 904912365 1250 904911115 904911131
    0x20a020a082a1e0115090c0507060c0906030c020a031418030604050604032c062a01050106020709091505090109050a11100c240608030f090f0919 64
    0x8481e5062442c050640400742203014040c001a65600405180508040c0c0000c50926041c0414850303108860800a9842c50b26450f0004841c0140004400c0d074013040020400301000c5080750080c4c240c02840d81d0345e41079511b8506a00201200c2d0400140790443d0000300c00040429072002248608a40041d4565079409104031008040c0c544001c00329090300a11040000780000814610b210740c0c000e80300c0c000d04a40104401344818071030004446507803881a240c3c10a41010f401030107100001c072316000002e07980b49840d404003008414000342c1c1070703444400502105034180a40c1005285a00c8103000f444501d54400c64001c02d0426030009940c1d90310001044c0f00425008010b0392034100050310020501410040c90328141e404106000d88112443d079180d45200e01021710340107402424060790318822020b40c1540e0070f03290141c50580c2e622404040354441080c002010701c00c425900301542c480410317007440410118514072a00c40c1a01d00d00300701c0d9004012000810030241040c00044203d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 904913615 1250 904912365 904912387
    0x70b010e180d111c0215180601030308090316062f0405090901021b0604140703020a090c0e280e010506090d1b0b0325020c0f040e250603020a020a08 65
    0x4503103001c04e5810383c501d0080f00740c901d401207a501c0b004a09800d500c81d19580d96031800402401c2c98003902500d900c40401000805c1c4150750f495008003404058924107400b190850343c089000350f80c00c1d2602da03030f04c0c00c06c0403206c40c10542000e11a0041c208250810342c01c40c18280460045120b000d024801c0000091651842035040700c1520084032640e52140c0c23801c0e01d14507501c9904550484441004400a407141c800000f90203045a9000f880c01c4147c40c102800c02001d8001c030740d0254140450020b0b090460b03035503c101903404901c814015403d03031ba000080110490810390006402c0001080113000d20386841c0d040304c070141c0c41a00c1f40c0400e91709a242860b014030102181042c00710241e800031640c81d150400450007841800c001d80c041003144101c1d200e4941049c159075000d1f03800003404041e14140101d0301042c0b810000c1002441000300c03007156040008075002d0000f50180c0038600b202e9004a1030010010700382d9840c0031070074903081c0f440207591030394040c2015240c86004182d04070a9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 904914865 1250 904913615 904913623
    0x1203110d0e030c060a020f07060b010318032a0b0402090c1c0b041103060307060e030c120c0102010c0c1a0439080c0f150f070b010e180d11 61
    0x5145403030010000c10311003504040d00c2c1d40004804000a0051801155940c4101c1c002e5480322603c0ba90140d107420820b94984000f000481070841c10300d07494002e204ccd02c0e005401007003031f0968000d88407030113402540034201c0610501060207482d008140c00303841d000305103190f0105078801c0d41a00c41007216110340b50542d0040c00390760128000103500500c0c034801001c082d000140c200009440600100f4012008144107000031501a0340540c02140e0030015984910703c0069965005404d94800d41c0b454408506c0300500c00385880010382c05401e40b54a6541e091144209072506480c0000c0040c900c0e43d20418940351759240071075100b05500201d006c1c40300c0e809801c2520303009030341500b940c4121303585508800404411548610041c1c68000901c1c0c80010541d061081c0d0020041000b500340401000950044409545110309050104500940300c40004042080c050240803101e9850104016102d101c001d060219039611408151399034200003804092004160414480d0138501508803850 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 904916115 1250 904914865 904914877
    0x90c0e04020f030625141606020c030a03060f2c040507120b0a11040602030a180b1314010914040b01030b13020c010e06090c0d080904110406110a120311 67
    0x103d80034420074401d1180102c5410070181c1080c4540079441012800180c5021054010a095480081109040c200052186c2010700f5215120050808d04559100b0780745030006d800120100b9a680fa09020390340d2009450001000c100d2520300d403560403440c9402c1d516000784500369801c1800c0c0042020484140704001c083c0140c1c07248440c008c101400c080442003802d4500301c0c0038918080c44400005ea1701c100315400e40300c0c2a0011803401d4040701049030103810350844003e00012502010034010750303900003003000841008111544504041d01101c08408864555040c80042c41003000104050301c414802c124044500044010301c1c1001600900411b003e0a503001d156500d01c480c001c10640d000d008100c41c80e0000b0400c000505e08419620031007918108482d0303001d0724086d000c078034000442030a1144a540024108004200490309441001c04041c01c0c0714804035040c07007030740d900031890500c401c45600284081c03200c0343c070307074045242c080e0858404040d143d0110702901e01e00b440440d82 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 904917365 1250 904916115 904916119
    0x2130315180602030103021306060e010c1a01081c05040e070c020409061103090d030902090412170c190c0b0402060c120c010207060c0f021b040612030206010e0703090c0e04020f 78
    0x1d51104503140440c0258402d00049100d062001008000d05e0110300c9210240e83e861b4076280c18060a07000190f40c902417289080b250900103080000313070340700d03000c010500070806040101828030420161440184100655a080002c02d02040103100002c1120540011031810314119507140c900119005c0d11240d140a40118141100d000c403881e0380e1401184206550010b031201d406001a0890989204040103544802d840010801240c1d84071001c07207812000b810041e00303900b1503400c00c403481001100c2d41d41c0030b10000704049001420541031725560090526018410484c2a40c421245a034090310190003484040303260307400c0100402080ea000010b5441041d21154100c4559010f540700d6801145e5a606048104a8490040301211500c44141d005407400040844100c4c030a14600d00181d6842a00d40d1000100070344034801c1e48555074000d0703001d040e40390b042491000e41c40301c002d08000201490010b840d4089041041040c0641da1505204030964485d800060a01e441ca6800a5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 904918615 1250 904917365 904917401
    0x6030d08061908030c0c120f10020d1506020708160b07030e0102240a0e0c060a0c0501060f0e043003090614090f071e0e090f100c021002130315 63
    0x222103100002d16901e040804990f40c01c1d01c107d0f030070700711340c0c039080301410302d41999204002d99004200d064016001d00c0c81c50f0440021524001c41c41510341d0880750b440040540c1001405014a078414414205001886941d03a0324052408600400c00c0c4901c1c0c2018041120b401e003064842ea10030b0005810b004400b0348860301d5490b0284211088903010380e052403225252881c8414180c00100d48800000d2000f01200d040442039102504ca40c000c0000883d581e5598000105441340100c100001410341010040c07568585407915510841c02c0300350f2504824402e0300e0401c401d044a0f005024609000d143c00305c1e5002a40c40e220000d0042240c4140701e403089481004a01d440000d210300e0400134034801c80f00750580d00c2c0855a042c20440c500a04001d0021074144642e1034861201a005614071080701c0c400300f082850f40341400d40540001140c19180c219481400b903040120380038041c11b4039400c62030f12407010002c04021440c1d01c801030401510710214012000141e005040d000018805030b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 904919865 1250 904918615 904918627
    0x2190e01080115090606090b0d14040f020f0103060f09090615120c091e021b0a0b1006110d110a05070b0a0f0c05101a030106170606030d0806190803 65
    0x50b000e4801180c1c44003000300318441c0000c0041007800303000c00300e5065496070384106007040e4000e1502d80c410201030458540f038030520903803107000002d09232003103014803012403800b9802c2c410400c6000d82c100320181010306041092062040d0550300804030b44c1c540d0000a11a07209140c584040c0c0122014400111404940040e02919407070318021414403503161900b100e0788038038810342240c0103429042c0d18001c0e4400c1d1210805442d5006100d041d0f44c001c030780c2501d50541401075140c40ca50b1101100e038081c01006019403175420442c424041c0c603490034200c0305590000003190380c0f04003081c0c00300708100f84003200300d040c40320521051140a030040c3c1554852525016246010751140000000003810303c0c40d454000340c890044e03075408a611401030712113044c4c01c10030030740030381045142c20780040c6030140d00a0701e41d40c1c2440303910000c124981405240c8888000f04a05051000b840f0f54041c1e00103812001210740e000011941c402c0040307038014101c1c00f583d800307401080b51582100b19584000510 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 904921115 1250 904919865 904919879
    0x1804020a022b030623040c05190c1e0506240d0308010e07050703050a080c04050424050d020d060e070e090f0609010e0a020f0f030d0504031217010302190e01 69
    0x103242c10314902d0b241800000c0ea81d0700b20940c92010001c494011103240104ca00d828a0a43c11040241c501480c5c810304091050051078420405410b031900442c3c0000070034000c000c00c1d0401201c2d90789121090100080d620344403651120001401c0140a420000130791618100c03c1455540300103010b004c202d204a4070b4030380940380c04004c1c000c860500d05d1950002e22228450030813500c4e419819607485042c628a11801d0301c1c51680a02030320300122007800042541d403101e221703d030326002481e0f4a0780b10368042090000d80558840d00418014200e01c2e55940142c0c840c1d401d14480700d60b000000203580e0220101607800e11909800c40425000400e00744000740c6000140c0b100d4445901c4c0c2500d41a48503800784c2d90896424041c04051030300880980805450861480c44d8040006083c865020500c0e40010381400c160750124004100302040900030301c1400c00e404034510101c1c0c1842c41d0281d1500c0303101d202c1e814051000038850000c2d90103102400b5026182c1c140201403410701c5010039611001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 904922365 1250 904921115 904921183
    0x1906060801111209060103030903022110090b090a0c0e070908060c090909070e160302090a060906140c03070b04050a0501050709080d050f0a03050603030f0d060504111804020a02 78
    0x507218519440c0703c0c020454612011070110304a0b176050b221541c001c0d00d5542032214401404411107140c40303d984140110403018020f90041d032589690000d45d0700001c0c03810802e84500a802d501a5502030203c010000d0300b1103100c0000c0d24100400201243c1c1d450108480386a0a1781010400f07010703070000d003d052005800502642c0504942c00d00d426540c5104035071b41e0315000d01c10386c8203400e05a404201d0312500c0090310030b01355170f451401529101e84c03500810700c6440e4581c42017000404120040041030350040280c0b001c040003014035407815400c2504103075a4010f908020b0980c903040c501144c20880100100001c60364460002c1c4264648440094070512452003040b1007401910024480d00348590111000e48203014103590170b00b0380707418045005003001002660103100030405400d0b40d01d007030406000c24090456001c640d15081c40b05000c180d842000e020801c000d0141f11581414543d030000c0201c0c00c0b42a18010b807a86800501217140c6078a5105440100781e1098020380d6a07101c503c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 904923615 1250 904922365 904922377
    0xf01090c030b0112110111070803120708010e01081507030f090b0601030506040c171e162006160e0d03080103060b1816171f080c03190606080111 64
    0xc03000b45480e81da40d000444000810306008010204054080c8883c2d03004083c07002140e00d500d0308940c0a143c49000d424510f0b8426240b0001850007034081042007540440c41c4c0c0d0240117041005641549002002c0d0365074901d00102c50721008800c800a01c03c14403951080c5400a05800300380704040e5a4201682c0040c0103440d040e0029081400103030090602d409502401c03042a92a11040024030403604500c1d00301600e402e140304000c0c010381025080c901c2c1e1103401002c680309240c04040400703c000c2e0100070031103154400c0c5401e0b618014545080803c589038000340564045182881c0168111b840002003191254007041d8858060140b59100345058103030307031251208000440c0c200c02001040c40319051041441003481c030004038480b04003c2c114030b42c03401c2ca08041200310f508128080c041c103421a0254614940d00c440c10a00c2d90b85d40d14008004d242840c090440c0310000340106c1c4d02ca407904003c500950750242c4404d000c11050782e00120040410f0300080049505030000003d1644c045 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 904924865 1250 904923615 904923623
    0xc030e0a0605092d04020306061e0a030b0a0e010e07092106150b0702060a05070515160801060807030b0a120501050106090f080a060b0d0b010b0901090602060c1602030f01090c03 78
    0x4100e02c00941070b0b00755400700121108130728019149610300f00400383d8001403102d0341000090040f1600000c000c0704a0304141c8131040490f4503002d40840080403101c8050102d4070402c80b030310040001c11140c4c031280f03040d100d40c98007a101c196210801a18024501d50107030204030220b00e40c0007001002d1800700310200348141e00621510007940031809422465005400c0300140c10880703140149042e10050050b5003c6007881d40c140404d0751102030618098000400c03541c1c44072800c110a1440f9054101c85101c0345061500c0b5550506c98010000d8174000c00c154203041d0f44001c000300c0b543d200c00400b00240b20313921031140b10b03511520300f9a020341420320414011502100c03010a100c3c01c844580b806459400d0000c0c420a80b06880d00809040c02142541d00058092840c8000c0b9441c0c07a0070034007034410340704048c0e80c076400c0f000010007940c8503900550840d04500240300322000c40ca0308a9458100c00d4500c000d1f0060540000380c101206192280b09643c42d00114a042200035945c0f1811613000d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 904926115 1250 904924865 904924879
    0xc060e0c1203041e030206093604171207230d14090a0b0714040510020c030d030e1c050c0303070e01030605010314060409110a090f0b03011107030c030e0a060509 71
    0x100441d003100f0b113401c900000398000c50a1050041e982407040c805035a000d9103002a1101300900c0c1030505445c0c00258150480425035010030042c071107903030302140100303500c038025914020b100e0820071030380c0300007812100030446402207841c800306110018610084000c03007290754440429200400502404607111000403415001891042012034002e0450b0b0b00130300d48420b113990307a40088841c0c4040305460b03403c1070020712005c40d0989036013511151068040e0003c00c55403160500300b500c0d2106031a0750904160900c142d4034100000420151484100f1074441ca090191031001074a07540144030300e08408d84000700800401e1503101005032800c0b4400e8130104401c6840704011015031b050026024060150710000c10101d050540c04281000c1c041c604102c80c4100340f01c00a0302e03500040e402002500e40320004d80f01c40311100d2264401c0080200c0c02000030842c40d0311500201c2c002c8242c050240034410b441d000502d4060007401d0b003454402001c8046854840f4405402034018803411401603030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 904927365 1250 904926115 904926149
    0x815210604290109020f130902032e06110a080a090612091707050a06180212010216020d0c051507232508070608010806070207060c060e0c120304 64
    0x94a2120003a125030032500c2811503801c1051400281d07115560520f86e0174400c110f21000031000c000484064105071030050b070b0f24100382c4214a50386a03411845100c0144010002001c0e010160004080303980307908214030b000c4094a400ca00b00310203124050198040003403100e028503071041d521401d0b58016100c18421003240440d4404a40320340c54001c12501c0914045611a104140548002071240d0308482e0f140025a980b42c00b601c180c00c194100e610000e09101d400c43ca0142001d41d40300303405100850503c4030b50700305040c00b0700c100000a030248018185984c1030011038601c01c0c0141102620b0102003005088a141c1c41c0e50022100342c0302002c40e01011450840300b00c04441c0c40802000c002c194204a40700c032000d00c024440002c3c2c0c100003c0c0c1c1340009034444140000c000030000e83e1120f0111350f01d000034150410000070219400c54010800600c410341c0c020316500c1c020740c0c01940002d80c10015600303642c075240c030402c041075004407003140c039201d2840004001c1040d01c5140e0241d010020b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 904928615 1250 904927365 904927403
    0x60403081b06071805090606090d140c0d020a03032001051914040c0608060103242c0103030305060a120f0302011b090e100b03190513030815210604 65
    0x21590001d1500c40003a4903401c00c1036141001840b1f8108800501c42480d0030f1080d00002c0410754181800ca07003203112441d0a0f003600300c0034005c1c16007600041e2243c010200c0e4640c0002c1002c0b00300d0100170244402d44115000c04440911300a002940800080004d414200d1401842605850001e00340382e08081d0181038130b43d0910381c581d00642d40300201417401070a10134142d8014100500c42e034105556108207004e04465805803410b00c5142042015003582020f03294051308d14235110100c41e0002d80d54001e0b603a4220104100c0c1101d403d450001503d8070382c90005200c2c0c00041e40b16100e42c20380a19800e052210701b0411400c658032a8008000c070390724801c41d040106802100703100100c0c00080341000250f105846540e03002e2820410310000340d4403003d409046400a4030320310a0039940400c171015000d11845140d030003910003280c40c1482c0e205550001c2c0540b000a10f1480080c2c0400b03400103898030381218010340010901617a50941d2480481559158411101924a4a800d46813102c0d24 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 904929865 1250 904928615 904928627
    0x60a050f060d0e0c0406120b010501020a12050d0603120201020a091e0e040203100504080a0807081b0703030902030706110105180d08130506010f03050f060606090f060403081b0607 79
    0x8102400c1c450510088000200091400007150761080c040c1a024500980d00e51103440090002c2c2c0e000104504681e00b001041000143c00035810741d80003100d001701050107140f801030500b0709480c185550744900a0100040c12444d8001015003001e032031049603294042d00544040c40b10359032050300199503a04031124400c1140b080380e00b0000c0b600c40a011078038503040002c1d070040c0042c0494001d400c1c0c00c03042d4412110200c500362512030b0f01082e1400003d80c0012a80e40290452900d82c81505100035031560150340f1a1000c0c0a0020004038081014003a0300712003002c43c2c0050599804c60b5552038090329031707610092502d03125480e0000064858041140c01e18014004100405d1a510f1607542541c02240280614100301280900380c000120100001c5000e001d1000610020514518019142c2010311620340400e0300302c03c082243c0c42e100c2405a0f0f030b03181c900300c403c03141c084540c2c008503540707101b160070140840030002454a000c03800b01285094140d0203a04551043e581c1800072070b96 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 904931115 1250 904929865 904929889
    0x6010e01020c13020f070c090e0d020601050913030215010b03100e0112060905150103080909090606030c01120609050a020c0706081b090406350d02060a020d06150206060a05 76
    0x1100038408046000e00d140790380a0710281904e0380e9080d1030558a6203032018011f41c0b075800141c1d0a03895080d02000c410b0203005500b074503441030000348000d506000004a0381310004200c06201c01110180c40145403080100e1080082002001009540c41e000c07901d103035500440d40f080b020001c0500c0040c226001d01e0806040f40e154010161f100d411560b100b1000c0c0c680900c0c151007500c6280d03c0540a140141c0807a8001d41c0318003202551050f020301480a0704400425103003068002c41d041001d240c80100c1e54400c40c01d424a003403000c0d00380c0c54109400420043c0c1166150700e2402c400c201401e1000d074010700b00d0140200854040c01d50320202111a40c3c0f04850140740512415030f003090b04682c040c081c0042c0c1e40024008189240c07a5202c80341900001140500f1200c141a1041c180030342404e01001c4951a2402400943c0d080590117561040e01518000071181e00103090070403540e042d88440080c000880040c000a591140b000355100c1c1e05852991260400f0310001a46103840c511034a5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 904932365 1250 904931115 904931119
    0x70f03090b0406380f0a03120320030105011e020304080703030216080705010212090301140a091401052e0b0f0d0510060903080a2d020c030c010c020d080906040e06010e01020c 77
    0x91078036401c000d020004a9409440b42c20888030003007c4001032262402140d40710859030002480552202c00e035252100000d9020071841c0108014005664000d00320700380d1010001d904941180c1241c0100c2c5184100c1d40a020309000300032002c410140c3c0451aa404503241420700c0c03581c1502c40d0805a1642801d00c80c2c5809a40300e03405c4101000e440d4809441a240d00a00004502c00340803000804038404940310001541e443c1a130700200700f03442500d40342060020008120500d802030560f141c80c058984000c00e5180d00300b50b5902800c0128083c040a00980c2c600d150712a43c127001c0e8007006070000b0504100c80d508040003d80e101c1900c500130011290940c0d1082425031940d100c030700b102e46c40303070000108009003204d02d40e0042118079000720b45e144182150480101d9920f10081c20319455a081c288242c215051558041ea480740040b502a074040b29010145812807826035403e03c200e41100381c100c1004180080d0b103400c00c10101c0c0c45110700b80c8845142e0000400126103c1e46400c000039 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 904933615 1250 904932365 904932461
    0x30c100801120606090c120f060312110a05100213140924091602160e0f09030409050f04030305060315040b0a020412122006070f03090b0406 62
    0xc0380e408500451100103003d4a00090301d0303a00e0305115401d4074540810000414210300820000c1d0503188030710340324051030000c104550b070700316a650701644400c4a41c2c4010403444011042440e10140070400029501c02c04844408211400c0c0c40041e400c60044d20b00c030350035441400101c4c20030840b102252408000d028045550b541003901090700d00501118408042c1c1c0e01d940b80940c1c03984000a8003500501a0741006404003010003464541040c0c008403003030380c80c00c0c07003000072044a22005030043c0c001c3c0c10450b6140c0c1d40040071461801030754400d64850341800103011f0007401028907903000c0c901941e41440706555401c00d155454115018801e0240002000a80444d02e048800c1b5001800a407000d407400b41d94a40b681100c07943c0d030740159000d8206102030084260031140d02851440a181070a002c102500c820b25102d500040000c0d0520101c203c0d0440034030711aa00442003281c6c8110051414202428618028040d800c0c1c0d0200d0300780a04403049000207a00c0c0403201204e085220380c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 904934865 1250 904933615 904933619
    0xb040b0f090303042d030c02040f0c021c1103040f0e0604090b04022b0c1e0308040905040c0e0a0c120213210f03080906060402070201090b0a0e0a14030c100801 70
    0x1114911001840c1720701e001c000d040085400c204602e034800d00ca28040d690720702e0340d0045801044101d4601404141e0614a048410140c00d50082803580f0101c0780c80c0044110b403149403000381c401d41d072621068409030100190214100b244c080e00041902c2030010402e1072591190284030840d1f100c1c2c10080c2c120151480000e0051422a01e00703240b02e040609100d00340c101c0560080c00511517840104d50b40f04550324184007a4035142c89100c01101c82c41d0903003403118074617180ca000703070722a501480c0d003001c0d00ca40004041c4070002a4003c003d0207030030a084400c0c540382a0401c010004a112000065481030490035502028026034100b0381468103039261207403030701c9011424005441c1e0101690700100c1d03407080c041846030058001031406919070b07111074030342410f8160402400402d1603100d1403050005c0d00150340d20140100a84000b82c1c2c01b030b583c40b0040c0c07a042d100451400716503a88442202008110b48140d140b81100b1041c00750b00b110501c1c6801c43c00c0200034081141a500003030000001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 904936115 1250 904934865 904934873
    0x1403010b0904110d0e1b220605031006060e03010c0e0f1c03050703140c0618011d0c03010b040204180207080c010207061e0e0c190f030b040b0f09030304 67
    0x801c01200000c2c070002da00715288602d00d03000d0300500c50086086965007480d40ca2485c0038040f014411004007104c601c0c0e0120400007607914460a007403103c007410b42295174107c90165901c210040d15000302228889440090300170060400c50150200041d840d61550740030341014014151242d5940d100d005000745801c080c05416502c12014a50040002c03001600382d05415045541c0a40242e886030341e90300c4c6904020b8000b001642c42c41c82c01c500c080165081d080750202d9681c2d000241000c00107030b00c0103424031a9002d044d90001a00d031881403603070754440350030b0b00140041410300150000d100c0d5001c10750801040f40228464940c1890501882040d180b0309a802481141d02c246a1036007014244c403a420701f260041c40040301c1950b69000f41c140e0b855524110418920f01900050041d03444005411f0b486011000115000304100510100c2410840405501906e1034003800e40c0084e683c1d00300440c800e40300b99801e076840380011012441e5140310500040c0300c4c1d007903200203600d95119551 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 904937365 1250 904936115 904936117
    0x51606180209150a0f08102a0c0c050607080f0304020631090e0c010c03020705060a1706060708041e1208090306250e0307080f1c1403010b 61
    0x86032144144250000c0c000503640c11030001d002c2c040d4071a01d0001d4000030414401641300a800480c0340051180741000340200000e1101c80c1102c07440408505100b15004035085103940f1070520441e013010a04135aa00340c1e000c4041e910035801006411104c0e5680c0060003a0340c46a0407020303100b894100006c00205581740c00031074006101501040c03078485145030121982c000c81401c1400b06e118418010340003990714a0400117001e002d0010000c1c0540b901d074142d42d541d44210b0190600881a44407003c2c14003d12034200181000742c030042e5a6411090024401003402000d070f411060001c020070082d05199003503c66465008000c2c0b460a0b041a24540c607000d8513103070030840c48500040128000d0407a40c985102c10b44610300440e201e10005040509160004044c0c589440c40303081d06411138000811000c3d076161840c2060460b01c501400800d090104641005045103e640500441998000b40400ca44c622200b240c1340e14a04440c030450340120b05840401c12440244014030074000150 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 904938615 1250 904937365 904937381
    0x71a0f070c15122412150c09140102010b010504050d32071203020d05030a060801020d0c020c041103180109060603110a0905040c0b160b041101090e0103322b051606 72
    0x20080040103120312011b802030b601c83e15244000110b465100b08024900108107440c0000c00b40000d0003842d400500080050055110780b503c24000301e0020310610900c9507000071543c5200b140454001006480034407425a8203010001a101d070303640004120030388034210344d10203070300d68080d03c031004813203500301c826420250005102a55920300002c1b181401d10080031100300814021400103c1c0d0440a41404221100c4038081d03810301d2100081240501d00f105d500004d0007844081c030b8507000402500400000100074452864014080280b15004000071f0b103005080b101d56010680b5001080140e41303054a008011088101043c010990814040c01442c0300c000883e0f4601c0c80c43d0707115400c0220060350260359020540301072003aa540d0240320480900b20103840e0310b0140d40340d075645902e003540480e100d100120710200c0140c0040005401c0940d0001c0301000c40c1d040b11405100c0364143c10104850400300b001e91801d072007445020380265050400304404c914076424082c0c03503c6014141c08 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 904939865 1250 904938615 904938623
    0x445030804032106151b12030b060c0601080105070513030201080c0f120106080705070807020907110304030302010b010206070f1b061b0908071a0f070c15122412 71
    0x10407043d185084100d0b150b07040352001100101d0aa4540340d100905441c4101e090400c0102c007000030740c036021402c00180d10f500e034000c0b01103248540000d4118000c2a614400c5c0380d01c0280020209160b180001c0c2c8241a500110020801521007140c29102417203514201303610400301400c01c10140d0b004103400390340b042c03000c640c8500e403030100100d4541c5544184c80c03003501600d860005009445e404520187d12400a04002c1e140c0b500645400c9250300508000134898070354400000c000905c01d1005c2d0200b0036007801100d440381e80303074a400b80c00303030000d10f0806005100310f0001544c807900c11070130301c000f040c0180c4400b66841003900141e015400701017429500c841c1c40e07182e00c410818041001c0c03805440b8070b45d611101c10f81001d500a0070082180d01c001032042c1c0401200708c098a42008440c3c51001501d131071a43c8148070311302030b0a106001d900014845016282504c41c00e90460f002c1c1440b0016104100034100c2d0a040390301c59140e04c400c81d519a5050301500780180034850038801141801 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 904941115 1250 904939865 904939877
    0xe16030b0a11070302030c060606160b060f060c0a060f05012103020c060316080105060703050a08090703062d090302030f0c0c040615110d021009060b044503080403 72
    0x898045140b465005010480060b40300003444489182e051020a4004204540740c6141140880b10846801c002c40c5000d490301c6900e01c08620981da078a03c1000000101401560b00c504000d0801d03511f5250201c0141c2d44103042081031302040546101d41c85c1030300c0d01c800e9100e006010703180c0c0403490048003410480540c4503101c010a1241c3d10700c0c02440c401c0a100645035400d05080400900b1621f041c3d002600a0200303009400c0020342102c00d0b1500808c0b9441c00301c400d46c0d07800c0c060034a080116031001e0551450401d04c5c50013a0170741d1403500320701d85891118a84800c185003d41c0121010504081c00580060002020130000b030300081c26480702c00412107112a01e444002011a81300794440e0102ca2480b803213101e6444d4111314140a022120805001c81c0804141c0103511580c1c841e01d1135040302d64a08150741000540d0788002328400002e07004000b82503040f00580e0344103950742d804c92107640d02c0c01c4241c51000e8282d081c0000380d4208040020074403050b907400f580c099034090401c0b428021 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 904942365 1250 904941115 904941131
    0xb011d0f0d050102040512010905070303180306050c0414030a05070603020d06180e0d020a03140f0c030a0c141908031509071d181315110d0e16030b0a 66
    0x81c44022010825000d08001030751180350104100c40740d8142c214041075a4100909a004140f010401c2030403280c01d0700708140800622103540d00c0c4103015030001804e0a01d801d091001041c024405482940d01c07440c080c1944c1c6d00c100c03007016560307420034100a1850b8001b120500c0399601c20380107425800003644001c00c010b911444001c84102e403524a8031002a039030762070805601d004021034407030348a0034006480400070640b030052060401c40d8010341c0e410000207000342c00b1040c1c20300700c03031040440b541685c0c1ca03000e103550700400d0b0210810017940c04032a421142c8201d600007190b02d41c1c6129110702c0903100c1403400d41d580006904000d192004481d0300211146090303c40e842d92130f124400540d90030400d041049500c4111000d00040140140e88603c1480105500301a006030070a40300fa10017841c0d240c1511382042c00900920b02d88200078104031080b02c61107603102c00340c80b401000c0790080c400303c80c41d9085a41e540b000055009040075140d18100301065203c1805078012030b002310041407141d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 904943615 1250 904942365 904942369
    0x111201020a12060b0f3013050c060a12051008030a080a050a18020d050f120408060901020a0f05070314030106080103110a270b0904050109150b011d0f 66
    0xa00598401e801240c914100351075030721500c0c800c80016055072880103040c0450540d10300110f006841c40d0760400e101c5004a8401c0308041c6d5120612500321130400c201a14001c40091004c03ca42101202c8074841d80b00c814226103090015034506040a958680a01c3d11800340c0c01d0140c540604425146001c581c0003049540c014002081e50b5922030f19500300504003030b402c000403150300403d44c9140900e048608020748601022102140340c044508050001c503c0c03d0403800c018802178aa2200e03c0f501415504401030003014200300c0b0500c0c016100300d50394407a4242e081c0d2048184100c00102d42c11100604a0b003d1800b4004050091410a4000c8100c000d8514039031b0080e0040e00100b200c43d0010410891201c0380da0b01d03004015500301d4142031400d8000f130310b13010480041c00301c4650000020700c1c1044036030740320088100d0018440e2401e030420381002e038001c0100f01c2d01500c0d03c103000304150b2018440c5001c0c400c044030060b07641280c19180c5c050848200c048820910354800e4581750450459 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 904944865 1250 904943615 904943617
    0x316090902180109290a1806261b0310030602030f1602010c120e0a0b011d09060f07050304170c011d2b02030405181b0c060411120102 59
    0x1c015810b4644107500038480016260392084d41c8401610324019a460300c0341013040f2808115103071040002d82c2c480c2c00980043d0b0780c0030085140031300d03850400900041c0b510760041d6800a0051581000c230394121004940c1d80c8001d0003260204856083c40444212301101030000716802400100095003030f9803250340b140281da02c1503030800c0c40c0e02c1040f030a02c059403203001c069841050326070008002d4001703103501c06030100180340403401c0c8081d078401e0120318080003885007040e400d0740b220040b102c1e50707110509150850424000405401d02e4080001c03404400092458010751212007800e07025616080b08444940c001002103640d503003051700400081007800040d0420740309443c004924281e010400e44503416207140301c081d06030b200004002d6103050b00f11080f291040f083c602b640d0009140d10b82030f8607600c141e40c01190060602e1080c2c041c060000c206850041158102c0d440c501c551941c4000c110340503c0c200801c0b83d400c601d0200740004c0c0c1d520480c0341887c0c0e025107010b02c66100407034840d01f2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 904946115 1250 904944865 904944877
    0x80a180f030215041404410903040e16020c040603080903060c0414041503080406050408060124030507270314061003020d260405030607080c0316090902 67
    0x800030000014811071400c4040d002806212088407410280380907501e40b10212403d008038003070340e0341d100394041640d952500c0d49501d40d90b8210380b0412098145419018035152510380003000c44020105080c40008002c880495290a81040094444102c2200755988103484c04081d8800c80c03464980c0b44d201c80c041e003070086014000340d07502da801230005d06092903401008520f2803c1c0410040c8403920b4000b00e1681c000505840020b41d03a41a047d101c00241c2d542d410240900380003040000d1007961110080003566101c034144c41e5039036601c0e5002c6201074403a040c0c0d00041c1c412000881c0a6070f10a40c8080e80c016040d14200684d101d00000643d161a4810074071401c0003071401081c03051000058003104e51404040007043d291070980d0744c1d1144d5689074000288030b100d40303020030418400322801e013107244416030031043c6028400380c1c84020240e04c540b180a00901551002581c6075020344540ca04c20380c03204144a142d607895080234400c03d07100c0d0304e20205001c11902c0c040786100c018400340c48 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 904947365 1250 904946115 904946129
    0x90305070e0f0f010e15150d1e0227030307060f0f0b030c0a171c030902270127050c0309060c191206090f0f0606110a080a18 55
    0xe850b052081101c950711500401d030aa0b01200f0b0401088046403c06515502070040c00002d941e1420300e0b40080d0070000710380c0808480f86004079030344010842c0c40c1d1000d190707100d00d200000b4042d200020408103a00400b0406561400240281c0010390104141c00003501030080c140d0b0b28011196031030f081100c540398a04251203a03100c0210f03152074050f02c2900e83e1004120700a181d0307a030308080002c501d80030310b010741d010300c080801c54110801c030104000b003221450318001c9413a840301440010300070a142c0c0c1081c1d01c180e2103040c2c0000d454100d00785000f00d401d0b80480c003151684c00d00200d8504040c00c01c0d0a0f0440e170069285a4828039a144112802a244030503040e03584d041001c8803500e0008041c00e0b03080100c41c100724a00c146601c0300038090103075181d4100001440201301c076440044c185540300c0c0710b10508280405840c07003026400b4030209801c24204008050315200f088680203054815080b0341d0740400784c5440401c1607000a03100103902c0c0d103081c4a040408026440807032003d84e120362 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 904948615 1250 904947365 904947389
    0x71707020a060f1103040809031e100c0504060e28060e04050a020309100c0c020d0803271009060204050406080d021506010c0b06011709100f06030c0b0a09030507 71
    0x1007041601d005900000001203c18041c0d0203a100c424180d521010b0002440d9040001c1d66140c80e403000c0c0403802501000050f4099946000c1d4081e986501e0003803401210b003494070b55506d0700741d80039030181c0b01510031035552180060100004d00c00e1b480181080341259207c1c1d052201784850702c076a101d5018000070782d143c0102c03030100f1003804150741d13028120b5804180188104440341000140d45002c950711010701007040c0c1c052000584821130004030180d004901c1c011341c2014030284100850040000700b4041251044410985504030780241004a05802c015040e043c00c00d4103030040c50400e400b402006203003e6407030001604481c240d41c810102d50300808202c0e00d60a4041c40041c50403071002003a0422450807400007418103150030b6009140180800124010f41d03c51081c800220700c00c01c100d20194186a42c040740da4a40001c4030280351401c041c004e008007001c8d40110412a58040304d400c031200c1c102410801c00b504051301031310070332100e07540010110741c0c100400d000800b030b460080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 904949865 1250 904948615 904948633
    0xe13110d061416170f040305070f06020403060b030c03010915090c05060705010b010210020f0702040e2406040b01180306111315200a0206030c0c070f052e030507170702 74
    0xd01240c3c101e014003c160300310f41e810040417a40e010001d5a0041e0f1520f804e40d0355a03460300d02040c1d5051002c2c0080c10107031011501004200315580a068020360403022100007544203801c26007aa440351800800c012502c0d0f0703074007101403c1e903040b41501c1803152860540558944000c20f810b500118401d0710103a440320b055813142d580511520b880790b808424203600c1d000c0b2031803030301070f00344900b010087c0915951003180004140900c0b4207103e0000d240b80c1180c070141c5400c2455818001030354074034400c5280012940b030342c1d1b01481c8a0b4164220400710b8130b50302c92171741d15600018519488ae250400030100030390a060310155030402d020300400100349209940d040340c001c0206400070125940070104900491500380000740a40f01036a04964081d540c1d0b036102c06070702c580d015480c4000058400e1100200b81d82d03c0b00c9842c0800d48200780c03000601c49240215554540020140c500e60751604a4458105948240c00c05a80714502e400c0c000030703120380c80c4554620a0421a04400181c101040d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 904951115 1250 904949865 904949867
    0x111314061215070e040e100504050601050a03030c20060d020301060207320a0b07080403060b1f08040201050f07050610090b0a0627030b010e13110d061416 68
    0x1038198003000c84010050301c150400420803100000d4091401e00c880344c0802c40013980c032074010182c103440503010340350480c0d690340c55174000d0482950211841e00404002040b030f401c15032456011203030199a5240b0800c4a0380300c01d815001c034440b1a0700494069846030b00fa9856520040c080320345140c3e4016600d604d0440003d08001090300404072606041d090401c01d0145200c14408160f04087d0000c902c400d40c00001d00b4441055000039048540840c4101c103001c0035002410440340039a1303040c007019003440c040084903c3c180c0d0b00d20682c0e058658010040e43d2051040c280d001d44181444c0d03182440c1000c503103030a500a00300848269200804120003034140040b0030005219a4406201d038004100004042e0a190b00a0b40200403030341c864008003901007031920426204c0c084a84071b2554481c180050340140134000c1078440c0b84900081b0b01c0038a8803542c030542603034001031442810031406082016110790f080d01580c041780c031100007505192003464201c0c013401c7c50600e940ca1070b40342030034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 904952365 1250 904951115 904951129
    0xd02030a0917030d05250c1a1801230609102102030a06050702010c021515011b03260903090607020111010f15050607050309040c020307120513140d11131406 69
    0x22500704001d0168001c2d4006001c0078420940c0e80c0c081008407900b42c0d070711700d20130001c580282741000b915070808a41c074441342070101900e001d06888090740b407210303038401d414003040e0442a1078442910018240c100a000009000d8000120504002c031000c0c60140d0002454405030841c1034800319650418001c00c613070240300d001d21a4809001405c11510513011607a58100c000344007103006284000c0b00350f890782c46410315a00c0000740c100324401d2014141001441c803003a6000d1070030070f0880044001304285145042070b205600002c0158503000140c41803140301d82160f0300032418841c54603844100d1407030038081da60030703255840800103040c0c403074501c51000e180c001c1e0b00540c001c540030010480420804800c952806005403030202e91080b40c8030040b803075441180000390401829112010240e40d020b00240101d5031106130300c15240c1d45501e04501000d80c4500050ba100310150b02d5400081c60100c0030114040c80203010646000b80c4038052000e07615811b07445202c440300c060801045250441d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 904953615 1250 904952365 904952431
    0x110a0608060d0b0a0b030303041a1305100c050708070b0601030540020d08130902040b0703030518070b040e07020604120c08040b1b0d02030a0917030d05 67
    0x8540090641001004240b40c1603152401a020b41c6400c1d0000d12000c0b515042440101000b40469070349240c641807043c000c044c0f8403c80014104100041400307012442068150341d5001009002e001c0009559080200880d082c88014007000340405808144800060450203004e034660b200c0b80e140c0240010101c4100611200000b46900003080c4112040d0040070560814101381e089441c00c0300400c10620000480020f6202d61010240b908000c0c490000e008240e80c002c4a07022465100c0d4509410307030140b030280050300c2c4401e01580700820700c203420460f00115601403406040d002c5074601e5042c49a55041240c00c0c0074000b17400c0001039104442c15a003c1e0b480d1000d4a1142081e6660300e61001da8181440100320405800c0020b1010b03550489000b0211a18096501c9c254401c011814880c8103111184070b000781c06241d03c0a074004022512080c0140c4d4540a40a003443c0101140980c070f03404014040c4014408032601c20154030a40b4040e031401080072008108003603c2800c198640 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 904954865 1250 904953615 904953617
    0xc0531020a050d0b182e150e0111030f04030312050f01060815130b090f1006030905120f07021f05030c090f09010e0712140a02090a0909110a06 63
    0x1002421500d079448015280c40140358140415152030000000b40007410b960154411180d00201b4441c118100d404d0020115079042c6080c071003000720f1660440002d00620484006511000442c4000f51003000b00814001050419032128840c080405186800c481200080348034000703014024142c201c2c4640c00217041c644018081840c21f002d012034803002c1842030707606201c1c0380d84c04544040450440f0b02c20b00000541000040302d044040d010281c445051402c0c003c1421002103101da4282d000054480c62402c2c840c0c2c407003503181c90000c4004280290050fa200d015102ca6011800400c0008194400540441b10340350910350040200f942207400c5503c4024120380b054a1220b6000020f491740b003c881c00da901c0d01d0340180c0001c18010254520030951102016001040c200d80341110302e401030a1694071010410703120305c02c0004541ca07c001840e0011100760015095010540040011900c064035101d0710b03a64403248081903a0810800720740a11003416421264242200010b00402c05 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 904956115 1250 904954865 904954867
    0x15061215090c1721041505040915060f0c0b18070503070801021e12040807060b03061e1006020a12020f070b03061c0206030411120d0e030c030d02060705070c053102 72
    0x342644d141d101c0e0b4841e1841d0000c80e81684d2800a0050054030700030004028180b05440c030151a100301c1200d58050803004c03400041701e8807100b61007500c203c2e44003584011201c186032600d071440c007010500c816904029100f10100030600362818042175000b44001c000140c0c5400b460050514020b02545204004000908c04a68191a411202504a0b40042000e0b42e200d4440c140075000c1d007201140c407034151207950180040245451440b859108000c50b0a84054071213248007040151988140701c0140e1001000402188402d51b00c180300a2290040310005582191400d0038074a89a0000107051000b00c1004081d0420a0ba40c50060210910b08283c440960340007c0003400302402c06403400302c1207400f001c00343e1104034a1f00483c54a4100312000c000c007003140103283d940c04015141c02809a00c82c1a0101d08001846554020715a0003803c13284d03464140c1214141c214071400c0c6c070500641c0b0700005898440b50306402d0b000702c0f1011041082e241c044117074086840c9920140708007902c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 904957365 1250 904956115 904956163
    0x201120b0607061a0f01080615030a0b191a19050319061e05150304020105070609061103060102150709050d0f0b0a050415061215090c17 60
    0x2a200694000a040220002450503205004503400740a01c980060101c0e2030285014406007402d030381c646448508994000391041d0f50303401140c14103030584d0400d4001d40c00044400c404c050b1540035640c801411007001420800c0040000c10000d4440a600c4c0b01c10751403102488041d91009114040168210303200d0700c0c1607101b61541034903280340383c48042045000300c041080a20103c3c101459000122018080785031a010080400e801c81498441c042d190500000360605003c082098ac4c1d03440005407500310f94941e00151155400b0701c0d0100c500d559210a92400280e0510440001d050034241c01901c0f460103c002900d4242c0100032109004648020010043d9015504006407902a10940000b26444c50600341e0152140030051020090380c0c10030200c2d10817070b40858800c9000b103041002d10150010f12000300c2e41315010f0031500d1030500780004007007030503c84d48404c0340503129000101844940ca40d00d070258210f400c50300f41d41c0921041c094118204002da114031259111510f207078a4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 904958615 1250 904957365 904957367
    0x30c21060a06030c02030d0c110705010e090a020307091a190e031209311d070909020d051e060106021504020405040303150602030c060a230901110d1b0206040201 71
    0x4040d0b10611040503210382094499034400d00940d1031214008109001c203400d0f120000d091101c901450b1041e9108940c0c00045661003102e50442e41c44014200000d19140c190035400a0360004081034288844868000f400480c1c000034540c2c54102a425191501c1e100790640300c0c1c540c407012925040000600c081d500742d5a005c2052418030708048016550740754400c020030b05240b1440d060115114a61b00c221400c804180c10301c1c0f08407032503903408100400c10300541c000c3c9100450a1012682d0003a00c0c148400c0d07106500050800b40010810b66020040d075035000d2416004114122500c0e107201d032481d1040800b00040f602612041c0043c1a107000c484442403403000000b40082d121720f03100c81c041400c1c0b6029901900c041c0c0098900c00d01d40586902c0060340d25071142104a20f2841200c00050045080d0300c00c900404034075000181029412288a006a440151403980030707541c1c0709080c5004443c460020882c00b040c00101041030105044101040341091301004103542001040000607 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 904959865 1250 904958615 904958629
    0xb060304020f09041b061116080d08060a180c08060f0f060d150e0103150528061509090e1b0d0606050a121401060b04151202030c2106 59
    0x42c0c8182e8030074502c0d540383d0800512000c07503200c8440d841103880070301194403680100c3c58000e02c840b510450341d010140c400049240700c85445444d0b19070f00072031412a00940324608064108100600c4030b06c0703441e111b41103843e50450f404c10300312a403655404030200c0340307800c40009580290125505c04c0040d402ca0007103880d510b01c00d6461841804001074401521600303503c507440c04920100e216014648030000003034210340a000c2940c514821807402980f40e43d080c01194031031031030035511440025203040036049400c101d000396014107840d00d0001c9000000700d100c0806a610742e503580e04000c0e140192004c121144944c04035003039080701004941e03400400791002e20751345050314103401e10300e21410010024000c0344c00465102d003440d40c0005000502d0303800c1d0948540542e03410040030050a0265080350120b2007002c42d580380502041110705e150000a2401200301c0c2803010784030100d40d0311075040742c0c41100c0c010510400401d4541d80c040d8a00c1c2240d191300c442103400b00721410450b00180c01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 904961115 1250 904959865 904959889
    0x5120610050a050a0c05070e01170a050a0f06020717091206150f0315090c0103051e0415110412141f110409020a120c14030115020a020a08060108010b06030402 70
    0x24800f0005120346900d02c03ca0b00e0000007074010741a181c00940b207140c130740e85040d42031040d81c4050f0850f00e000c0d42819004a6845101c03607014000301582c0c9416910b8581d0301001500c15259954240728901c0854801034980c10340e100e0700c0d046a5a1000c05404000425030880490101039000c0e00400400240d4800001820541201c100300004d0b1088000703880c04200c03082486000c0005418860403010000d410140c0c20b000b41c03428803403603a600038600014101c00d41c1d09148081540e0100d07003c16404442c3c0d04c1c13119413148002c1102030288010f01c40981c0302c1e91005006500e000000d605001d10389425040400100300940301c08032891040d04000307282d645d1480c4030705980d0484e200324182c010048800a014003041035440300303050320f00902690b024a115200782030414451032822480b4443c010400620f445c0e20707a05590a000c60020100310344c40301d1000750300c00c2401c910056564420760f140200060401451190304107055142500e0000890a0158a05005100059513900c8400700 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 904962365 1250 904961115 904961117
    0x1020f160623010315020c06070305150a030f0204060b19140702130b0907050a1d03010e03030907060e030d0c02091b0f0a14030c1614010203010605120610050a 70
    0x15680c1500e0501400074052841c894840840c4056000e50025001e001035040b01c3c05144c00241c10f4122081e0b84080e8480c00210801a0308850000b0f85610f02903403049810420030f410b481d41c1e64154002103070fa032607240d41007652014080201c80b400c6141602400c0c01514031250300b035060403a40d2044c8254103130880750350030622415243c10500603031002c041c0d904c20b0b90020b054a41c40704150707401000a0014844550249610b00700051449018008a0348030a0042d40c44d0804000c4200049021050040d07946526548802d4048a4008100301440c051200c0c180a0f1014903d407a401605222000c0724450103038125021046003641c100c4100c008003030701601c4071503469603800340020080a010b5503502064102240e000140b000c2080a48030115140d01d458001440d4100fa2001c1c03808202c0e140320340c2007c01c20410342012194041e41c5041449002a40d0094034480340490030398000f43c00036000100081080740030807941e0810319410101c00c1e01c04d8080c0200d0800000c220f4410040250 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 904963615 1250 904962365 904962397
    0x221060c030717070c03020c0d030516020630101406031801060b04060e04090b0406020901090e0708060a060c0209012105010905070801060e010f05131e1d01020f 71
    0x14107103405200c1000c002d10051650400f10f2401070310180c50001851000c1e0010310409000100505050501c4e004554060302c41c18109200c445030441a20500c5904907000b038024011215074081812141c0f00e02c880c0910343e80c10380c0c00000c1c2481a80340f0004c141c100b0090742a50100710345d204104400c001c0c000d0998017280e403a500d660000614030041c221404517913103410700000b0107000a8010b03109480a42d6a1506010625010003042c0d4401e070b00c014024003000c80100300041c40030307801045241d00604040040b46e503111800e0300700c080c0844103040450500703000c000c051f00c0e1543d170300b0300502501d041403421001d1f146c010800301001401100f41d001d0307281c0d019050094a038950710200f00d6106000744031036051480d00c04c0c5c0782c1003984501001c96003440c41c0070543c0d125020029060b103000c20080c900d0b40c1c0c942010050b00116040305007503e15034800c0e00e40340303403140007074250040140042e000c161030502403692600101e401c00400056441805030480c0c8114900440d514440c18180c2c175 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 904964865 1250 904963615 904963621
    0x30b0109020904143414090f0d0c031112030a0e010e063702030a0503070e041d0d0e180c0c0a0b1005030a032c040f090221060c03 57
    0x1060082034088aa0340751510060104010178580c103074041c4044001a04003240300d40741a03c0b009156448a81003808198100505610200c100d4050260758500609000c1103070100c0d0007203980e14000c0031058840302407002d02031042c00000c120490060f42c0035200044400b8812443e213445e402149462007c010440b015103209a1103070380f0b2446d41c828024420395580c43c404000c6003203501c80c200d4008502241c0c04014907415000d90300c0f40c1309124507402541c45c2900c809030444144d03100405950620504401022094403140b0400720041c42d000b60030000303407050318111450000ca8982c49010406882440356042d25510803184085401c8040c007010703500e03031501c00c02260207996140f1820b40714424140090140d940200c5000c0c072080c5c0040b41940e82c86101b49074a0b00c01d55000038010502c00c2c01c044400c0f406404403000201d03c40c50b1b00110f54055900090241d42d0032100e00e81c1510340b81c0c3d110405503d04820303080a001d001c1e0f00d0407a00d20f100413009640340d22005100341c0b1928804400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 904966115 1250 904964865 904964869
    0x50a05040b130b180f0a060813151a030c0a06140c010608030c06010e0709062c130b0a14030604060902010c140105101d0f15090a09140601030b01090209 67
    0x2454040d010003030403c1c0e152450601c0c007a402414010a80d48614141c06640266003020306041007075500075a00d4a00f1139692420b09070310803200c1c800482e144c007440b01000517428080c1c4590300002d41d84041c0c1c20600c1400100b0545001d107100c0070a4440c46d02801f0030003059800c418180b40007420b0110030794840c1c0c4a6500d030343c010200c03070303129441500001442101c42e00002c150181030b14420445d00e0031b00d8039661310444075400c01f801143c0100759124540c195514000314012085d88110134010040d460501c01314000041041c20480001d072030702d074040728034580081c1402c0a01004070a020a81070464002980c541002c1c0000d000b1035075822000c425640705012036207400fa00310219614082c09070710300e18000d01c0c2c00c8074130003085800241c004c94810401c407140c5d00343c2010031076070704a152258144004c420202500d8442c244030484401c4182d5299500d145101e140815000551030303101d400c1822407c40015030410440d08440c0040c000902c501418078195400c1440040c2c0b02c0e103003800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 904967365 1250 904966115 904966147
    0x71d03011113150801060c0f0f120306060e12100513080301030c081b030a11030717150112030531080a0210030209010914040609110c0d050a05040b 65
    0x91000703860540000c0441400c4010014030003156090820304001858048040740c02d0b80007805510f0010b0210440e0102080070303012040c010074003c03a01000d11013100e0740e945086540a000310710100351102d604000c01504021250000d02c4280c1f81d00c111480c0150a41c0c1d10313103a200008101107035480d8089000300030858070340300016500105c0a55a075859050030b60400e1b94070702c5405054031a0074034041e242249810b0407400d101000d07004015543c8075981d040b4014440c0b240b42909071083d1280044c80a0712411400c021a15200241c003000850404410580c00c1c160030010015143c00d20740400039a001c0d040760140c00381c90110380d620581036000005000c402d20440208015510804101d210000c500988594030071904c40245441d401025416030041230f81e11070200f4403180c803c02444402400948007807c00620004156403500029002c542591898410452001c40d03803241c0f24504222000d080d80396401d00d907040c69a95030005205205030300804501c40320200d61f08840f4080b0310 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 904968615 1250 904967365 904967381
    0x501150b07030c0c1e03060c1409130f05070c0c0e010503120a0e0a1403010513050c011b0c1d0108030c0705060c031207050315120d0c0201120c2105071d0301 69
    0x390251040004000301c9050010311b4001940c245250100c50791143c1e00403041850140259840d260815900a08001f80c0140d1003551500e65078030346480404c41d400b203110b1107200da0308070b03120003142c80c1690400d648234460350780110501205860040c80b295900040134282c01c000d50050384d0f03450340021002c030782114401c059079412803d11000403078015882812240c20761030540081000340da640c4124446019411806040f2f60841500c010f02548912940c0380181c00c1d2982c266100c080c01e58030943d0106240d400100c4281c0c034400c21402e00200a0186801040070707400443c10001d04512254407115240704681c401c81d0000b0f82d8200c03e4200b48240c4814a032030f00090f081d40e00d0031a0000e80964802c0340e4814040040c004002610315080c0046020031401d4002810803a02c291070540e002c0050000c1641440703400c12040320008002d00548291070b429982d601440d400003c40f07120850303000c82119451909007800c00031260380c040103130010901c0b607018810180e1740810120b801040e9036 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 904969865 1250 904968615 904968629
    0x603090506150d0b07030f1410050f030a0c081b09190b0d0204051f080f03030604091b08031e07023003270d0b010b070206041508040501150b07030c0c 66
    0xc2010044490340552002c1e0705000c0e188401d0190038146608186030010842e00303070b0346120004209020505020f5840b1200380800350444370f2400190b102c0c0c0c00c1028560b40444844d9002190380b40c4505c00c2d100c0c1c481c0c034000003540c40030040c1c1403030750803034028240e42d2500003802c5640d9080880c0d42e80d20f454001d2022074010f4804c10003418001c082c5056240003240c00ea0300e841001000080d1001e0000c0d2107801c40d41c3e1000a10305503104c030420070014040e003490569510802608285c1504a1119680000c2042c1c0000f0340c1c0d034600d094400c040358001c4440e40400c41c1c40500444002d130301d501481e01c0008011000c0c41901c1403400c080045084035454441e049448081940c16041c8090344400080c40010600c41c03940d140000c00f0000943c1c0c1c0181d00400b003440c81c13401045040c0001d4041c1c0b00740c910040c81c00b8241b40c0c40f4400741d4984100140e0107070004000d6824401848420b11854807650031030301400c0f0f2000c3c18039008503254842c1403802400c00c41c404040c1c809101804842402130401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 904971115 1250 904969865 904969883
    0xf010207030c0317070f03050c2808342a0e0619080d020f03070302030a0c08090409110f03150c0912010c0801030201080f060a0302010e0402161b0603090506150d 71
    0x347c100200702c2d8004903851009881b50040044070382200c800c0c2040590788070000d854583c80f140c1d64007041500140200881000c02c1d182c0300c81c8405401407050741d442d500d040c2c09103070148a410301124401c02c08040f0503c080445900c0d45074800303000c0040043e030350101070301c51981e00c0b2000400c10900b000ca01003c45241040c1001c1005080402c803203141300d2090b4200d90700000c50200654903031051500c0100903030710410801020f98061218000d540307008080841c2000c20340b40c042400d5a00c2068101c46c0598031882050141c6018410b100000d0821340003402900c900c11f2516075550b4000d00765030180580030034584c420ba9940100e100c1d0210154000740002c0030a6000a001c681f42800304a0200364585e000541c3c1000407000b051080200a0150010794a190010754030516a0b40b440c94008e90200080a4a01d00c0282c40e00401d903c2165025054402e0b0041100c102a242d00003034100b600307040d80e03034011a81c00910a40c2029010803904041c894190000700e4410b1041300003003004037 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 904972365 1250 904971115 904971143
    0x304121b0806010914060f0118030f0b06130b030c0f0a0f030f11120a11010908030c0703060e01020903060a02030a1b0302180909030a080403020102040902180f010207030c031707 78
    0x214942d8100c0b4100401070041a0090420200b0b40c401101d000740c00c04086842450950f101e101a0490448001030501c0b9440d141d4440d910b480340c6022090b20071606150034032602e41800e074400c1c081941011010400c507800b0000185e01c451840700308911407081035940c51000c0d5141340302140240710503001d0050340761b84c920389101c407000d495200340d40c0d803030425229a080382818041098100d11040140c11000120f40e103062005181180c0a4100a04504003181c040400c10041005119a60082038132078503528109054a03040f60504103140d0040c84641c02c0c07a200000e0160300200f01d1003025850740c0c3ca8204a0f4000d00412441c0440155090174148156425900818941c101e058403a06180f0030b41c07040c81404041030b80c1d02c80311944100200a08a4030650a0a810034800d00c0054505640d070b45a010a980140035000c206400c102005403482c80d04680360a0102d0342070014001262464603001e58140652002610360820084801450403108040307807050395004803c000c8041e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 904973615 1250 904972365 904972379
    0x1050d0c1b060501031203090807080f07080403060b03061605042303070312080906010f09050403031d0d0909151502030705071d0709030510020c01090819200304121b 73
    0x203d000c0c40705440e0500f49a121030961486030096046c415005100280340240c40d41c1d0380c8105511040722007a80103420711503280092140c4005000950040c2c0000ca864581c0508142c2000000352452150044005035284059007020a480440c2ea0f1900c0902c252036a401d900d80480c20390030f1000703506004400300802003240c040d40b0044c00544e542d4131424603698000320a55100000c1c0150f16100051800c108004041e82d00440e600602c80d02d0046620810524090000d00c0300762003070281900075120100500d03902070080c0e8001d03c13108000f44400c0010b40311040019400e13008248168280e40d01d0a000c0300c1c000c10490341c90399402012111000c0e0345005076107000f80c0e80041c2019040d0094045023015114115950a8940200150001c00180003482000303610650800210355200d4101c03402140c0500b010388004101c101182144050300c07000140360751403964521080480000d040d8449400001c00c0e9000d50b151000d15290034110341c2031084140c50081d607034080e006e1401d90301250300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 904974865 1250 904973615 904973621
    0xb0108160c051f270f06020a0c05060403030608101b052d0a0e01182606090102070210020706020c061e0c1c050703171314030306030705090601050d0c1b06 68
    0xc0d806540444e0500c072070b500b0820150b0b441440107408403940d21302e21300100341036034000c048c043c00e1400c01c0c800c0891207079070342c0f402d1140c1143c09034042940c40c10204280c40061200d42100e0081910030400c56002051001c083c10360045080100040400c51885044804008590311080c22640016074400c80c03103000c5165001006450004003050044d44540d4003810144e01003410758114914200e050201003450050340503001840300410041d0180c544d032050201304d01500b2200009603642d0458010b1183e040240c50021046500001080100711740c049a05c040851045451507034038404121602c08444801c46c1d0b07807464100019640c18520000640c00601b540090031760415461544000da0340c5020720f08010700400c40b54082e1200445800503020791240c4030040b50052064291140314032951907241e00c6041e40d000101703000d4640307410010440249001c560110103803404100080c81400740637030a541d000d40f6840380082040c000c0f84e14891540c01b214000d050110642401006 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 904976115 1250 904974865 904974881
    0x6030a0206120430030b040b1009030b1807030605040627060c0e060901030b0a090504080d1505010f120e24010506072303040504090b0a0b0108160c051f 67
    0x544034062121805440f00d8962260b1314100f02c060301d01c884807603030784158090315036506480c1d403007550740c0881811595244420f0440c078100d6610f50030814210300d400103000e400a04802200360000901c8001c07198001120401d603030342700001145a485501c0d105000d0490f48403007486804041542c2503c0581c1d4041101341c05000701410704c0001500502987d4a0b002c04100f590892001c1010400c00d5000790031a228201c00503100b22480750f503c1c900c0c0021107406a0303084804902c00580340800091a01400c1e840300c0115591fa12074030301d0b11001034803085108107000140a030400000d894407800380c0c8040e601d24001c9051390010b80c08410700198405071401c80c0d4406030022000441c403410301d038098402c021f07844120006841580700300d44040e00402d442001d8244401c200208417034582c5d004028046214040c145030900f06141180107a8401c0c40e1801c0c10405064200060034090080c0c0c100140d4183c14002d6982c400e0b41401c0707044c075080084100650094405021200e00701d45c1c48401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 904977365 1250 904976115 904976123
    0x8030109020c0d080403080112030c0c0608011e150c08090901170709090c030b04050f01020a021c08070815060d09080403020406050303030c0319090204180b01050f03120306030a02061204 82
    0x44803c201c0e41c060320441e0050300d001e03000072042c5006020300c0b1a04203000781001e01a041c10080f01882da55401040d81164000e440061304100041122442030701d00108a218100b8180305440d0510b40000894000001904200705000c6200c405110000c000c580d60824003a0a00086685800b20703205104401041400c00744101c100014903548540304507845141e00c5010150418034503200d240d4004009042902d2500503d039080380c4a41c800d20003021070310003980162080e03240108003001c05031511482a014040756004020307501d0792105120f503109a00104441040f0303402e2000c20340501440e1440d004980c5808103c8052100303102c040d00499208a40510505454806050322800260f075115040ca00034408540410030070319070441c052018810000300801039400040659200441407400071b04c03604480402c2c041900c1003d8058481a0f0ba5005483c001c0c0002c603a4500800a01d010000004400b24645a80038410960040d070000c0c1044d803200701d41c0700b118501d4841500c1c110703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 904978615 1250 904977365 904977373
    0x50c090d0b010e0a0b030c060f1603080106021b0d030327030503010315060518041127010519140d06110a080f130b060a0302090106050408060a090209040201140708030109020c 77
    0xd00c50300c50500804208180142c0a8000301ca41f0704180401a003000d0005c401186e818030030010b07141c1c104451085440e0082d940c0650070351400742c02900b001070302170510001c0241c00c0f0b00b003005519407200c002c591903810300c0d0014400c01c1c840205005c52651401090203080f408107901c042c076901000ec0c5058030702071075100d58040c2180c01e40708110350712849215006800c50340550f03100700c0c0300c04403207174414040c181c0c070b81d008038401c000604262040000320300740300304061000010045500c400d0340500010313240d090141088501c41845008144148468501084050f481075250650040c4025521038024000c20204c00c0380c0741d5864010848035000034401000280c0183c0100c000d16028025907007856580016640b180343c1c03000030080090b500402d12003000001a203402c2032042c000d0107542d0360a5155810320b21858203010b0040c00440c49a824400c02101596501901980213542424001e21a818134021024076002e8a07101410b1010007100004036080160024510090034000fa5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 904979865 1250 904978615 904978621
    0x11d030c0f06130b09030c01050103240b06040b0721090612020a08150301180803150d02032d030f1903150314033108060405030d050c090d0b010e 64
    0x11540d4600480f20842d03040c0da40c00400010510a0b0702480d001802682a070b46440150040d80b4255003007030340201c88101c1510244003c259a0802010700c0444000c41442040341640c00207455000c0d900803d803070600c0c00100d42d810814102d40c9250901c06035404041040c0700d61301c5c040d1000300c00d44180d20200f0103480b56082c162009201b1214030312541e48981c2041d486107010740c084a01054032254056603038080000b0704501c1450b03941c500c0c0b40f061036896603904d007101c10810207031201120280030f49031002901e0010b83d808501490369078024078081050b140d090074034000c1d50300da1118680445c0000112070364014a414000e00e109080342490b00d03050302c090304044045907040600e001d4040c1c0c29140034800a06071030b904c044d1103005041200c0c10070340c07400c00c0450142280511050300c04850216581031040c07500d1071200070132102c00a00032a240c9038450680301d1069400b01c50b43c0a5440d00018034a07103002041d10840d110141035900014160300c0d01e02c0004000303004400c0325550b20400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 904981115 1250 904979865 904979893
    0x703240f061e0f0315080a0b01050307080c0904080d1e0e0105010e0402010e1e1203040f0602010203160f02070b032a04050d02061b0a0b18030403030818011d030c 71
    0x44801c9014995480f04042c480100088008010780c3c1454940c445c1411400030341c0d007008100500003640101c896180e903524010405203043c1070703070740701441c1900082c15a4020303a980d41c4100c0e80c8160031030240d65441001c0714400009100001c2c10030a00ca500e9080361a41d070724554041d06080c10b403900200417598a40060b10804001164002c0c0060181d254000c0705061819031004a104040480c1c1c51501c07050340058942d0f00d100c11741013080e60001c5820801c0d0b036140c00221000f0700c03d60008614508020504000d5090141c440368180880380d00c26a000ca80b080010034010000c01800355181d007440b0002014117003050a000452003e03a071424140c40034000f0481d411140000c010554254095080c0600c82e0400c00c0e4282c400d4a4901c41c580303004005106000c81d55200e8040d240c1c0d18604a00403140d00c404c80c0d54a06881e134401d20081c00000e810620650704031429401c06ca840250055070203000d40420140303050b000000c08013004d007400b0008050080c2202d9441594100802d140d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 904982365 1250 904981115 904981157
    0x40302190209061315290a092306030c0720010816050903010f0b190308070803180a0321020708160816050a110301020702090703240f06 60
    0x7940c4401014040741d842e243c030079145001660b64500110b02409a000e181c031010080760b00c1800000841035820408070b840004040d10748012680e190304051909a00410000c154012928142c003206c80c1e69012400602c05400c068000815203030341c034070b8454400171460300070034000c80b5454902c110110203001d5101621921200c1039440d11038940d65141103080003c02c521071501448010405a1200d80f020700aa08489e50109808501819040d003031121604400b840201188035460701400010000c004071001c840d0420201501ca0301d44921880d6240c01070758601c40076100741c2442c88201a00180d40204803481e00100c0018010080c46100691240c0354004000a1041142015007440d05220a036038501a040b21802c000d00f80c818440c80c001207110640d0300740e202c00b04800410840c10840004840282e00a6051980b1035011030345522028103a81d081c942c9481c1c0003010b070101905c01c0d4038142e0066084880c426503485c85e00503070305030901032400040d0181c10710304522801c0036 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 904983615 1250 904982365 904982413
    0x8121c0e060a0c11060c0a080708011202010806060f032814040609080f040f080d0e0f01080a0e1501090c02010605100c02010c080f09040f1b11010b18040302 69
    0x100c0684099550500d00100400d0030400580900040c252450800c00f02013004500c00c074181d6881a83e10340e0f04a2001e08040c000502c602c0405c1707480b10051084024131044140c00d141e0a0805290645401e030001d805c078010780e20740303180c081c01c00300c10842c49005c8510070010480aa071400031000031001c420800b40d8000c201d00b48440c01384100800c0004003240e2060f07681900981d0403a040c40d440f65405074240e032181d440740805024105060054401c2403140d08003081407400c08001e0401400d000c82c2082800040145c10312850b4000241600c0ba01d4010000780800c40003030b03178000b40b4541c3d0700300140e4000b03000750048180b60184440c0e403140144100700c10b0319402400038880300300c481d00494180c0d610300f0080b410402d05580740000107038540e01501d0320700c900514451b1221285010300044034101005820b115051074070707107100c144410881031a048014500802c0740408030000b540948940c20056401017060002c1524a0700e004100d035010b14400e500740c0309841e0818095000035081c1c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 904984865 1250 904983615 904983641
    0x1903020a1209120b0606070204020a02100614090a020903070f0b04180e030412030507050105070e09070810051521071806050a08060414011e1a030c0a050408121c 71
    0x500f1034400320340c0ca1a038090740100010012840c103001c0354017050030303a0444008200907034428055420034601c00d00820740617183c1101412200e45840000034403142c0e0207400006400e03800140c54405407414003241c40942500c49a094410782e5803c0c42c070312103a1107449144000039181f6000c0c1d200710094081e0aa041246000460806003031040080c40b4401c003d03400c606200d000c02245000441c02e01529100d08a00d49851013500010018002401c10040040c0200880042040040c4802c41184400da50301034998210202c42880d00340c0701481002045200158210811110842403c0b00b80d4881c0015a1f100104a0b0740540e125203030706a0340c0210408502c1c14003c0d240710511880c08290300800080003c100c0345546405e084080e4401e0b0001400c070b4500030100e941007885540c3e190010032281080c100d4400000c1881e04490001400000c1c2404d0001105406140f20700140c5014104031000d0b103070030310114080548141d00520102c041350740300c41a0300018409a1282107448200b03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 904986115 1250 904984865 904984889
    0xd051e01060515030c130909060e150f090c031e0c0604030f0809063006030706020627030301090209011b03120e1f14090f0a030f021903020a1209 64
    0x5011048407600010700429001790184481c4c08905000d03504032000305401c50000400c00407906000058940180c0415050b44c030400305c102400b410a18025801055040500d2041d22011002c500b090181100c04d03034580704e007940c103040440803000c801d20825000c00403100c14090303042c20712206000e188030140c0358002c8083c9940104544a005200158004124501d0050541101d03441c0000c044441c41d42202d6604000000090440c00740d508510100e009220b0f9a241140080d61100c0003041c145507010000840001c0c080301c0c001c1030b9012b0490701c0c1a00d480f582c41d080b201000750020711030b80340018400c14040e1658078000441560268265603180301a4844101c010042e03c81d40403c11418400c4640e111305a5071840409a031104071000c01040038091503d580d26211000f40c400d8541e60001203240c000d207040040c080a0569060a01703a8138000f129070103a0410b0403072283d060f200440c42880324100341d800300d68202000d1048480c1264104004822103235100c950040c55181c501c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 904987365 1250 904986115 904986139
    0x60b090f1003080a05040f03050319030506061c0f1410050d0b1513060f06032415051e0406020f01060803030a0e01062303060a0b090402040c0c020d051e010605 70
    0x3d08000800c2d2400352410414980b5a5626401c0800d1030103078000c3e01c0641000c140012000c407a528525600500c03417500780103a04120001502c5171251a6000c0b200c2108020441c0e6915000d0308003654000c1d44040801ca0381e2200100c000c042042107840500c041c88480d0042800d1a05e440401a40794100342441020f94400c18040850241e203a401a44040e900d2a014000d0301c0b45d0050f5806402c900360655002440c1c03101c0501500d0780e41c000c5044110b141401351b02c2d44208040100111900140c2c109100a603ca00c00d8505206403a07070b05072b0062038400c682810110320380040048403810740c04c4070121107103010458201c410b03a0081c410b0540040010030034407001d503085107000c03100b16400000e556544086850f0500e420407116600c42ca10302e09148020b2071305003c1c1e01d6000ca02a1018000309161031300080320440c0040000348145da81d807805090051103000607984459024250340481151418160342d50961035900101a00c4001c4104800081c18061001116000740400d10541 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 904988615 1250 904987365 904987373
    0xf07020a020f0d060e030c0d020703050a1113020a0302090f01020d02070611010f0f0506100804030206062209031d0f03070905150a0b0d0c0e09060d021c060b090f1003 73
    0x4164401c55501010300c3c4401400b0603ca449450301101e040f00045a813403a83c2440a8109007485a0000554204407000c0000c6100415592400d03a4800c00c501d068a00d0400000c17149010889407a5200344042480706556401d80c2c000c004201c1d01310f45115107559a8001240d0720292040101d0041e00859403c021050240400f4411064541c0021800ca00e81102e21000c40700c6080002c248030b620b400c10b0015506003007402a142e0000c43c40c01c02600e10701500c02a503240c20142165000d60820300314251100301c901200c3d0f03684c02c2c0211080c4050a16410001c100d0211020ba004404460301d904501614140c28130042250f4041e000d080c071245420307100001058002e00300c3d0a07021984021111554a07030950340090310201d00d909840d11a620340000455200622800c10301031a00310009095403050340341540f244045581c0d200a0980e4400300d110051040200c2d02d44070b9000300e231a010041c0381d03003003907404050554203800c681e41c2d0044031001c4010195440013140b402020280042 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 904989865 1250 904988615 904988629
    0xe062d071b050d120e01020f011a09011d0c0d0b09130c0905161209020a030f031202280329041404031e02010b090103080a081b040b0c01110c07030201080f07020a02 72
    0x15101401680c206c0741a410f548c034250340074248402000c030070740300841c1c1c690b00d0031106603400f404114440070000c003850303034110001940141000391180c2d0301152024038040c06400241440101401c0000d181c1080d5a40c9450022800e00494014041d0300b00441e8545251140c00c0c420328a080500342043d030040010340f4458001d100c0911034075114024140541ca644200c00011817141c0b40c100d620303045a040040031081017007600301406004015510035039500720081c11041c41e41ca51303115543e02d1a150254000c200f6004402502c004440302c048056101c8070079003c0c1814195002c0c40061758240c0e40c0800d5003002c540c0140491161200d0104440c4881c1147d06000d0513030000050031000380c400034402c2e401c01d901c1141e14140004040720700ba03030f01615203074018420040810030131365803024461142c06680180b1030a80c3e00452200c01903582500172148650146035603590350409c0500701c507210341d102d0106901041c41c94010410b0058200c510ba8406d491135406081100d4140d0300304056 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 904991115 1250 904989865 904989887
    0x3060c09010320031f03054207030605010212040902031f03050a02010306080a0b061005090402070609020108010b0703092304020313030f0e062d071b050d12 69
    0x105581c5403d01e500000100303200c03d40d07940c140102c0503201d00d840124241c1c0850300c1c0030456649140d049003000052000207000e10208224074050281080070560180408054030b15010919840300078140292640700703c0d14000c100d01e95003800706545036401a030391240101d20f8941e02030301c100301c108914201c55010b540c22035800d05101c0c4c0f41c00c01c446480301e07485007070740c2080e2141d40101808004541e05803141d00300400011000e0400454680c030781d040c0411000788107a02400601c4600c001c100d204401b00e9240342c000a20031500c0320b400d401c14030000c081600089001c1030380704e400881d041160105451031290705555000e002070801c10380c5000e50402c02d8149513005080100071030301e5070f42c1d0f0001d1407040044079031003600036026060042004880c850f0110602208035050b4080e901c0304022624100756060b10004c4030a0005c14900b54081a40c0d03050700c001c0d20105143c010010420f0700040c0b40240c07030400070381c89503d44c2e04000c040b034080740f0b000703001148290024660b1409801e01e402 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 904992365 1250 904991115 904991117
    0x4050c060f0f0c071701020d0b0406061e0908010903200102030606040303140702180f060105090609040209190e091c0c030c0c0b1b12090109050d050304092a0c0203060c0901 76
    0x81c84d699140481684001d118080b40e040307940103d03203100e100f1a540b107140c0385164211001c1c446240f8145015004640f0b505c809510380c603500ca0410482401880d04500800c60b10000300300601c0d0505005228011344e0325000b0302030324041011042c4070014000d0741e005100c000d18040c0b03040d00c1c6580680d6002110b01c2d4010791041d040c044440541d9609143c0225444102d0b1245403600c0d20b030f0f404c55a00b14000b4106814032806001d42541074072101e09507840503205807070043c3c1c0e520000c4001901c5d015406c03104c0c11f800c11022004100f0f440346820032801403158408840864015009400c0044860300c40c82e40007614020041020034401c1c89800d001c00c0c000c10140d0080381d00c3d42c0e1440b84039030040c9206031600ca012403016903004010009030b40c0d4101c81280e180d04040e03c0c200004c00c0420a441101e21032041090313040c060100c00c0c400c880040c10328580030407101901e03003c6603108190100b051103070080d01c6403520591a009810400036160300070081c10340c56680e802c005100d034008031030f028 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 904993615 1250 904992365 904992373
    0x110409020a0e0a1b05090f0d0c1202040905070801020c15090a030807030e0a0c0f0605030c040306150e1e0f091f020409150e10080c04051b07030804050c060f0f0c 71
    0x8050742120900e40c4e0300e103040a98890303580d07000c0710091140901050300b816000e809907800300004140840914019a823070030000b40101c0c802800014090131001102034080d01a940d4002581601540200885120b20060700d0520f415017440d00b84c0038904494010b4580c0100c0c0041c00042c2c401c186490748005141000908030300c02040b520324010400324200c49803040010140040c0c040070b41c20400a01052402f14903515100c912031005e80030741d2000910017500c13a6015010400383c1c20903036015204900454100d0310700841e02c900141c14a034051644c1d90074000119003004070040400384541900c5000303011307044071900c030002d603003640c110382e80c6031a5400d020110740d1720464040c48400a100e0071071401c0660400242c01c10410002e0100c0c800e5102c5030b00100300000c0b010928508218007110b0004041d9641e51800c0c003071681030354810240620004d80c4404050f08008a40d00bc1c90240c412100010184000e22030035101d000c2d0380c0328040606011101510314040c0040614058000940f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 904994865 1250 904993615 904993631
    0x406050421080109050907121407120605101508060d1b0f0f0603020328060e130b0109050601021e0a050105091005090a030e010c0309030c12110409020a0e0a 69
    0x100781c041211221841c0007865041c0108402c5240740140b03504440c0000103422a145028a05030f840d04062500034039040c41407074810b05c0003030705101c068002c000c448103d52079a074091410700300820341214201000c0c00c8007030010901480050f65000d550900e500c0d540c0980d15850308000b00d42c02c94100031207003206600d00c0d0090180500c0b82040040c840d82620007104c905001400340580b080b070b041402010703c14000c00010000c09001c520030460403d0700c400a8200702c0305c0301d80140c0526041f81c0314080041c418060b10381c030440f104444803801990600b209988401080c0d0949205507031403030059000a01c81242c144e220b0a80481e070f03004d03000448a0b84038003507a409081d035030203d445401d40c1d007020311940019900703401043c2e40102800050140207a603580c02a054901c44602941000f10198a0508240c01110002d0185402c804601c0c50690b40ba0401980c032000300f0740865000d1240404922141454001d05c0f030650350041080614906001c50f69011300c20091070814655111000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 904996115 1250 904994865 904994903
    0x12021f1e21051b19260408030703060f181514060a0c0215030612120d1e09050304050102101a010e0102190b27060c0a2303060f1804060504 61
    0x901ca42184007280c2c4c0c034015110140504880181c4560b00c07003441c8000c00d0090340f0507401403055880b41e4400d04480d140d89a07008200c0040156070018142c41540400c0480c030482e00000d04a924582d10206008010b881c034025000307a50144142c41c205564920b42054034075158001d480060380525201c0070400c102d40000f5040c0f048a00d00c05030800b000414400e8500703100004181c0741c1d00d807000801e038450b00c4100001c0203204038512040e4013651003035050100095050341203000c1c00b41680c14040c10b2998140307641c403507101d8400c00d07025110b80040d5152412a0380580c185040b0102c99030009412844015a60103441c0700070281140601c00584101600b132410000400303003e07807908a4145462032501c0800c07655500d07090941c407506201c166030f030880003130034692210300407420a48400710b8500c265083e4921a40101600d40050410410501180003452146204443c81708040c42a041400f08c000c4d10a90001060f0840d4800217020031550b400c0190440e00c110401d42d030100704000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 904997365 1250 904996115 904996117
    0xc031201090608010b0111030913180302060106030b0a0f050d1707050c041109060a140c07091401060f02121c060312180f12021f1e21051b 61
    0x40022070755590741d01032160060920407000008420700300400190074a0b80d40c0d80d41c0303000b90040e103807040d802403650b110031108603003150b81e40e051400c9071031001113560302d0040d40b1014240a59400030345440e070000c03028900006024120380c00c0c010300410080c1020140000220101c40582e24801400707504050440c64400070300300303d40140003402c4881081001c01054588840c40c0c06528101031194403502e980d62011603142c400c0c03e0404560b40c203550001e914550040b1452140c8500aa070400908406d02d9040007001608010200b45280e80b103a90030740364400b0080310000103074461200c0700070340c0c241d400c001e00c02e240c284a0440490006c03100e01c0070550380181c2044940d000301a0300b45c09a690014181c503881450806001d42c41420105203031807500051040186141480c40c590b0b05545a00181040c000b01c20142009450b92000c005400c81c0d1051480c8614400e8440110f100076100d107840303208507038011050b1800c2081c400c0c0060f002e042d0291030300050300c000f50320840710144610 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 904998615 1250 904997365 904997369
    0x1202070b0d15050909032205011209030306051f0912050a0305032a120f0f062412010f06050c0606150d05010315060806010e0f0903070b0103050a0b0c0c0709020c031201 74
    0x1800656441c101141e01f079140b02949007004200400f000b005100582e006052002113882c602c500160802e05810110007034086940300d02d820245082c18000c80b03d503940c405010603125510b80d6500655203881e000384094001030080c0054004208900c0000c0c4a0002181c102e440d1a4015444050400a1880401c040d9141026800c0300048040c03074a00c0c90700001d54031460514645d101807030182cec50f041403e50001c0aa600c9a0030407900718031041c00e40d0201d9804000e413a001c840e04c55000c101c60740409003083c040c2044440310700c0800103856200b40c040b250b40068880161080c0e881e031000f8050300400d000103401007040b00f40144174250b070061090318021409100a180c3c07014411032072000700e6495400c01401c64205c0001842111900b80c00c2d16000501005488002e80d500a05c0c3c17410b40c010325000810084902c40000b090040c0001c040d01a00d0080c0031340031440d1582801510355229a0000c0ca5031904207000420010300660301034800100600e007560f04c3d1000000c45503120020907 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 904999865 1250 904998615 904998631
    0xd06240507021e12191709030a0222150501020c22051003020d05100501060504030507120f0f0305030a0b010c0b041113020a110c0d05060c0306040f0609091202070b0d150509 76
    0x517680c242400590341c1222080d110a11600e0326120092000c81e845440b9100c0c003900419200304451400340c030a9003000801c40c03c030b50f001c224000408422000d940d000c0c1c41101d00611031818224440d02d07020411004528416100c1400b19144580c95006004001c00c11419884039017000805601c0301d6035052030b407511032030142500e0310300310148100f1980180c00c03081c1040414802840080d000081503400d6541080481181020f0f030303d05080e000090180c01401d0244a20f241001c25802c840654060980c41c4014000c198a420044541e03041c0703e800071340403011400100d400318113566421040750b070740071304009214a01d1482c10382c2682c2c494800000002c170b442101a0703c840c810b1000d00d808042c21201c150b558400c60b00c07855034480300030b4000701c0e08003030020128055542d2688140c00c100d1031078106201d15651502d03100002c00184c0401d0700c5d074808152038804850b2021420100341c071000c0710f1080c1801428200e0400030401c00000b40e030096070140003c1081c0d5250382c800ca2090f921 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 905001115 1250 904999865 904999903
    0x603010f050910061403030a1107081507020c01080f0402040c0c1e02010908151603150b07060506040c05030112320d180501030c03020d06240507021e12 67
    0x50f051120704851850b4443e4207419a00b04006810f0340d400300031130b41c0c41c80880c602100703800c0c103007400780e4200912a0f01c1304640b8419018450808030300714041a101c1c3e421502aa00f03407000c8080156100b200460b0744c024401400d900207401403401d54004490491245864a60554190b85504501c400300c0e00c41c00d41100c00d020280c0843d0703881411040509100c0000d8448002c4072040701c2d20310500580060191050300450f134080f00e11951016818210524542c066690b03100076040c92070340711711000e42e901c5007401d000071250306050242a007065665924a0700d940e10344009110302030905d50007281e40107044003580441207038517124000078041e061980800e007255070240f240b4100800c031542c82841a0003140c07150741c0203076000311130444800b03080c049401286400101c009219580c20702141c1307403a240000c0b42040700f941c20000e6010220304000f9010180c04002d8400d4091294001e5010180c0b0680e43d980202d81c0700d99809518001c1c00c0185290a0030034654200b202d0140c202041081d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 905002365 1250 905001115 905001133
    0x60303110c030a171204140c12030306100507050a06052e0519030c0e07020f211606050a0903030b06040308030a27110109050d082715040f0803041d0603010f0509 71
    0x1020700104891001c00c8071058800008014070a2b102d00000b000140316103038007000e032848103006000300d4040303e5200080d620390990514182c0c00401c4181d8070021210b5030180000b07a41801400402080c0405c00d48004401e031400d000c00c02c91405038120f1103911501f4520001c000f4224a044074007400c0a02d0680b0b11600d80038a00a180182074010b50381380e80d0010303c0c0c1030707424004408202c8101c108000900e43d02d41700d4000c0c890301e5464041c0000e000910745402c014030b245184d880032519910a91b0103001d05140d010070840c8074050390001502c132078800c201140c2828202d40c05107442100350506020540c0f145081c0d60f4150320401d1b42035036602920004182250b03031180f480000f0304000c6958450480b95910740d5180c60144c07056402c080710201d072500c0c000030030400e17040c100030900078003484400f80c24000100f41c0343c015103d4205030180050002c0798140c400b00550701a80d041d81385001852412280007100968040c1669070036541e9410b41d030b200300f9040d000d003511403039403c801003644607 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 905003615 1250 905002365 905002403
    0x60507050c0a1d071e080f010510120203090a050f0d030e010203070819090c0602070e010f210c1508061002210705150a060303110c030a171204 63
    0x300201d540c6901c58211a00e051240c041d441c01c10101c0080200c1c0754510b540d60344030090b40d140000c0c2100c00880101c1e00c2018000c540c1c069040b602c16004007640703a1050b6604c0303050181c4626407060103804211080c1000c00103602c00d60207158040c2500080f00c07168011511414281010030300e0046140d00050742c00405580c26015840303014075640000c51651602c0d0318011b11500c8003508002d031302072036041d00c6403420020b6000304c0d413125006101c45d8000c9540d200d01035903c902c24482c1410b40750003500001480c800410b81c000c11982c2960168032085205d8807951542031080745c2c1120100030700e000108140d8820301168000401303503254a00581400420008084072030b0404204540c4004012000040c011202d0207804060703042241d1a2191792821341c1c201080240d800303980d40034680401442e1201500300d00b044034000e4541d820241d501d000c00d143c8441d4801d0722103070542d10240107080003405512a49101850048809080043c00040300c54441c1c0161b4068034500c90b030803c003903064 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 905004865 1250 905003615 905003623
    0x5030301151707081e0a02194401080a0309210312020706020705060402090f010f330306060e0402040509011a070b0f090d080c27040606050705 63
    0x4070001e0901102d9584001c2d1070464504009000c0c00402085034007140c140305800d19201c1d29490b448489510713070702d840240c460082d000b0741d0081481c1d40030866140211801015501a540c5401c41905800072581160390340700c2603490030450480129044c212024007240309154080c10021000d0000300203c0d050050001e102504a40f407215101d841540421504c10f01155005034503080038144660340701c12030002405080400f030300c4a03000041030010410003040f1240b00d2032080b112203180b5141c09427811100b00e401d00801c01d484c0d480b44814082100c2c60035000c0814450a0b9a0407210840a01d0a01d10a090303000d4500100c0d80300d10080c4a5550400704101d11200140d40850a01c0c0c03070080021849141032280c90215602c03145120b00742c00a14046070500764010300b11074240c0c200b80d0040401c08030200c601208078060900c0d8464498855420750340242c22850f41e180c14600e0a08600c012401c01c6508a4404c98102c4c040044a464030300036500240b1040c3c45007030300e8140504055081c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 905006115 1250 905004865 905004899
    0x14070509060d0b1f0306062d0807050d060905100f0303021009021306031b09110d0209030c04050f0f07140a0810031203020c0c0603250e1905010f02120301060c03020705060705030301 80
    0x243c3e641043d103920740c100140d494408050b0036140c044210342b15400706039002c2c40390600d400303143d60900b24049182c42d02600000c2c0103207460584403184039075920841903d05501e000060051300050149540b01c41503411003594180028940301d0f042d9010207041e4126185907000700c13113004180002d86c50402c0b1100f001001000c098500307010a400e24070801c2d03080c1c40f442e419600362070780c081000c04080d1810014502c0348840500208820705000c004d500003400c040350b1090103d202c4000084046114104915108003000d0000b418030305110703400e495882000b0001a90010400c030000b011600c044e04070141485250ac005940e0003407017825500303021809400d14003450b81003048c00200e03954808083d41c24081c12440c4401020411000c48140055603422507010a102075598409128900d440040b2a4240c0382d2140a606083e011380c2c030f40342c0e200b01641841500b4001040b2940c0290b49040e0158403e10589007119200c1e80000c034a50886481034403290300200c0103101090b5218a0159 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 905007365 1250 905006115 905006147
    0xe1503010c1805060a14030c04032a120501180602030907060809060103060c0210050406150e0f0f060d0f050f120f070611091314070509060d0b1f030606 67
    0xa10300400d040a030502c44003442558014034000450405241c81b5503000058400350800b59a81c81c00c00020880841c0c1040c00142e074510103220800f080d9010881810410b0500013541c144081c1c5880503122100c0660f031401d0b105035407100d820112809082c00d07001c1205204500c0141c417410b000365000c2c0381c48050303002002440000005d10004000010303100381100d034046008641e0680c0070700100d017406600100080c2443c101001d10080110790341040c1440c1d00f108000c800340382d0ba01c654030507020b83c0907504114104030100100707149455001c0f00540c00000030305581408500e595070808050f040c2c060039105070b04240c10040e1480810700502d1320900c01118002d0400c2800500a140b0f4407420030300603e034507914410141401120019102c00765402002e10b50000c02c95400c1c60040c0c0300005c62040c2c6042c4080004080c180142e060310ba4007840501914208500b001d040c50041c0140300c202584001c4178141000181103140c282100c2d0f28a540d80843e100b842c100000c0e100e18100c4030001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 905008615 1250 905007365 905007377
    0x5010315062105010b0909071a0301060c020d111c060c0c150c09270e060702030d050402130203040c030c0e0c0d0b21070501020c10050418060e1503010c 67
    0x219200340318840105001040180c04042c8240c5003090040030301120040e000100710f01040014980400d40004130307041400750105060745e101928042d48024002d030b402107118450000098106241540810b521900004034241190000180c007071080e901040310b40c0d130b8079016207000c110700340c0038048a1032068140221406c2450755148402580309900385238403a03a4a200f111258400e8036200018211074000030710821400d20390240044a10300038180343e50034124505038003100080d07ca44582c20070b41c090360418040d42704800140c4400352003039901c078040d940341c0340005443d84001c5019611511711042c00518500c0e0220f130350702440d4001032024080c4c10810100e104280c003126030382e081d4608002224032040d000524600521071101e000e2000071010500c25200c00903c90341030319402d800300c0b10441c8202d400c011407107442216002c0020800e220401c0101d0020300b4004100d0140d010100c5c8464230740088a00303e85040351144149020b1003810301c030904080c42084102e04c9149846 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 905009865 1250 905008615 905008619
    0x10050a031b09030f0c0806091f060f0b0708071a221203110d02180901060201180602282712030e0d060c080118230a091a070224011a0705030a030501031506 68
    0x2d200904be4410351a01c84000103c02c401c00c9141c000700ca03610303a840b0080742782d2061800750126580c88212840380343c403042c1250410401c00d0040011300310941c81b00c481d0800b49a5400f0460103820f0700781d0348000450090100c44400c540c14009000c3c1d09103800744111050300c03900c04000090074103902540640e45001400c801610b003501c0c0ea13004c1079401410260b40e91a60201450394803a002e03803642030072440c1842d41820168806c0c425030012020717000a032505c0b070444100b4407941c01c0901c5140c0024a4111a802c0040e02075100d0f90364003040140201428952600c0c0d4205488100d882200000ca8100061240c200030292080010180300c600b0060407994180300100440d50700403c005a070755040008104140c240c001d888040e52000801030304451403510103c66034404d0750b00d1800340c000c40880c4240c003059084840408541302d12690b07141d0340307844808401c003d158080d072000b0113820001da8011400810007040491f00640e00011690b1560070700602c0621820b080d0007100b0b0030400d003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 905011115 1250 905009865 905009879
    0x6010b1204080708070807140709020c06061c0803070804060f050702031215131a0315010909031b080a030b030c060a0513030210050a031b09030f0c0806091f06 70
    0x880c0d809035001c0c403495a500110f0819503454000d17000010200c500000314401080300780c02c104452003221504842c00240c80d0388441003640184440c40b0280c0d401000002c88600d0442140514240c9079229070051641c29210340e403c1e0f5000b207038680042031580092008205692207454a100d40014042115041080380291a403080000300501e5802010104a4440380d22a9504094000504008026840070880c2c006803100b08401549450181c4840e5040d040c0030510034484049034043c221107078240031050005145503417064007005040b0316065085484404281e151034054465103031180748401d00142a5010001b9240c00f076007008000c484146c07920801d549003541542042900c3e0026032014489030034481e400070358000d1040503030000307558000c0c00420130220140c1d4140184400d1000c002042000000c86100160510a003040031031000002d42802e64419002d4158a41e40c0c7c8446510b006000ea0755984281c0102c07140c418808000d1550036078076a01c0e800140060f83c1780c128 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 905012365 1250 905011115 905011147
    0x81003080f0a0908011427190212030304020f060f07050d120e0a02010206220501090c0e0c040302030706030e3d060e010512071a09041406090a02090a03210206010b 72
    0x440e016440c102490345580701f4600c00c9910100c2c0a00084903050f416401041c003c010f10048103a00aa5001e10708100d0150b0100c01c62b48140e8015241c80103512113002071060f076900102442000c030314284415000902d052011032200e140503603401100b078450117440c20840e00c4a101d80305071b6a015a0740600180d8021940e07580c0a07050301100404002a0101c0966207940014024040e5281141d4102040401080c0d04180d03050318079078440681e078503004540c451040e80000396159104000400c48540b00c0d4000b901c170808910103554180e0314445500c214612003100b05101481098880e40c069001002225450911007500b40705807403802540d80481e40b418000c00c0e010755003456210301403201c10042007004200e410080e81c4d00c040c040742e4881007a0442000710303103e28204202c0d41c00e09118a241c0d140a400020721107c101e803100303a0000c00a6024400b1290000e001c001d0000c04074011000d40303030103140500d0780b0b405c50030041c4000a0400e00140c01c810300c21001401140c0003a02250 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 905013615 1250 905012365 905012371
    0x5121224060a02161d07110c060d1d0705120123071808030a08100303021c03110705010e0c1c080304020118060509100f0c03081003080f0a09080114 65
    0x560010350b15418800120b0508610f04105191800400c00001d40041640030003c0000007800f5082d400e501c90880440b000e0601d0007001400340d0180c0210409480d045000740700750107080100040300c3c140e8144091030461440d80b8614140c0258008000509001d1310901c255003000d0020010380401e901d5001c2c503070036548111188140c4c410002080070340191b8080d03000c02d1440c203001c003415580c0c01e90343e0307543ea110314017100004a05c40003082907180b500007800c090300d905401912260003a007034426400d042c0310500100b055224088406c4ca041060010241c6034060000424484440e180340f5142c521611000c83c064504103c008404000462144400c594441400c80c4e80e030f101c9000407600020340383c48032a0040840d45000070b00d140c01000415110700192100c00c0c00640e207520070b41e8844074118010000c00c0c2d0313288004c8002403003840709580c00301807004a800025100e480d0710030b0300c0d009000e800740420320014400440c182c02c0b040040017000c909009024a00366103040e200110806 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 905014865 1250 905013615 905013619
    0x90c0313080d0e0102070f110612041b03081803210910120213031101080c04090b130608071e15050703030207050124090b09010611070305121224 64
    0x810b80640481030790b00403e080f0394440f0000d40d04c0c0c030520b06103066103800d100c0d0100e0700019220309806c154200f00c025100040e00d282a0b11542e9907c580301c12450555682c058118840450004400250018041d01078218030411444000146105043c074011071401c100310000c0715000800900c04242d01100c4401c8000d4440ca50000c7c1d000400f075482804520240101d1400401d0348503c050baa01c00b151f007102e0240c2c90641d0f01c0e41d41c1c2ea005552101c4240c56410000000b00300c10b019441007030300080301805025041d204068a04180c0a0442e007007a04030400d40e07001813904014030700b60000a90421a005100568814a00503031a4482701002a00d80c7c10b200d40410f10805150003941a039841c01e4000c0024406130808482c60892071124a040c072080c0e400800c800b280b450258496000340e03200142500895908118040d5004c050200d01505580324207a00880007440920032001c15807a980313800740c2ca401005600550340c6a0040100124490524040c240030300c1e00c582402c1c0240c0c00b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 905016115 1250 905014865 905014867
    0x506190e032802071706061807080105150904050c0a030c18060c0804050d03020c1002070806041103011e15050103050f060f120d1106060a0617090102160302010209090c031308 77
    0x1030b0500503402d10b080c1da444001c0195030740003280142c80c000704a03280310398006c480d404802e0ba180b00102803a10030540707030840060b8680b4014040e50410384044043c200c0103180c81e40c20b0001c0b4800040545808a81c24a194000071036403404032074142c05020360800c140e080440d061035280d81e8800b0412494880c0204010100e42148103100c1101d04840142070050030342008de8075213043c061350b0741410b80700003805041464000c0310300303600c00b007100b000780d60005014040585035a01c400e0001105c0700040c0e5415541c0320307035201c186501d12013406035401d034510300070850f4441ca0103008108822580300304d0625040c2420000410202c40c4120781c04a421251410010603200114056800600c601072003882140000c0701c0243c1c00c442e400361050020b0317080f112030f40d590380e09005030200503201d00c0000c03850b1031401c110712440402c0d80390785c4110200001800d1083c1e40b058100a045000401d40150b5130004160095081921382282d2220030032208030b00c0e505285d03400e42075081c48a4400b0b070456030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 905017365 1250 905016115 905016187
    0xa1a03060406210b060111070e0402060904050108070e0c12060d05210d0509070f03170d110c0d030b03121c020a030b03160b070f030c0506190e03 64
    0xa51540031001030140c1129091103c41e01211610154040c80029100200503600181c1150311039180002c0303400c0004003070304d02c840c903103040d09444840282040741c2c8804144a9100503807518490340d4002e007007a100800603e45400424681d1721405400c0581c10a02000074443d04405180365540104058803801c8002140d810218204941c04004200351091682189820300c3c440c8054100d03c5004034042140d5141c41c060a42e4071051840341d4125070111090420204d001104c85549084a401c2c00700d213440d038a4081305044413042e140900d2020340205241c920248104941d506681c2c05041c1001710140301e40005c3c1c0d6540709440c00c0c02e6031102c00101070242514418402e00c0941120500707540314034004002a018040340e21f02c00d4000d01c00d1092411480b8242e4401400702c0740c9040000345002c09585440707204070080f000580074000030180802c0014410001a0f10545121780086a00040b44209409461039200e102160394028040750000c407070307200500009503810000401c0a00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 905018615 1250 905017365 905017369
    0x703030e030c09091e0f0a080715180b061002151024140a211107060504020f0a051f03060f0611010507050414090c0904021b0c0a1a0306 60
    0x10890444580e00312240034180701402c0d0740042c031117104500b10780d1a44040c025518206035545d240e54550104d65110000000209001c50000c10055000c0d40d0241c4211030682c041205440381c031060b1001281c448811a0207000c0260b5155800c03e41c00c5809030480000c0c803000a65840800780c400003520b00810104810505e0031038460020700140c6026805a45101e188451a81903100d000c1c02250014410000c1c1c94402c204445400c101c5032030301c080c210603030844140c0b117a5001c1920513070355a031070410503410024000600140c40c4500c0c80443c552801c1c0c03040c000c08284500c01039029401250090141d5907402d1b00d135083c80070300c0c04c1c4210b03995035025200301c01804290303000d40b4441c05240408294964040203404111440744000c1c00769848114040f50903110340e11402c4402115086001004e00d0001d820981004000e07050604128410001904a902844c84100810b4a0b0051041d0600050221b407940c500125800684c8516154641c3d03541c14407029803403900d41c0004009003140d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 905019865 1250 905018615 905018623
    0x6041203021b070807150813030e060309060717060a0302130605190303090b03011a0d090c060507051c020a08030703060b0403080a080f01050112020715140f07020105090703030e03 79
    0xe5007164002c4200c1e1125140c1243c1c4440781c60040740c40034001c0c1d003400b00d1100b58800005900c2d210f555540d0b003440d80c906890700100d1020003022820881b003181020250f030744450146000e16074404c00b41045062032040034155210b0440205080c142880c100b1411743e484640322011607406030703040d0300d4038003606074141c0050800c4d410407544103100c0325101408405070f08403d41031382c2c880c1c0c84a4408545070015241c4078003091081098042620000c90358804000020307080217040258081624402d56540000350091f58108100007040071402c6001c1c89400c02030012100e0342c903d0340b003e1444000c28025112441680c02600c45c100000120301c8040c42548200700404142e00714584554aa103080003165000d80b50400c009400840030424458010803000d0403184140c603115041500d880307481029401c060000d840546191140180222160080709080d802ca40c1e000021460206a4046004070242039402107a25007020050080400901c0c101581e8043c06c0000030740650000091030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 905021115 1250 905019865 905019877
    0xa03020601180905060406061701051302152802070b251a010602060a0507031b140f030c07140a032a05010c090305071202031213030f05060a0c0e030604120302 70
    0x8144500c504220a00c88039070300040580f031601250b039600300c407027103541400ea410540d00491031000348209500185058095080c144816146007030411440f000d51103a01c0581e43d01e50302c01680c0560040c6502941489a50050403a09012604094483c0d510b0100c4000003510040c000e0a00c00b010424060400d90310f0504603044054443c1c03d40c0c48a200944030324094608510a600b0480440c4402d0301a005100d000c103402c3c640c08000100c290b8045036030102c46074028a4a1000b040000604480751008610410044110503a508000e01d8514900104020700e0003030f0790464991100041e6000e0000b10f20310000102c030502191a44030308070381c8601860f4000704158030b0310b80502480c0380c12108850403a4007503000e55100560f98070045001d8425200f000b50701d2b8000c1d03d107e1200c28560000740143c5180300010000d80c1d40c0343d603640c001452070044d0a658543c807003000c004c0744000300d000d0110f047d201450701d0322200000710007007035581002034801403501c50000c83c2c20350650f20036030690b08 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 905022365 1250 905021115 905021123
    0x7080306040b030c0a06170a0b1f0306080a14070b09061c0b090a0f050a331706190c090510021f09110f0f09100b0a0504090e0a030206011809 62
    0x240c0c05d542c500014007451030902007000640307000740001e0f03400790700ca200d42e03111084041c048900c0c40b4441210705444078110085030040c145d46401c08624040204000143c0320310650f40c1c060070149161015180510692102946010030014121340d900c03244162036891411841d881c1d00042c0641e41640035110000503290041c45207010880010007603048200e0844c9078031810002621031380da23340c050750003280c5140e00214083e01d038036219001d80f144011203038000c00c114014070390310ba40c60310258600600044800b07034820000c2c845241c803002085e160b1040e5100c0e003041000c22050000e0200c0c0d03554860644104400414007001034002d00100a4001a01745440081e10391040403100400b421001500e080350004118212401d00380c4016003142001801c00020102080800034844c0b030040059620b200c0d121400901c1459000140c603c1e41d0b800c2d15010b850710b060542c00000c40f502d0f8500301e111a031140d40d035003000c40c5d001f003001819201c880e245005e5686400001d1b401410010000074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 905023615 1250 905022365 905022379
    0x100c0606270b090f0601050c0c060a11060f0403020607080a2a0201060f030b0c030709080a110111032a0a170a02010b06040e0a05040f021e01090b07080306040b030c 72
    0x4541c81c900e9a40d80d585038998500100000d10300d00091024003030044072000c0700c20100ba0040350b529030085003e441441002421078003190400d2002c140150030140904010618200c11069016003d010f82a80700d07945066000903450a030310700030344d9903c3c05003105c401d0111910209440c0c10454102c9005811118140ca00c1c807400340c44d1038010f2000041c6031320011f520303002c40420340c1c0c0503a211900c00c49400c05803c9000743c582101880781680042d12200900040d00300011301010300b84040d0346901c3c094114035051081410015005903400840c2140c0e90300308105c0703142e82024070b88070f6081d03280e01c0c1110b00c4240c41e14240124071b000040f24014040c6842c44c0d40070035040102c180240381e0003d6903802402009040400d02460f07028900600404001070800540f0071240c583c04aa405401481040c13500e121540100301281450243c40700c2a05495840d0650f0f5600002000d009003205c5940901d0303d0f0f21601d58a06500000d4506445941c641c0801159540c0411588030a41e40c014141c1d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 905024865 1250 905023615 905023649
    0xc0c0c04020315030f0c040507021603110609131a04060b1603140d0213060206010b0a181a030405060708100303080c0909010f08060604020a05070308100b0f0a08090c100c0606 77
    0x203555503c181c401b03018400e0781014009800a031004c9840c0d206502040f081c0c000040c20766464040b0900c1050300541c020f40b080c0507204c0303556110103801300703005200000060b2001022211414061054041c1c42c010ba0038270b2010000c805c10202160170715209203c000f0002d0f9003c2c51304440b08010080340340540b07003012580030007201c020341c010040d0144070340b50a0f00e85641c4502c00c2e40c40d06424480c80d949000180900441c0a001c3d451120344244010351100d04613841c0c004d0011003900b03207803083c3c1000b04040204800c01c4800c11001d904000d06080450281c03a004130b40d00090803003400b0080411256901251121a0b0401a2403003050003c001100c2903848162101401c00c50b48a80b00070303846070350301060050030248201c0c0c00b00c840c155140e51034601c243c0c6050302d40c0180942001d1b45034524040014070300109201418030895264100c0d0358a07403860200038000040900507101a400c0308a900340c0603690252080d510741030b141000c010350708450a20300000c0a044e440010810591400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 905026115 1250 905024865 905024893
    0x138040902060301260106080d12201213200102010b031b1009030804150e1005090a140d06050408130909150c09050103180c030b010e0c0c0c0402031503 67
    0x40c0039150b0011780001004c4088251040d803e0b1421445104106d070400b4600b243c002d40708003080c00342c02030b03500400300d880c59003a81040c4c0002000300c071541d00d51001094442c0024000300d55150031041400d40d64030740030405e4442811a011903249070440480e201c4aa0009034000e4008120001c0014207a60120b40fa880c0401c5061441803842d80c450044005541805802250361106803a007002807182814200307526440300b204451024028001c0d0003d01000c103507203034501c001c17203420b030f0b075490544644816051042c807501c2c1d9001800411003800141caa00d4a070341702c817555540d80020011986031542d04015540e4412405604c10040e4043d4020625030740c160009560740e44140c52480e40c40000c1c00c3c203841100c00d60150040001c100341001c100e60b40c40b9401c054007468210581003204d2200d65105030013086603600480d40340c1003450041105100700d80540d0341c4a16031301c4d40342e4689a840441d56883c0c107155400c852159a0110208000440448010080d01030103006c443c540090710f80307 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 905027365 1250 905026115 905026139
    0x231b0105091c1103071d070305040c030506090f070603090302120d0207020a03063216020705060418050a0e10150306020d09051209220e0114090138040902060301 71
    0x9072030082c442d078000003030800202c02c10781154100200e424011915650707c201c1c05440c001d4003e9442e0b814460011010410904c5440e000304045001804260a42c410080c2442000d1b03101e00280341c030700f41c1c05101281c1c001c00c840760321051018900380c0d50040351140c0d000030300500d000a50030165820000c400c0040c181d00c03541c012141003000d034030120b162a0000c03101070030303800c42c69640081001c0420340da030040301c000c2003421100380183c41c442138881010070540e41055200d040c0d503918104400c840b0352024810150024110b4400b402070048466a0b160794000c0b245141c5071040d0f40b01d1842c41aa9050900c210245502c4003065581c4c058030031103140079021805080c0e0b02c40c0292030301c0c00c66483c191022185182009400908120744132140e0380103c64400031003c180944500341f42c904007100307105da0f480c000c101c0da0321105c02d0300300001c0075030854901c0300c0c036100c06070080444042c8002980d081c04c07900b001132000e9096400101c3c0301080103070540e41c4000f9008400400045604000c0359 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 905028615 1250 905027365 905027393
    0xe07061107090506150a0e10120b090106140d091a011419090b0303190801030308090105070905060a0c020405090106290f070f0f231b0105091c 63
    0x700c9045a0302c0d249401d00310741e41510815403000340e0840c0c201d58558070703202401010980d8200f0180e4007030407601094111420010000012344030f05143e10160802d03100da81003c0000360340550389503040c120040d001e00700b20911407907034030000b00b440178048080c1d40082901543c08400028052805081810380d40801c1c0a28140212020030303c1c00030b42031162100311a2503124020206451a140210006100b40103403aa0140001c020614606d812000746030840489036417480125032550900420b40500038040071a82d90404060220f800c7d841901c030401e54404803412a603925221a040d1059101c00b10000d40040c00c100410500c1c28042d0700040071a01c004903901051404101074845500300d44507101442c000c284003c0c000d0000c00b101608a45224418003100030004d5203070840d10f8003030071100300c1d104905c1d6000000c10201c04111070326240d0106000341903001620401c8801d00b0b1518941c0c90412102090119042e51080188210195020b03000c00d210000e0b800d001c100c8460407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 905029865 1250 905028615 905028647
    0x40308030106030b01260a0f14180d080601032a030c020601090c0c1b03020909010c12060305300c100b0303090d031b020603070e03060619030201050d0e0706 69
    0x48102c98035402041410400d07a804003080e5046c007032041034501002000342192143d1075441c64100000d500c1803040c00070034217a450101600b8506154100809040c00c200f6109541050089103469500705035926042202400d0211310507401c2c110300010840000482940d441e00c2500d0a010f0540640c49013680010607400d03502d07203a884400100503229042c4511300020002c0c0c89803804030303100c101d050b502407070301c640c60f410f44036987d03000107000340341c207a80750313485d0783d640301d8940c5034040c1c005442808031110f1f0b6809202132440d54850a4548084240141441640244c5603d60300200410005001414004580c90321107060406070760740908890032603003e180125032031040c600001a9811140018004a40d035036031076134100c4014450f1880c0c4d143c600c01d000000030059a448011b54850011652400e400350b04500800d0719086010380020f0040c48100d070700031807040d004140c103001d60f0780a0a04c0c50741c620300d0446880041449003080d413818058a90041021a4461032a114854075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 905031115 1250 905029865 905029871
    0x904090b070e281815030803100e1005060c0a0510090c170607051b0706050904150803030606130e010605030402030f0c010e100c06050c13090203010302091f0b04030803010603 77
    0x11070010f81119403040c4100746900a0f820041140322007440d4002c010b07040c1c40c42c000c01c02c03400300304074400c42c40c1c080d410861303401c0400f1040003180b41c1315850400040c03450181681240c10320301c10410030001c0c1d41c0901401540005030380302d40c0280420140900715408800c41d46404c0305400d82800420021600300c80318519007000040e00c1c460706000240040204002d0700440c2c032070794829a00b5507c5104100340c903142d6400c0c20300142c4070511a6000600c600d4444642d61382d0541d08020480c0e800c00c0d41c120681560b05c1c014801d0b00d40000c2642da0002040e03c5c2d0f5952004409040603090344a0b5010000300d1703020000110345143e2110207540110310a40c21100c031200c08003440c5031a4548802c10900040c40e141c200c95440c6043d134503035500c002c0039050184408030583c58043c1910070840c0c08421031440090704914060301d000504000b40a80c0004500310750441e400a4140308010340381c180c02c03019514445042c1b200845c02c02e0014440c0c0c0441590b69660791400e204203400910030300012920b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 905032365 1250 905031115 905031139
    0x904140c03060c12071707050310320414090706140322240c0912170304050708070e060f100507230a05010e01180209010b0904090b070e 60
    0x40008495004098283c080d60409401101680d0700c554020701400401200c030901d0807140d40101d00050180c80e01d41c0d6525038030f190109400080c0200b41c1d0024560035005003d01c45a100460a4400780c180d1020b000b5031030700740c1c000002e40601500300030040001500820f100300750f4000924030084070340d00d03118400720701c0782540d40ba1078602044034207002e00011400710300851848148000240b134810701c2515900c4480c840134450607079035040c418040395a5000184842d5812a036031030014801e2110003000c1550030b940301c000586400040d240140408004101044418050b42e0003812aa03c1191000c0e0307611400300034a41010b6802a004040c1c100c2040303098108240d41c0520309a254a03250710700801740d914544040c80c032140c1002d0318000c40c017030107216a0b000e01072099254010000410341c00707803549086003120708184000c01450301c180001801a02d4610301d560449081c041025152000c40012038085c0c85403200081001d1911000c010b6002e030031800d566102c400640d41c01001c07035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 905033615 1250 905032365 905032369
    0xc1a1e130803093f011803110f1f0b040b040e070906090b010507150b1507060f0b01020a1b080a0803011517150d081605100c1d0d020904140c 62
    0x5210805001241401303262014201c2e04410509070700002a600014024802c0424082c05515182c030440010b2922521101c15440130040e0f55200254440604007545400d00d01c400600b51464100000320340b01c80074161140d84960205420f040098400e00c6201c101f4111640c460301240a8902a5481c00c0408a10710f649071088d62812001038440c1031030007450380c0301d500407003110140310385003580c0718403840300ca6444400203070500c0b02d0f0f11290280c4481c001d1400c02c1c10340300e841a80c0000c481c41d001411842d40c2e40000c4c00008a0f4224200000308650052484040d24007500010498031880b0581020800da01c80107504071401048da880c40c180c0c465800b1180d0300c0c0300b1400e0040017075007200420340011008001d6800303680c00074014400c1000d1565942d107a50000080310405c82c8400502205101c030034420300a42c401d00140800032860421001340058001c2503034040b0784c2080c943c0f0035030396403a110030794001d02da00140205454030f040d00d82400b5601d542c840941950086100a0020b8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 905034865 1250 905033615 905033659
    0x703061b020607031a060f090406030308011701200903030d0204060e0109080a020a09150905090114010510020d0c0804050904060e0f03090a0b0c070b160c1a1e13080309 74
    0x20003e0312030081041001e000401c0010742187c2001455240f081191030000d0361640700b01c20085100340c9034080c2039850702c110f001d603108200340c84000e9641030400d03006c2c0781c030030b0080301e502c640740080b1500d501e80c0c402c000032900c0c500031082c034030a000c1c0c07000501280051700024540768000c8242e80340c185d034503280d07030207142c0340d2401e07440094002c240f070907043c4074100068020004504000407000503081d9074130b5550056510540d9010400c3e55a00441d010425884031201d0140c0003e50b4054403041500000070f40d83c19559a0040c1000b844001c418100401c1078101d8004060062880b4140d090070b040c60001015100710500880c07083d5690b40e4a0080048183c5015810080411503040e01e41455442290701c102d0700c995181c0075004d00803580300030b02e8006c2c01c1c089000e040541822281c920b4070400902c17164000c03032500030128000e01c2d2807220050071602104299136506081510041407210b85000d802c1242881c002d0400002c03494034800006004038280c1140c100942518051290000e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 905035971 1106 905034865 905034881
    0x1c0e0d031a040903020a0308092d2512060f02070b04050705060301050906010c03200a051009120f0924030f111b0703061b02060703 58
    0x1104140009001c6259400d8508010200541c0c4019540c0d03110154000c0801212030005800030304140041041581c0c9150708050101140301514010324040d001c024842c840c00d007d01d503503100613642d00028690941e0789146018109404000c01042d104019aa069151091107244208610060640f203008030004411402c2c01e161081c203040e802d0348030600c00c0030240300601440c0d032a140201d410090901301003c2c03054940c0303030540d25a15040e90100554540306c00291030420082041c0018030b1040c0d064074115040c0e04a1001103a4140d0400390544d42045007501e1500d000d0681e0001250881c248910900c1c0e44890140720181c019154080a8100214044005406d40191403d100300700c0700030b0001d405110707644134203400303020354030209440c0600c1c1101c001c1c0c5d0300b480a0320256400403410700003070aa4640d50030013074100117038210040c413801c000070780b0152180c414680 = true := by decide +kernel

theorem cover : BRFrame.Cov 904856115 905035971 := by
  have h0 := BRFrame.cov_init 904856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 904856115 ≤ n) (h2 : n < 905035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
