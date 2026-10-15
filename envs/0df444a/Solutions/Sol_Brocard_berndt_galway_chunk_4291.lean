-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4291
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:08:33.884275+00:00
-- url     : https://prove2.me/submissions/d29c701a-8683-4336-bd05-d2bbc7b25d7d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 771582733 ≤ n < 771762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 771583983 1250 771582733 771582739
    0x1060e01030e0303010801230c07200301090303021c06030209010312051c1e02070308011701090506090c09100b18040e0102120103020a06142d2b0c170402 68
    0x112040600b00401c1c0b009600801c81d640000440d224460700c28040c081115000d4090000320004108188800304102c40d1200e60201c8001c0c60042d03403810100704d05405020307054040d8030305440482055010f50041c500d01c02810b200004511540e5000c45c10795031030340002500440b240c0c00400010700405c000000814440c14054101864031840341c003241113000c05200210345410303580c0300303030b0202d0044400440c1c0b00b072000f940b40028540f00170303001d80f80c18491070110118041c500707420800c0030b506c03102c112580135040c1d82480c1000580e8030342c1d0340041c04141d07200b4480c501c0451046848801000101c88604803040e007800580c1e1400c290040c42c02d0503c2e904207031582032040c1507400a02c01000c2910310700240b002c40d135045005000c04003040350406414450501d080c44c1c01007400d10151034182c0024200750b0b541b200080c030040310071050f140d01c03481d650f00c0c040f68002810240c540151000a04942608011403444046505444c41ca00c40c12011420356074000d040c4203030102001354040d00207 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 771585233 1250 771583983 771583991
    0x51b1207121e1115032a0412030c05060a02030108100902030c0a06030c030f020f0d0513020402041203020f0a11190f14030c0a0b0301120f05010914010c0306060801060e0103 76
    0x40e4030181d50014040b1021244000100c1445541e4600340c0c0700b000d10014040c0c86181540340005503980d048038014410810000440c1a5500a01c442001c440c05030103c2070f4051031100302032030007170708004418408031210300641000580c81c4070780b48241d07030482c0d95020045c140090718800481c0200301884003a07130540100498643d0545805018a00526036554000744080d2000f00080441c0e51500c1c0c4256004c0c0100301842c0b002e4070f14025070314040500b02d000181910f43d0788603071000d681c009400075040381c00480c00050800b464244444007900039002e0301c28844028500707a40f1480034040003400260f00000003000785c14002c3c1c0001c03c0780341e9213596280705070b103c06514407ca410341d4000c00c0d0325440412000e00c6c6080500100702c582e03030151150a0343d2810901824400e0005004503000c9140d40e41155082c0000ca0300b1000d0800d821070004c100f503130240d05000c00c0480d10f0141c8900b0544c281081d4400840c800d02c80e080481d61156a040c0580e42803800480c0c801b040c02070300070704040d1a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 771586483 1250 771585233 771585263
    0x20d02060d2c0d0809061609050d08070519020a09020313140c010905030f0a320c0f0607050607261006091203051204021c051b120712 59
    0x841c0b5416079040d21510980c0c01c4448016040c1850a050020050100070500c014000100340004020350400da031010100c0c403130144400c0444846425500203540b00140b0541c100074008000d0007052200e000c1d0040d645050999030340526100c0c180303480250400030581d410480400c2641c0035642040c20000304984040283e25260a0282c3c13483c000c10545c3c1140303003444065030304204500018101603000d400c9401001a0780ca40b284403160002d0b100da070700b000400610018040c0001c00881240c5800c190a02a850f02503580d03d2000b0fa0403402038a100070a0344035071801c002560000c40d0f1000050201e0790321400100c81c00d54003401071201003002020002501040d4190462003000c13a031490840491400c84005c4c0412100d500988038411500408404280c0c808111441044042040d99094503507202140050344140c0b03070080c0da00302c036007422000c100c008142c0b5010310012096a80310b40d50100200300e1a14944d841c08a069409a0030401140c0070064000c1031a900820f071007410060 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 771587733 1250 771586483 771586511
    0xe0c09040f05041104180201020c120c03030301031a0c090607030c23010b030d08040f0609030e1002060603010e1f15050a0806090d020715080a0609060801060906050904020d02060d 79
    0x4030603a0115002d014422480c04c0c82e040c540301e2210152403003070350a00e410000e500042e44840111403000c0c047c002c10880506041c90820002003110000f40c00c4907560743c0c0d04c2c2408416407008078120030184280c00f0100c1c1c10412101c043c2c6404103402401145081125502510f000200450842d00522074980b4243c120340075000e0754000c541810008251030003110101410401020003400034086080144400710301201e0041c0c06556100700b00142211582c1401e41d04402441d22445d4420207501420310340541c041041401080c00fa00244100380c0c12008450311054020301408020740050300000110f20650441c0054411001000c0035503a01c03040811030700c0940317401222443e03003c00c040c0590200100548403140e06584090720b655410020f040142c4d00160100f03c08000180000c01c07140e900c0381c2d2000001f05404402081110b0b034031000307140038000d40d21800d10070500d8918001500d04245070141e101d981e005051015800d49907003002442e03000780c0c407041c404130780d01c0a008c60406 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 771588983 1250 771587733 771587741
    0xc0f05071502030c091203040608040828090302091509150a030609030503040c0f0b0906031e01090e2a0402030415240504021201090b03010e06040b01150206010e0c09040f 75
    0x500940060b603545d03200b209000003031003d400c40d0382c0150300c100420048558040c40003074115a1000c41150354036020030180b200584280101e00030b404c1c04036008850503400600500032030740700b40c82c00c940350740d203415102c040d19800c02c1e0b419402028a000083c3c0820360f54885038404840104907241003916511030504440300d400c821004600c0c008148014440310540d2003005003115000b0b41e0b04907040010b0070140380183c44207a4014000840850f651110400103c5031800c91666800e4040d0703550300140c0068640c5080c842c070b540c000d5100d0030101121150121250b88801c400306484291220f090100039440140140d07801504d45101040c04044c60107a0300e80150700300e95080868210100019000070035600091149104004014001084450362811200641400108148003801003400740c8000340d0303071849900402081000b0043d56042183c180e03040605c02d26004021740d0400d0340e5804080c05000c401081c80310001751100100b0300204105103000d0b201080d55019007421400396 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 771590233 1250 771588983 771588991
    0x9100513140a2105040312090e0a05190c0e0f0a0b03100e10080606040504030516300206041b0f090f0b010f09060804080c0618010e010c0f0507150203 66
    0x90b00201c040ca814410308000c14200054800b500811031440b00e01c001d01644120302c8000c280c05241d00c00d00f00035a0260100380e006040c01c440d0341c0700c585440440540108000c55195034150b85148000107540f90314440c803400c1032803a03214a102c503403000040100340a031865405901850301ca00c041401d00b10740c40510b00440d9410f1200306200d09001d50000300305002010a082860703a00b0007042080400030364036030045020342c1d0016080d1594203003100c4a21030800d190500f40c0b0a040c40c0e0003008104000004110100c000300100c041039001c1b04952200032500c40740040e80880080740c08900c2c005524603040605201180840e55a044c1c00e00010318154132280807141e07100b11404960300c803805910390400091038543c2c5440100000170741044140d000c0c04082148034400070f410000388004544203000d0341c40441c8d94900d803407a04100c840103c440c1c940b200f07500313000080760340403c140217814141d0b0003915003080d40b10490764200c509401014040e5000c0c024243d220507502c40d68070045002d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 771591483 1250 771590233 771590273
    0x150e01090c030c1202011e0207152105060d170c060f1e010338010801051b04080c0f0118030302060603010e070506041502101514040509100513 63
    0x101e1461824200c1c00441c00303034011a10b1616030040303c0010303a405842d4030741c1c40046090b03803500301080c900101d01e0011035402c0207886402451a140045421402d04000a41a0f100c0e028510349200c5001050342e0064900320b0308076545054400008807285054000007410340402d500300880400d0303107440d00c003085d14040f0301074030703424180304208640301d41401c40740540b1130344580f965255644014514901110441c100e42d581120120135003d69440f00112064242d09840c0a584400b0b440d8000e110940b00d40901901030040c2c034450f04551400d441c00c40c0d0b5040d02500d000301e85030b07060054041d42001d0590400500c01d0103007000801c1b41ca40c08024500030741c000c005901e4000149070848000080310010750b482030400700701c83d40e14407003100c090f0b880c209000350050350b10280c16450724007100c500703a48080c1801580480c4910150545044540005110b860850620f080c041111019244140c50f5041080440c08190540d08101e030440004440c1418008031501d4000030002042c0380610 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 771592733 1250 771591483 771591503
    0x31b031e0423010c02010e2101020406020708070303020a03030522060902030f070e01050d020a18090201120203070f030b0f041103090d02070b0307030f0f02030a0209040c0f0507150e0109 82
    0x104540d0b010038a90034640342c1c2c10031004945054070018240e050040e10007410030082d18251501c648824041c030340031810400301242e2039074451010901039040340c06100d0052281039400110041e00050000449400d90054242000705841c01c03400303810b004091406001003844070314804001903415180487c0141400686207206104060400001569180c401d40c454281481020540c400c5141114004c44a40c599821302e403000c01c5400c41180e101a1401400200782c196640d0690441141240300f41d03a111603840700900034504078002660b00d000010301d580133261180d4002d6205220b450310040500001d060307030000090a5950010075190411000320500c41a514200500c540000e803500141c5482418050b104056000080c1030f1002c25803906220411b080302d50b88001e140e401c03001010741d683d00d001900b00010b54410f0218a01541c41c09055a008a210790f0418815910036a02c00c0d1818280b511411010b44c04462007016259441c064201e040000f44141d8135413500c5441300e25 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 771593983 1250 771592733 771592739
    0x40e1f0605070201020c01300b03010e06010f0e010f06110f030313030909020909040b072304060206180705061c02131502070503030d09140706030e0c060c031b031e04 73
    0x24100381201a01b0f505200344d511450756440c407036803003080d8240c1241107a40c82a08203850120b0140100000c066010352070b01124070207000300451114140d40310300e08446051035a440005c0000103003485003881100301c207102440311500c107004c42403481c458041120150000001d0700e606545c802d0390b01c49034800242c4552001c1542150b412030050990f4282182082c3c6040d02042c2c402c500184010281e0580d01c001a005c540a07095100412074900002c090071110124003c407168403d0142c40054071911001540c510007107004110200b0000002c0c1030300d14504002e10100f41c00ca000080e62056544246142010161000d00344001c082851040e0b254035061850303050380900640030b8110b4000f850b060050351000811150500115400003a0480380c41c140b02c6208520324801250038000c91100151f80c3c1c1d4590000494200040203448081607914200300c514440c450134074409030002d00c8203122000c0f44010340c54523800340c181074a03c1c15180d40c0641d880701c0c1c0b603c0e20100386020003103814 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 771595233 1250 771593983 771593987
    0x10204090608010b0a033203120a09050a08030603070e0f0a0b011d09190903081006020106080a021306080a03170f06180703020405040f0f0b0f0105040e1f0605070201 73
    0x1a40140819802001002c001d64013242d9503580d2800007400503d00000c03042c5949001d4541b844860503107c0e0065410354211846680703d6206030303603c035100b40399000401c0c4002140d1241c0914650301070014188040310365180102ca40004203029854003e40b038000411700740030030090341f0035a41c83c040313032500703107040d032141001c8a01ca1000c0c94100095503140c5581c046104141541219080360602403581c1d4800188143c0460a00e00e2001581040d03028400c05400010103401401404107504d034040c5c031841c0c12401c0750503038410b1700203560101d81108050b0422500f801500c030507440b0041201612810070510340110f082045002540901022101300b500807106500442c00e00c050002608100340021403421014010800301d85501003c2076646005e50b046071700400d006042800500d2020714480014a40046803803402410140f84074914a047c005015054005840302c0d4100b81c04c0c0300004907101002070100b407042c0c0d44e43c0c0303201c1c1c3c1203120b150a600007420151780b2079030348403124400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 771596483 1250 771595233 771595241
    0x703060510080a170702030a080708090916090504091103060103140615010c03120f0c0c05060f040210120905070306061508091e190b160e0f0103090f020a0801020409 73
    0x402c00c650026030901001450030007000c1440542441d0298880180c1e0000904282c910b450090440c60f001981c074040140350005000c851004650b800003594401103030345018280c0800c0000011000d50701070005141c030b0b900a1f840326008914000605c1204008a0714100d82a0070903548070300040480c0468900810405a00c43d070aa41070242c02040c6000103001035211034001814016146000116582c550717100c41420140010b041c0555140c8050140c0302420901041c0c425003da05c00043e4815000204540900d40c05099243e0080c03411408441e8049410130780d1400648900428011400401a0030081d600600c0c00091040c5444101c4141802c0b401011043c8003c0a017040b049010100b082c00140c1c00b0070300c1034500c0c0080121420304040d01d2243c44441420b44000c441d0038042500603682c49035525281c0e200213419401c030142e0b64002c45a0710f01e6070010000e034001445511a4000400052003540d000103c0d13081580021580901038004500e1030303602003401c110761941b0f406 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 771597733 1250 771596483 771596489
    0x30306031b1a070302070512010e0d09061101060b1e04030602180405010602010e0709021b190c060504120f020d02030303070e0906062701050f130509150d030815030703060510 77
    0x7071510315050844c0d034040e49620301c1d0b00c11944291203004c00046e40040070f41110311402c0340202564804034001c0000ba19080e004c2c0a42400a031001d1000c2c0b40c041c505100c0d190a4544455986050114000d43c440c3d40410485040154210500c0000001940e900140010742032030311940480c04108424003049400590083c82160b044c00f0000440105c00301300001611056500541e0303030040f107288404210949248604180b05103405800c101c08541060002c040c402c5e0360040c901d0b0f42d210708c00c6500e40114000d50b10a82000b140010024014642c11190184080c010350041030040d00000c0c00c5030070480d90b420214095006291080c41c10610f03841d40300350205d40c21410207106010f8400e00300041030351985800700070700d0301c11791a078010f00030b6400d2200c03404030142d84c50f1410048607135004c10351b12a81e40a0000c020110749041c1e2680c030004080400940b03002041e40d050b403802c9944400242099060b041c00c0350203401c01d80c0381804035001540c0120380206450401641d0101c000040ba4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 771598983 1250 771597733 771597779
    0x3040e0702012301031a04050705191815170a0602071b0906080322050a06022b0e090a0b04050c0406020712030507030c1401020406030b100f090909030306031b 70
    0x400510000e41b402a510000813601c440d500030954440c6005460032901c0d41044e9405200c611034030061081a030711030410340d2100b6001d50012071103c220541941c40313040749424407261450040c02200000c41780d02100c45104401c40300c4188558581c1402c81c1e200941c10740b0180d1a401c820046241c640c10004000d1880960400100b894900c01f01d0300e0340a034a4840c0e50b4200d20300280950365220899480180c000104402810f940d60303e4065641c100c03401041403100c04280348014602d000c10040b410140441d10f9620140d06080104520b01c0720040400f804156540c202311441d40303c80c0714440c8603007074000d41196a01c0c1050310281ca44041d0354070146903e0280d00c60781c00041c1c2e200050320019a40341c1400c0c881400580341c5600c0001c1c3c1340308400e40c1c642c03010a00080c41a450380050300b1100080d10035107403030a400002110512000790410000c1908840204010052079210000441c046d10303000030030b01c0e12039032000c41c05428400d11191130416010f00744490115405550340d036030250 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 771600233 1250 771598983 771599051
    0x4181a1309060b0a080105040308011d0408071506090e07082107020a090c0201060f0b21060301020705070b0a141e160206070b040c12080f0c03040e070201 68
    0x81000504103100034058166481e140c010040802900c1d80040701c400c940106003546568032144040c5c000c200c2200c09900140e405030001920480040900842a44c880060151545c1e241c84d604000d610460045440901d0107903550031301c085074070408015043d200e201080000b00365070064500b40c0343d03400c0182c04e030b080b40032007219a0846400d484104060300c1500c507102c0c11a40006498981c25a10030440141007042404c07001ea41035120f01c068a1500c07400c0100c00fa282c4280c04214020210450302e940c206110444900c1c4510980315440300000b0000b5140c070020340d07995070501d12546d00c10b0780700b03140104160480541080d03101d41d02e5107420851605102c40840d9448403902c4845038400c4a1800142c02d2084425100d00050b01d180c024046a135210800c0c0740c9440e540d5030807101910012002a000f1990440802034211100e401151003402d10038200d4402c42c8552201c0290072503440104030015070303d07401500692166000d80c00001d055500601c0c08801410002042c541461320 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 771601483 1250 771600233 771600281
    0x150e041506051804180602130603020315041d190b180a14070e0c09010306051f0e0303040807060203030f0601020a08030f06040902150c16050916050403080418 70
    0x100c02d0a4440c02d01c0f040c043d8036070184034a404900149141004c5565451030750000406003d107076001082e030009040042100240e9a0104070201d010690750202d03160001a1110054502070300841c1a180040010322104005482e81c01d01c4c1c0044241e80c6a80c00204038001402d0103580c00d80d107075110340940440b070300c900c1c801381400e908d9a4200c1c0000386100e6803403200360180d5400b08414001340403061600c0c445410404d03d00201504031712017541c002420902c0101d140d08014900c9042d4041d40d42044164200e0072005980103103445040c4d0f600352009200004101d0004c000e075900034034035030700950343c0e07801c0404103401618001070220b81035503c0941150005032081c412280c0c01a00c0305503030505032700c40500040141001c9180654001c90034000c2e00c0100b9100c00007005000724441c1201c0c41e00f0320000501401039024071515622040c000c4c0014400f4140725807403a1211410701d445031a041d165a079485607500190040c5040d62541d15002c3e40ca40001c1c8200c107000e0030402107980180d04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 771602733 1250 771601483 771601487
    0xb040c0e041b020a0f03021501230d021e0301020f07030903050609070f0e060102010f060303030e0d09050a060c03110312060f191427060108180d18150e041506 70
    0x4804c48000f000c45080c0c0b20210305040c030900c9040040b405d425001c214959645903040040350622001c08403c3d01144030340e0401e031620420302e0300c031243c6c06082c0f98400000d5812124620821001a98155400300300c600c880000d80001090418400d07201c01c10800d0079824441d1070700c88010464012944960024400c180346038540c074088924004804010303682d51f800413030140803810042100c15081000200c00c141e0550004c0414002c0702045920030800c07460704030b607140b50b6031043c1c035040138502e10240542c900c2440114030043c020709018107000208026589590b00100000703201504050a002c030034a80043d1340d0354400000c85090411100c45041b201d072000d0b0f00d100b40009507003007101c0d810035034441000110000b003038494904504841e407280e054214104485441c00900e03810b0002c0c081c1c0070341e1800341460a948000800007010304134000c0c1c0324170b0100b48030025441410303140001e09401101081c0300c00d2080d951000c90b880301d00f00034001901c540701601c10300207108441c1844215 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 771603983 1250 771602733 771602743
    0x106060c0f06090212030726130902070602090d0c0f050111031602130f050a05010501020102071a0a15030f020f120c061c0c0c14010c0e090a0b040c0e041b02 69
    0x54010000140c500c07000c4c1300056924002d445109414000401d914082c00808034001d00e40700c18034001c80041001c10300c0500300340e205010308282c0032000c0702c00c00d101c10f540c01d90241412034420300c0014944035009000403a2640e802c4000c8805041da0a002e0003074002404080c402803000303003070170035580010300c2186850317015a8003402e150a040303441580035961403072070041504c1d49000040003040d60441481c0080e0008a8428500600300b500025070343d413051003181da949810805118813580d16840074100031201501c0320b211151502c0e6421a04020000c2d04001141f14082a0520b9011481400107182c09120b10b6403148000070740d525070440c400b0804034000340b4120380540d40c4030052944401641850b08804403510718262014820f44d810400c0308140e580100d4105202051841c0c445083c1c0c3c0520072200005040c040140c0c0030360411481268112404071008514410440082030844141030f00042c00102500d4010019051a200d1400b01d9030180c4180fa880c400c08000c065526 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 771605233 1250 771603983 771604013
    0x9060f03170703020c040203180c0907020601150504150c02040b150904111b0703051005070203090108040303140a0209151204080a0903050601080d09090b09070e060918090106060c 79
    0xc1c00c00150403800c00d0b109000132515140010011912414900003d00300101d00713040d400103500c0703110a00f0317689281030400e41d8821b041c150300800781607003400b40c1c1203415003408455030140082404003041100c0d51800000c0c0c10307101540c425040082c28010001515104624180559410380303a190101d1850000c840454206480200c0c0c03451420070940741a1095003100540084014079820b80c000d000308d40241140d01440403141b040c01d00c9240c1d0400c41d03000303440900169204004c3c045072940150b1840e07910500034103000840d03004607480807400325402c44070400319030b130b00146041081c070b001d9a02205060310341c08002d0070b001c503041c2c6000c40c5010103040a4604031010420509040c800ca005130041c40d030120684d003195a442408650701c010061609010039031003500400e00b49803030320a2040100e070052045034280c0707417048262124010f41e81c016800101c100088030968940d50581200c62190490036040c0f8600f031400542107908076000780081084016801c0042101d41c9031480c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 771606483 1250 771605233 771605273
    0xd02031206041802120304090207060501080f0d0c02010f11011401061103160206070813090f0c050c0a02010f12021308070f0602030301060e0310090f020a0e01060203070f060609060f09060f03 84
    0x413991781e2113030061450045a000700b0409000003000c03010050b4a0300803c0c100d80b5120200e4801079000c29030b568035000034030f406600142c0303d001940003661150000b09000e01c500d04015035591480300b900c03400e5a101c14003140760400070000402c081540000050071a41d545006107003080d0100e420b43e0094241000060b2043da000700c0c900d01401126400c58189010640070b10b40201d03a25070381c60014101504044151520b81084088054020811981c03103401d2400036100454280c3d0042d80d86401c0c91040000f08140c44544414107a002e03c0106210558003c6070200e06142400051910619030003558002c148058100007441d000415241510101d0a000d8801450f800c0403d02e0507181143c4c036840e007410044a0780500c030a0718410101c0354004d940b2092003d845ea10820f40b015401e00c903650059108000700780c040394072041da0f00403e40c40b88002207030055079254114250340864100040c0076098080405c0340303200602c501d000804052840f112030a00d1515101c1e8800c03c52296506 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 771607733 1250 771606483 771606499
    0x70503070203042310090303090b28020a0b100e010503030c031603020a050604030e1305190903030b28060311091203120c03160c050d050901020f0d02031206041802 72
    0x12441300b09452625864002605902020b040d24000808001c003921051700454050746000c21059900307070864444001c0c00c003a05017a941003101c00c1041c07903d40300f6030038114003036000000c0005580c0c41407280921100c52103480d03a50b0410440c00103401c0107921280c030070303070040000c00f002e040c1c048107948103403801041c1d0b01c4210785281002d81c10030f5001c540051103401240200010150411020164008156200d030405019071040c00b040740c4064030903100b0761419001e5405d00c10b085411111443d8031900c1c003c25a01d494a002c1884a8444240b407580049074010500070340540d5907503240100100d21781808102d004445080c0c1c54410b8040c41d500070f902e000a1003d03a0f030030800c11035500754402c0c06030241614000b5a841c45581098640b16035403440301512070856032251243c0b000b07054200001d04801403d0b00801d0704e25902210100703055024035007030301c28006410302c14011584016009185d41d20341a543d9000b802ca0000c180e42d2140e41740c46c40c4141040e144e0317a00c408520758161540c80f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 771608983 1250 771607733 771607769
    0x7140d0b10030c0f061b0c260303040b0906090d1e0c08030a06080f03040b090d1a090f100606020c010305070207050406080c040516081b040b0a02011407050307020304 73
    0x1550079051500041c0c068681107800042000360602104d003111031555805c1c181451404640000045041c00503241c0c2c80d805605100300611094408a000079800040302c0f0382110007626410741d0000ca40c2610b2541030344c4c080102d10342d400e000b110344c00003060b005444076921502015061407146260070803d1000c0d0511040d44601540c0d071210055080003410342c90307203403110786078001d014540900140c078000c0002040b0183c00010565050b50541c0e0383c4607042a401c00300b1700940800c28034040e02e82c000c41d001e180e00301481c08040f06000d492840042c120081003007840034a080555000c1c483c0341da1906030100445540443e042c12103142c24a400309403a04c5101080b46851410b07009140d2152915200245140c0c0008001141d190190b905000569521141d004440701080d02e032004984888005541c11b1182c82c070f146882c0400e034a2040c20700d078651120b441c854008484000c0903079580c940c140500340485000c1c0e94000403601e000e40c990b00d40544001d40b240583c1c0b28944204803080044c0f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 771610233 1250 771608983 771609001
    0x1e0a050406180b15090c0901080a0209061215030d1209053d06060804031b0803010e0405010f060321260f0a0506030c010c0807020405010e060307140d0b 67
    0xc0c0d00010314445010844425401c03c0c030341031034054030044004000c43c03003a4100341c140105594030031740e0060000d41c1007200280040d56400340c01814550740c1c0d54208840c12056a56001400b00f4200c1400c11040c54640903518440c000c8840004900c0780e4031841c0c1d440306160780001c140c071030032a0b4010003103408940b82c6481841c2a20908050310010700e00c00c10b00e03034070242c803601582d04001c4000000d4a100d54001c003040846141e8007c1070002a0030304c00050210b4000d0003003100da40303107441c2548110140c84d11a909107810a804c00c0c0203c11543c03040c8400c5c860240100803182c183c8440c01c0100c0d40c03469449210030039400e80510281c8854840c40b62096018a0380400f17012071080d0581d0042c48422018121094200c0e11481403114640108844200c0d9204641c850303140074005151400c41103005442c10201841c088940710410821200140c8440c041c560080485504c82c100d1424010101030900409404c508803820340244000c1441c0d440d110860f4515410201203000340d180c92580c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 771611483 1250 771610233 771610241
    0x30606130e060106030f0b19170307080a0914011704020f0d020319021f08071d1207060801060f0915020109050a030503040501060e0412030c031506090e1e0a050406 72
    0x1d00c0301c502030100001210364254105602d6049545820080c0441540400c001e5400d60520844100103848091200c0d140000a1080c000305c01d0f000c81f400c0006070303911008281d1040c10010700158081d4010410f00c94066a80640c0c1c620909045a015000d942c8080b04030000a10107882003c04c090b00c0d10464803080c00400b5899000780a9428010003040f00b064504c160320800c9006071082240ca04064510501c480d03042c01080d542c0b105192540302040700c01d130324010f9044d0040d504014030b0811036660300000c522582402009004503d1500002400200c4164014020310056140810049601c0705802d001e80300403045000da00000c11304124010804001e000301503100e14041d10f01030603001006140700b0b40c40307000240400341d02c440005107030303c205940081803107404103a2110090b00a030000d050020080c94005800c4a10411134942c6180342da0000e004114076050a1202c00c5120036615441b6150541e00c2e00315180e007182c03c100118000b03200b00032250380c1d03001140400c030315900 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 771612733 1250 771611483 771611501
    0x71106090a0317013203030703180909030f03020a09090e100e0601060e190305032a15160e091609080a030905010f12060e06030c030a020108221704061101020903060613 74
    0x3102d4880c0c40312719010b0107000c103510400300e4404e2150000607000c4c40b03c1c0030310754a180d407540e0342d8202c0c40c48411060b800394200d9020301007030000340070010601c40c903980b140401c40e0900ca8020700301c1c0c1120505c0c00d0112103620200c2005504440010710030f40b0340000100c80500c8058a620501581010421058500d9a000207103d4040001c880240002d011082603c80720b5000790014110b404010b280d65480b074218030107620040202c009440c011044041d0030703003109207082441c40c6030000000920340e0802185c01282d4410326080011100d68015802e001621003000249a401002d460190058a103403068904100d45003001001c00d074880d1911020a441c614014010503440c1c24030815440800c451070b50083c882e04121000e24680051030300c00303a0b50103071181c110b661550b081950040c81d5940d103040c20285003031036800016400e02440300e12800c1130710704076807920f04020f40180075403104696502d650713005100b0031001d9a03010446641080d0308a50050000080141d80fa000c2c2034545 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 771613983 1250 771612733 771612739
    0x110601053d05090a06020c0d020d0501380f061204080c010615030b03031204080a022103070806010507150b27010503070b12040803071106090a03170132 67
    0x1040164007142c01002070a1551000c42e40c031202c80d61210000c03a40c801850007070ba5403201c004000e850150520315000d0b281140980000310702a042034844070304003400d2095084c0000341d60311809440c888524000300c50f101d0112007062801c402c00d8009001d600a080c9070341440c00c00320010401f0802d00380120b807503480d03003400240a0a9901d99850500e010170704406400b10781001e00030095403601000300c810450101c075405030345844645848503150003c0c040c00066210b0f0408025641d001e00303a02400000e10010407503a246444030000b41401c00240c11541402824001180012900c001c1d003032020810303002c00a00f210044e03002805110602c091404c80348404220f03480710b800312006244c10303101c2c15001c40c1c80c032607546ea03e030b00340d0b52090303400c80e459000481c03000ca000614414019138002d01c0d82c0c42c0c000340d850020410310341418400d41d03007001305602c041541c0d01055089060309515081c603801e6002c880d80f40400d49038000c800065070507081c215a038091581842504d1140010003006 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 771615233 1250 771613983 771614089
    0xa140a111b030307030c1e030c0201061e1806080307110d0b070507140f12070c0e0c0730230d0c11011a060a0e030109060c11060105 58
    0x4101d40342c90394415954040041d00301880b54030600d015021001d0b0890010030882d02002c0c00c00b00841c0100070f01c011003c1103540398040003840d64001102240e01c8024480504070303051074411900c02c03039080340f800d582e20079041c90010005c00d40040142d6124603003090200801c503140100040c6140d8100000905a458601c00d100010783d0010180c400548528074080e0f160001c3c0f684542e07502e00f28258103003181d000120004202901002a0003510300c0303414407240c420303240e2164001d070b654212404854a5004902d42007402140a076070340d04c0008040298400000040007141002000d9800a0601140520b00b0300188403104011510001407401c098a45640d0700c0000017900c090240301c800564920b111040d184010301c03800002088040002c0c40c000c00302d00512407180c00c050b4100e0288002c0744920715a5440038010f0081d00c1c1e10a03480000e800c0019640a0400140038482203400e61262005011035229840100b100d0140f402e80c600e9007581d8a42940b01800c50955110304c0a00c103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 771616483 1250 771615233 771615277
    0x12060806070302030f0f09030d1109030106090e07060309020f0f06070204091103010c0203030609040b1803070f0c120c2102060c0c210303061c0501090c05090a140a11 73
    0x4164043e6010750b01c6117010680c0703619882802d03603c01c201556a0040354200300302007030352641103034000035503526411496802c00410500080c00c41d4403540c481c5a00c02e40b95007c11a03201310500201c0081c041e14141041829490b80210341c0080d20541c04501900d2551100718581da60751f07054030b03606c0d5401842800000c1040c600401a24510440107000b9800d04942e100c16a0001c41900e1061001a080384655692912510000c400c05030144001c00b51105c400c11120304140300600307100d8040c2c84160717440303415880e1980500e00b1941c804000c0c9000031107660002841e03500c0c05002c03600001c0000c0e038401080c0f00f0505802e00d030700400950101002550080410020a100b500c1c200c08840d500390340d114440307840140c4043c1140103070141d042003000400a10f4200d61841c0001c068940c60540181c035980c403a421103042c040d0503a000101c41c8410021441e04001440d8800382c0060107006440402c6a100a454009403103c100b00392076600b203d1864000030300361200903800803541c061880b5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 771617733 1250 771616483 771616487
    0x141218130f091506060c08030406060b040305030c06010b04060e09060312070c1805070807081005040f050f0c04060c0f020d05011817090904031220131401020604031206080607 77
    0x2981103403c440d02125003000044500d0310384188012201151124403a400041d542c0d09020340c40104226aa6036481034003166525050700608044c41c42980150f54232061051050b152250507031040c511401c08000c10300030940e0003448410303502c8040c3c0b406001602c0f988000382c00d000c0b4034650320740541c2000c0350503424070a04a6400080b01c100300701c120401d0f1800c1480605a500488109001c10f0f0300001040280e80b080c410303070340d003c2501411100c1c040d40b1040058141c0d4243d03802c200c581600c0d0710038408945009100c1355005900100994039140c5480d8014040448048001d400301c2c0c200c881030020744d01d5030094405000da001c0000c01c101030b07002341c400100c415254002d480445415040302584450501284c0e082c980081c5802c2042d615650215602c1c1c000d54100d070945602c50141d00c50581c10a00d141001418a0b4100e548550701d41d00c4038408652941d01840700303150142c800102903600480c1954215825190950350f40c9509520b41000d40303103950220240d44203000401c40c04035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 771618983 1250 771617733 771617741
    0xe01061e0906091a22140402042a110309040c021606091412150a20040308030106030b0a0e0c070b011e1e120f141218130f 54
    0x380e0024020881103880b5079066045030350b00c036007026072440c10014a440c1ea152240091710754841c020800d0500403039000b1a00150740c106e080f2041144030700d005000031498540200c03c0c2040d00890f64414500c001d10283c4135540d03c1c0d00f03002c1c0034000020302c6000c01035018011100704180140041c400a030501800070741d1746814190120b80001d4280001c00c0c480e20070b921083c11682d0202c0c0c0259040c82d00001c001c4002c40903000c0c6901880344c82114000204401c1100c0d02c95240014000f480514070f008c8009440c1300300858190100c070030001800020405419a4156001447c1c005954144c50340070074001a0240c1040b65002200c10811810032001401490f456100300041210390740e80384600d00107030303201c242c490749480c2c45144284020003607000b241c0e60304070414401c000340c160355818041c401d4a81c0d07041594602d07169001541800034110381d50307100031071180c01000f0402464441942d14041c07001075005da00840c2003001001c5c1c7e20525002e03a90302212404110b00c54140346600020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 771620233 1250 771618983 771618989
    0x120c151f050a060e090a0207140c130c0504090e0a02090108010506030705060c03030a090c120c050306090a030801060c02010c06020a0806100e0102070e10080703030f021b10030e01061e 81
    0x11468205021540741000340b4044215800c036100c6494000740301040108003c802060000c0456080c02448041800240c2100301c1c82140da0181c030504088030b080c480c0d0740d240e0a1030002424249401c0e0700c0455030010441e030441e28080400961903a1958440c0d08001844401a43c00f110642c0003140c0d10030306600240c02440101e0440310001e503503206000d024000d850340a40b45800610004042c5481c0b0780252b442c5c144105844101c56496448620a9030381e5603106413140640034100340164201000b00300d4010005800800100c034043d070700105100c005004040030404140c0f003d200310390147c170303203004901c1e441141551030f0400c4800080000b682154210310454142480c904003d004510801000e54180e0140082d54182007412401c0e442c0a404035130309070245400043d980d64280f1464003d948660307101c407428a42c05600030b2400703c0d42089010b031458614000c8440755250038151840076440e04010400400c461021401803499910030841144441f1640f181d8106091b020410b07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 771621483 1250 771620233 771620281
    0x3070503070b090d02060c07150b030318011202090a0b0705100501120b061009060f020f0316021f120915060b0408012306150418050402090c030405120c15 68
    0x284ca00100e004070303580c0100703a81484180d0010083c600103d007543c60b01c2c130041005210042003608074100401d2560b44103085030494814400c3c01102c80c0d681c00300c0b1441c08890100000d508140c0c0300d01c001494508144140d00c04240d002803940e0401c8014000801154840e8800300030b20b6950725008010340160104c111442e1480800040c0240303401e0039090008101580c4140415062200a03582500820800700c00e41c0310340308210394001e2041000b00705902446860000010691040c410030205e041c1c4542440c0058480f5a00c0069000300780c1078884e0070a02010418015600340f0130301003d40300803c0742c11541000d0009c070700d100036000200304032020706e0002c1007429070900640c0c107541c4000b00160120900640881c4103850301401203030000d0140104640341c95502c0003040c0d44101401c40c5000055140c0c4100025032034660401a03000544899442c07540c40c040d030302c40d51262150803182c0c546c7c000100d05041d15800c10002803000c4440689030351240e00b003101540a01082d40804150 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 771622733 1250 771621483 771621493
    0x601121a01120218010815190f080a0f0809060903030309150c09210102192d0c0303150b0a0e040c14030f0411131a0402040b04090e03070503070b09 65
    0x1400b0544200d03941a0894030161500300490801100c6060000d492440a603061000403006940d88640710000d045030b6503a003420f040d1501d0450030b100301c51640170b50380c8d542015003400c010075128881001e5696004121554030030341000003840364004c2186154041c4030100801c000081c2c006140d0003241d50442c0402e03690340e038140380e088170703442402d40c0c694000e40c1e2480b001c080240d8100010381403114010000d4113141c800ea80f29010540040942c20010303d600f41c1c40700c200300b1503410b181c40d00362501240c00d01e1034200c0e00004d000401140d03030040c00c1603a00c4107420905d03007072a407055014000d8101425039410905074020a250701288946114910b805504500a8080d01e04c41c01a3381010007594111790700c100605070203d41c002d00a035082d0080940b0702000d6900c81cbd010201740705142e60005005800f2a000102c1815004945401188104828041e10000b801a5812200908808034880020101031802d40c0100381004105100200340c000400410b010451b2040c469181224 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 771623983 1250 771622733 771622757
    0x32502010e0f060a050304060b06370f080916080703030e0d050606090403050d140f0f0919030908070f181107031214011502010605270601121a01 64
    0x10280c1800320746050fa00c85000c001c808121030260001d9580325024140005032035076207030702141ea160710203a8824400149a07104a066180d00300d50011139002c084c036103180d003c07002c44000d03011a624040788400d008514001400f815001c018010600318603000d003030001c0d170340ca91950307590752020300084011841458140206051032446007110039084001003090f52648024072040440c01707002541000350030406040c01c14032030f00404408804202514040385001300401e08810b002818200000d171420007841181c140c0050b003c1d90000c04040000c1004a151805880c4003150364020a02c0303018007c0006141e02070540a981151507040d074100a00079110a21030499010b1410000306400c01d2210b10007292203404500b0398807103072180c0021a030042105a420108090344410400d864041c000180142d082c00340704000d10702910704040060401035141c0840014001c0d000d0342c4481a40010000da101e504040300103405400d0420079113580d03054040b03600e0031100b240d901080f103920311750f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 771625233 1250 771623983 771623989
    0x6031606050a120e060c0f0f070c150f2f100204050301062909121e1c170c0f0309030408060f040809040f0b03010f05101208030705090102032502010e 66
    0x6507030080d007200003900190340ca02e001d40c145508a15400b890310142400102349401c1d6000040c00414011007040001c18074001c0d10007001c100003240441000358440c80c02d4a031035040044c01d031068041780c0e50100000c020010400c44c500c1c10748803900c41072140e880000b0317a100c047da00400950f1000e070300a0007125151801030303000200040c9040c10112070900f00b000d40345100c1b0050500c40d1001403150382c0d03040090780d0003481d2a1030f16291401502c2a8219680a0030040259200c460a0010700119046008101410890b01d543d0414828440540010244400042242d080032070b00c3c1c05040e22401c103c1c50b110781c1c94001c0d0107890001d10820f804140038500c1c0c600b025204961004180c0c0ca058504400c2c0704c007501101c0381030941640c90783c6407442300307940a004142142031610000a0a4a0f0064240707441c60155401103400c1d0b204c0010074008903141e681100c0d405a41414010750b59907003200100d00d1403141407640310500400d0000080c055080c4e200b0000c03000d000740c2e51944451280020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 771626483 1250 771625233 771625241
    0x61202030f0607050d050606040b27030d050a05030c091005041d0c03040f020f03250f05091f0b0307030f2a110127021315090506031606050a12 63
    0x189001324500b48048444c20046802055000201405150905c2d0307503501e880750550050003002511903a8210f564407552200e00c080355804d501107000b028a001c18880c040c1c558030034004203500708a400000034212000c501c00b00e48a02201400c4031035000700307c00e002000d640142c050b10f0360200240311460a00c014001c6103501544000f0711481c95902c0da69556a03040d11b034404220b801840d2107908036442e03030701442410040e9005144070b21000028840c2c1041024440d00f0090402a04c03079010321603601c45440c00c60f0b00000701c5a04458142a40d080300050780c4456204c014840000001c01228907410b1704030748150403000d84240655041440324001341e0408281140b804030354882102c0403a482a011581600d103248000905c200002ea1201042030451690300207112480d1115400c606105e10440d0001d03074041020002c0b04001c04039132290464034032a40c003055403114045505c0340e50a00c005103a0050000107013586070760750315003d403030794001c90501d1001c0351740101d901c80890b000b402 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 771627733 1250 771626483 771626491
    0x3030f010509041a010609060e010201060f0e0c07080a0c020109060c12051308070b12010608040c0302041a211608100c030612050f01060f150c060e01061202030f06 72
    0x4092a0103a08000500c0051080200300b601c43d80f401e08240701c9800702c80c1c01e8841c00b1b0001c0d0390301d40b141c0c0d60a1142c094400042c9a507501d0446e0f16100d0f0402201554a9560041c0c5035540f241030100d031207030041c2d204240107124001d083d50500284903540c0540001610100030700c00c0e01ea501241d07507030380780548140150901c00383c0501051411815007e02c2400100550b141041003104015280c40442d071a0640d29040007211038000268100c61116106019004010a20b000b8007031b46029070310411141307402d03c0000d000c1d54480c1040e49001117540340640e5841d401030710f1400444280b501d0304800b2130000c00710118901503c107415400044404100064075518001811074180400c10350300148548400c0d0000c040d592003002c24072324a12049480c2090045006241d00c49103075021908450842d4810342034050038030002c102c0100c030060030650308003683c10b2816801025080580c0507089901b141d10455181000c0410381648890654909a0007541142c21010b0302081039a52100291 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 771628983 1250 771627733 771627751
    0x30203061807080f03070c080609031836010e240a1e06020f06011d1005220605180f04080c0601030b09010e010605090c0703090b0705010615020303 65
    0xa0000d41407880d64080c0391400500c00d8200c0740310399030352003806003482d250009202e03a5810001d00c031020b00000c4115200517200c5070740079258500305041180e907a8464055811040c1c1b0714020503115940d02c18640709201c0020366181c140005001c1005c076840c4141d0440311483ca01ca807800840d02d4104000010b120740c400241c40e14041c009100050a800c0048090580c490843c02021a8000d2201003080c003900741302840841441c00c0160103400d00040140400c100d91110004001c070924003403040340158102045610b00d62541c203040c00745090390303800030341d00b003400750b0080c3d003200030000255007290640312000c00c40c5d90b03241e008000400e11070302030b8120200b0b4801c02248807501c18084964002c1e1003031110501e803447e9040c0c19410200c0036881a140c90340070108001d01510b0030f00800140c084c650303000304402803c0800280700a140034100e8924803002154650030075005180b02006801e08202603030b152a01480d12a028000c00d001d50303203030701560241810b03515000209903030060f1341d0a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 771630233 1250 771628983 771628993
    0x40f090605042405122407110d1b151a10080c121e090319050a0c0b060109030503070c0317071e02010c142113051302090603150405010f030203 63
    0x1190401c0503030081c48854035100e00440722140e000102e007500c1b1160070720700009444440d1902c0e44015001e22010400d41e05150411134408070020f6114100b48118030480a01c5203040d24141001035540d41050318403002c483c03078038003a281c4415401c18510850300c41140d17800030f042032059080302d020300d0175209150f400e402031082c241e10191003030b809640b0a10f841390311000c4034680c0600f8550460184d03000d243e07a800004111083c1900c040503180c00c4030650400d18504240814010404031614101621400f514070104800340c0c4200074174801560407800300c0e6210020740c10040c803024900e1004960f1144c20295400d0805619000e459046d50800f01c1c00d407015815805c1c02c0070554520340100e0400c50524441d0b40044c128001b0b0750b21090f49903000301200e0101c001115020400440c101c246400240240346141c600064190b041e5101981c20b14090041004094040c0c0a603070008c541c03064011040200480c1d44c02c01500c03007030300100c4043c0310903640d80a0443c03281c06c0c103000c0a9099004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 771631483 1250 771630233 771630239
    0x26040e0105100201090c030c09050a020307020a02010309230105150103060315050603012306040501170a031b08030403050a091d060118030507080a021509010f14040f0906050424 78
    0x8105250b0280115000105000980d5500c5424111240d003084401f1070005400b4402708449101d070030b601c219215421451410710a0020396145540440241055199030041c02001030340b20081c6c40071001080a030905003461000703036010b054116841c14103002e0f81e160f141d03400c0d8401e01545089035000b000d1005142d980c240c160019280050800f47c1640d01c1d0780d00000c0b0f440c004503813410044c0400c1540003440c00c0840c10402501d0060380070722000c4031a540d500009420101d1004000e603490305064003d0341422740d9125500c05054005422010040104010f161b084001025806030942e0740404c995160401c00c1403c4414558603d0b092060300e00103a1554040c041c0e158000c0311280c4150b40440da2962078518028160b041401c103500414100b20071410700256101c400500c5502d1a4142011000002c0a80300da2654101c100700d2002c1c5040900240c01086401410140020607a40ca440d4070340240681039a220b00b81c09549489418814020b08640b25a0034883c00d074890450946 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 771632733 1250 771631483 771631489
    0x606060316020c0616120c150b0a0504020309010204150f0512070c0f110f060f03341806050a0906050901020102040801020d05180a053726040e0105 65
    0x152581840381584a442d49440c00c40c1e980c4c0d4042d002100301e081c4c84460b036968501d8814119a0369420a07002e21015144120003d07208554400c103030000760b000001d41e02420f8000466000181d801541c009200005028880d44103400510036500c54010304416101038240131603041003142a180700280d0b0900460041103100b0b8000341d0400614901194146401d0700c5502c80c400b0403c00454030406080c100b5070309410045060040041c0443d0850f040c0760036440402400c1c80002d00c00c0303d104410519041c0c01c50162a28024a8201050500210441d1000c00b1300b00f41c6040e9900402500108800a82e0a2284089601501135981ca03440d41610300002510260060082d032030545d5000c3c400441c50759424070151024105e0314501180301d04000c0c1041151b1448500b90049903000a040c5034041000021464460341c8a5031209070700843c5510101c46140e4803030342245500c19040d0440092000180031010303003040c189440c030486070042f848298203100302e11a5107031000c0c00c100100f084c2d10f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 771633983 1250 771632733 771632761
    0x80a0503150603070305070f0e0a120c180e010501090e300a230c120f090a140103050c0a020a0f0215040e1806010303050d0b1807170906060603 63
    0x110a9405660100d07401002407103980046510200003a9900200f107006507101104140740c115a08021844000724004208014075034001c2e041d01c9420b0511550412844c0c000e050010005004200c5d0014000740c0500081d01414808103440e6083c03030f0010a03010080c1c410602c8400040e001031040500c1d4070b401040340071328884c00249990039041489965103804004081042155850410306400203802c0002c044000115501c074600078001d0581005000a0200c0300d2400c00d40116114043d262046034a4031074884080e40280440f07000103200c942d01c002c3d45480a1007601c0a0246546500500c561402603607041c0c001680210910707000705450104100c11140050440c0302c0d038500407811980305500660001e516000008208680c1e0045020380c003c1004542d4050985075146840040c601c0c010381c031802890b41d07541d01c480d0701d050b6110000410101d00c0d0901e0b460103494030201c09000c80c0b4101c52140c02000f00903001400c001b03004901e00f84a000300828103403d42d110858810406 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 771635233 1250 771633983 771633991
    0xf06090e0a1a0306130204181212020910030504020906010305160c02011704030e1302032a0706060803040f050a15050a09080a050d1d0f10090e0a05160507080a0503 72
    0x41c0c502c0150b05459901c0038000c03280710b45041c0c011501120200e205101c1103401400362890501c400000c20306c00076428020300d544a01c640d14203c0d015210701800500244101c03548550b000c0034004c1e20702503488d01074200b240319500840d6030500c030303a03921001135050fa10200c480b15a0802d01c900b04400e181d0164988804e25801803400081207800200360300803540043d81c00742c000c1041d418900e00c403494501000788042d91205415401c5041440044500c5c031605040f014a8180d42c00c003080c0b4000e1a4030550702115005481031000d0790340c1d07420140c3c69900ca4000c03855400502c203804100d50402803416421901c6840340040103440a210455082d04030040300410040c0480b8006030f051030030004500824014400740c1805943ca96016054125003000c85c1c0541c5803181c1d000419a50710b01448003650001d80b00055000490301c0112040d40700c42e0006c41e0f00ca92108240b240803611a0700880c400c0019000140412480d041c065903075010f90400185003800030442043d000d440f0f00091500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 771636483 1250 771635233 771635261
    0xa030312090611030f0702030f0d050402010e09040c05030d140d0b01031506020d0e0a05011d150c06040203190f06180c0306090209010611030409050c0c010509070f06090e0a 76
    0x1084007554901c41616102e01c001501c0309000f00510003c43c403600d000136000041400110328144a020303201d4454002c4140688120350755000150569003d10710a22450200500640c500d1030640740a0f410510346004140c0240b0500400c114442d01400034043c01030518001182400740e1101114090560601401d0405860b91b080c00c4c031a418503c1d402000c0d0202750003420442c821114020600c03460100c1c00f9209040c0f0324410800c59800100500c91800308449441003004251301244121440c950790344003158000803500c0036480082442e40c0601c0c0f0850980e0920300080d105403491507500f080145c01c1c032051114000025050b076210201e4192240c015501c524010307142c0803100b4180380d006a8400e03490f1442c4108616095880a0141c0b00e40c1c00e095204c4600083c440e43c0c0d03805035000e440c8800d56500082159011003900b602e0f0607141c0540203210b58504034043c50744810b034500c112004001c400e035010840718000c0a880d01955034442c0524141d80d0f0742040300e806402c0c907015040ca = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 771637733 1250 771636483 771636491
    0x1140d09020d03050705010f05040b0402090618010f0602102003090c06040b220e0c1b010501060c021e012a120905030f0616110f06160f0c020a030312 66
    0x80182c4425032048500b40c0607407640c3d03403900d0b0f0a091040c203540d2410325140303505180108110000d000310750010f4000344c050365000d403581e41c0c80010581c0090305d400050300400000000140105068184070151012942520654050f10b00d80070140e440e00641c44000c203071901c2d00f80e050030f15018040e560202002007118000d0010002040c0d082c1c1c000e410228200100003000600103001900e42030965407000b0f03070f400c1c4c0b4915041c50301410750744c0075100c46101140001c0d20a40046008180d1204e42c0440000300310700d583d0360b00042c1c8803840c0814203c1c05005400e844044081500110081c102c40603140c0541d80140c807821702d034080788880c1c3c2c4802d040b0940300c011404500e160304800e000d440c1c030b40c031841ca51900b404d041601c5c00381c81c2c110b0440544c1c0460200034030751080324000703105071140d403c2404c40704001540003030500184844c1501d1600c24041000200c070f450324004445509035445803031602c40103103002c6036801c2c4a43c01c00b17500030407502c108100091003005c101905400030f410010f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 771638983 1250 771637733 771637751
    0x3031b030705310b07020a0515130608010501260610030b091003031716050a110115050307051002070b0c0f06040501090201030b0a0302030a020909071503240614031003080d050907060e01140d 84
    0xd81c090f806600702c2f01c0000c8a40d00180300558008030f202040004042c20042e102d171510740107a4030500001c2c1194012190103210100f600c2c06500440a00b20004110702d08034a890000000d00c1e50640c403096000030209254640d025103c01c15080c002c0b00944020482800451000d913102d0b4081400003041240c0c00840c2102d4590031301c104881107076150050084030349060201882c0422075003011b4401d52218012554494001070500101c541d01c1e10102c1c0c440c001e000c80382c1e0400d4030a01102081c0c1c001e2a081004001040d813110314558401d803030800c0340c200c46c4014421048000d020081d010b5020401103030161418a090b507501c203046408451556849100100201c07024080b01c0300843d40320b003242052504403001203240107008180051646140102c0242084840c8142a5031414000003041031001101c842c40007640d0411403090f40c4001560f124001030004480d81c403500d0142d000c002c21010f125030500f600302c90050b5252040c04074540f04210155000103007a96039583d8485500d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 771640233 1250 771638983 771639007
    0x20702061e160b040b01090e0c0d0f020a0e040606080a0209040f05100c050c120c0a020d050f010908070516061d01020c19030b070203031b030705310b07020a0515 71
    0x1000d0514810f01401d1100d0a1500d441e004803007040c3c000820a50404c51212680080010307030a004080454400a0b0440d15040c08861904010000b9422440328400855045004500740c0e015a00c6440c0400450b55141c030301645908086070002d60015119000c0303008140e0070345110010328007540c10b5071800e8003078030b9405088840c0311000e100490700c007050742c08848005001d221444e0311403400e0380380340031880c558407921400c1e87c40009101c5c00980d21b07244140402001440c030300403226002004203842c02c3c184549146c005030307802c540710320a40c00001c1d01c410304101480201c1d889600c1e40f0340486915110214401c003c10011740c11403080200544096035070214004091036100a6405a00c0c114107101820f4140204a0815940200107101c2c11060f44608003008100e400c5840d130310ad13201c061003107516205d504007101038243c0a0f804030240910505984442551136440440d2035580d03903000340468080c804001c0e6014030041c41c100240d042810340c85503802c01000865250041516007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 771641483 1250 771640233 771640267
    0x509040f060608061011061305100213050406120f0b090c1e04140403090e0403090e041401230c0906090d060c030b01110303070311040b0f030415020702061e 69
    0x10b0000a0040020b001c81030a001c0001041081d15292410f404145031404036542c0344050701416440c03000980f42400d104040c07040710340440440e18190350304c00742c81c81138228800c0c0600902d40300343d02d800000a01d0301982500d40422540c801c00c048840380303054a441d040e0480c01810008240541030903888190b88102e080f000c03000320100482c2032076800c00284000c9490b095200302c00380f2040c03130600001c250011540012549224070121030356895180c00c03120154650300402025020b0b90a010801c00c1040000700d0305222603008021940e203481c40c2d01c604c0c003400102d020354480780401090405074071200910600b08040d200c5417a0810690200d81e04005130740041d07400c5a82c4150200c4101d0b0705010743c4a02030800d190035080c09038900d031603035203e100103000d800c2419501d5400c0c50000c488038042d6402055908043d54640e0070a1154900d00d034021a000c40c0c2400003541c80398152110380c800d44000740d4002d05500d085c5110030403520b051641c1c42c01c44009020080c4008501c5c1040160 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 771642733 1250 771641483 771641489
    0x1080406020432060a0504030f03020102090a180c1d010e0303090613090b090105011d01110f030a031433040f06051e0609012f060108060106050705030304030509040f06 74
    0x28000f1510a55000226103a02d02030396054410b66042001c2c074a000d0744442510241d07a0098800326504c8200d240607802842684002070f080b00d0780e41030019000240e130b0314495003882900d4040c02004907429040b552035646a9004400c8240051101d0326548600074038101100085c00f00c3c4d191882d1840081d01c2500f180080e8040710602034002e1150f05070038040c40d03001e020f056a01035055414280041d1107080d0070007440032410502c45032219a0381c41800305030940507a00058442400e440c150701c94690b0b01004169021904203c62000c006140d101c0f000c0c481d800001d800c00b41d814070007042a620100094010b8410603c0c00d100300303000d649a1145005a400062001800d1807810090100700107000c1c140383c0700c00ca0200c2500c0d1301502c0c1e60040f80c04d094424070b02800d5030101400440f2038040541d0b01c0701d900e090764551b00c00c003140380040c000b0306a595000459510380c1e038995040b0303824411120018015001131004c1000640100080e200a21000300040364804c0028140012104198 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 771643983 1250 771642733 771642779
    0x705070f080f0d020307080702041a040e01051f05033a051c05070903060b01170c070c0b031e07030e0a030314100b1204050f030a0305100e0f06010804060204 69
    0x20b10310360309140c8100050401c18100b40007031170501e01e8689075000b1500881001900650315040000500c4100c01d1400c0604040180100300b002d4450701c26038004d107800c480083c21110088680d0100e100100b031428120342c8000c006201442c0250000883d08442481c1c54814800c0300c0301145c00340b022607401c03004003d1940c1c1c03100e8454a0703175061030700da4101c180104121549090b05021410742e1200107001600d030011008201c100100d0012100c2d40710381c040c452014600f400501040d201901c1c01001c0b99409002c141e80006d48800561509100654a000104c4401019400c1621114410b40c4e8040c031181400940b95105107071aa060a102c00d60441c000307540c40c15145100100d513050703560803c44441490010508040f41d144d0307a071144040e564280956080000c04100b4100080d80c100d405000659817106030315003025010741000c2d04c0c1101d000c4504070300460805500d4a0581c1308103c01c41d6402890344441c401034510400103003060352559001c01002c6065404002048492048a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 771645233 1250 771643983 771643993
    0x105120723151602040e1c0c0c051f0305130803010612110405060904021c02040314060f0c040e04020d14031c0207050304360209010f17010b0705070f08 67
    0x5a4108005000c111800322030241c81446800f00501c1031804a880e070703c3c1e06032400030301e004c07902000600e4110090701c80140d8180719956516455440303480d0401180c8603010747c002d215241c2c81006010318484c00c41d120150704015410317002c20b2094011540003241011300703140c00940e50300c43c840958030903000040466a44500155002014801e405500702c10803a185d08123400c003400586c07580b1034900e150780700c1c7e40c02003807068824015801400b03212a01d900c0440d03685942e441d21500c4030501e514480000e01032a00082e400f890519611803049aa00f44210b103000d04100043d460410003400998004110110b04000500082041c03181099164001d40d2245d01051480722644150300003035119500510004002840c00410356096801203140204a07032100c030101d401d5441d100c0710300b82c7c1031981c20900003d941810703801041e0f040400c0c1d0302c64041032400a000d544884148680300b1a00641c0700041180b00c0d0402c0203410541d110b5810740f00701075507402800761b1486164020340c0b0310f6080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 771646483 1250 771645233 771645299
    0x1505060f091b0a050d06030309060809010c0c020603250206150d0b04080a0210020d02040614030f040b06030123061c0b0714040806070c0303180b01051207 68
    0x80024110080201100c0c09120751402c40b040c988590101a030b544a050004a6a514124007413826503101c1e008a40c41004056074a081c02040303010352b0300c0f03804c003c00c101d00e0100c0c03403d0074180280c100a00c03040c0c40d90000c44c1034590a1108943c070082c071400e03a1a250b804142040210002d101364024020f0b4001d1269040c00641101020001c0c8038807441115144c80383c0b070010710365105599205400c44a5151148141d800c10ba00f0002c809104d051034038400900d490900c04264040c206444c5140c0d0703500e00068503040c9045042c4001d4a02d0030b030b44801000001c00185021b440c3e203920240103400031920840c400c9408603080c2165103172039a8100120100300749810000f5070724000340c64420040d07000203400d485a291015014104004000c00242003086900610003145c004007455000c030342140c900820300401111500204600090620001c0305408a20201c441d0b80a0381145441146034079142c2045129040001c040d1482e000d46000094101c0031500b500c20388010307041c1d903000c409013 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 771647733 1250 771646483 771646489
    0x42a0302100c1b0f1211060705070317040e0a020903100e032502090c13090c0203040e010602010203150604050f040f2403110a03120503090a080f1c0516081003150506 73
    0x103500300917081444000080d0116407116104100d040b802d60300b040c2d50720700364204203040091a40000d050300342c00300d001c0f441e000b107442d0050044070100300e8260316544510428000303034411000d402e82c1c980c0c80040f910f042d1901540c031100e140d850801c2284d142c4008020700c02c15024074145288260340c803104094066080003241c81c2d0f8401001090035180031041114484c03108403501800b99550340d20000084401d00801c1294090000d40464821941e034032217000b8080d40c4219151540020803503000f01e03075410a84156010b0740d0008007944000d04841c0c0a1100600701c00010081094071582c015030100058024042516110b40c0b20940003404d508111102c0c442564034540100900c00080000c07a0700c0e040307112920160b629020750b50b070716420015481c03c50380d045e01a2400382300003010349902910700010300505c4855004a22110403030388517502201c00843d1044003401101c41002c0c41d0070b1160241e50791002e201540315401985a40303481d10702c0700880d041c03541d020766900f00b400410301d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 771648983 1250 771647733 771647759
    0x91c0306090b0301090309300605150d02090c1c0911011d0a1203051306080118090812060a080f01140108030a1e1101090b042a0302100c1b 61
    0x40b00350b0080c041c0903603d607030081804c201442000609400090303111171520100b000c2c2013180d030f4200002c140c0313020a0b041040c0200b0342514200318520281075075420f2400c04203644016560014011380440e40c805c240da01c455403081c0d00b10b078181e80200182202d540410312981060a016980e20705802115000141c40070291074000002c10b11104a4010a9607500d5502003da41c101c0164084261480c5414bc1d0f4034021803850401407000b0f0300b004165203500c00140c50417a46c01d801d01c580d01054034500d50003201c98004003c2c04181040268094400d8110403054100b503001d01061071080d600c1c5034031401e05020719610300d0745075100d641c4907200012504c2240c2c00b43c40c203040903500e0003c1c08400a084500754100128081c0d040b07030540d1020900a0b9200f030f503100000402407080c9002c5140c07001750990100c0301100c0f242401c01205002d48030003071340140001c0204d0303070481d10036040d9000c0101500c0e84452481c10040e00b41d00500025424480006a6240400b01c001250b400c0660301c1c0d80c4c807 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 771650233 1250 771648983 771649001
    0x613050901030f050c011418040212090a03031815090305090d0303060f14030d030f0605040207030801150507020a06080408210a060905061e040608010c120b0319020108091c030609 79
    0x7c9800c40e0a0414042001140c1941d6840360005d0300200d80350000c18064010400740c520244000003c0200402c00400c02400c4035100b030f60b0400c4401103040c01c0700c581e9520780c28081c0403035001c058003d01041666004250607030080c02c04505044881d0b002421100b49d1880850020f51161030411042c640407550341e0140040c00ca103080282d03900d00220f070340d44000e00c1e0720100301502c8102c41400c2c03030969031040000c1c01015000303640d10860f0707043c05002500c0a00c41c0c80924121003001c01320045c83b444c1030701c1c441d590040c5040c0040d490035408844000c00030f0030070740d4200010030451512000d14010308011118400c407004a500d40508900704946690b84908100d5013441c08001c0c4a075151803c1c8850f0090140d6001041641000810014802900300303040725131800e01c4400a080c0c120035265012103202800340b102d000c10340c080c1034444003926064480d44a1980071100190700540c160765000000f03100301c0d454100040c1d100c0100a8400040501180d0b803180103010009550243e0048 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 771651483 1250 771650233 771650237
    0x1d191703130b0f03040605060111030a0507020a170303011502030f120610020105090d050a0207050a08070519051c0206121006020d08160c0215030a0501090b0913020613050901030f050c01 82
    0x2480c0d0002981c3c003a500c00144020291175440c00040e0040e07005a500c03181400240041300c1d20b594003140054519070200c07100b41c1c85110520400110564010302030544841c0b00d05c00f450550b4039119880b404100140f503080f0039800280800402c040740003010704882902003654180c1414684140701c0d19a0110001500316410710b000c01601420000e881e0516246920b482541d0304003c007022402c00c2c5c0d01d60812079001d52000d50006030180c00048002c2a80c000712030140145030320300c0381c0071429840c0d84245034104000b68400107502c0b07001c4580b129141d0000e02031034075180d5a401c0c261094141121040d0f801030b00c2070b81c01d0000a078100140c502c0c400e0a410071003420309285044e02e462002d01c40e9510200402c40c0455011506c44028a07030715030012078201600c81c1041d00c4000058542402001250307441d00128500c1c0f4541600614060340000c000000803072095000d00515911611900d045d00901c444001413030f0316078490550096000e20b488038403801c0c030344c5040c50174031030190b0704581 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 771652733 1250 771651483 771651487
    0xf0510060e070915050909040506180313050402030402041d0d030507090806010e06010306170c27070c1b0603090606060c0201050d02030406060b0703020309101d191703130b 76
    0x881d9038001501c01c09645003c0d10151300c80d07518250448075485030001c2c650b04008808240410000d000070ba41d03024011880541f0341101c442d80c1850340d2030095070010103006256a0b010421810140d00031604240050300104010003a041c810752540d0751a500206150321400364000700c42e506104158000f2a180b0701011000e2400c1c02c40e40c1c1d40c0f04103005030800c844103a004521203a0199209000078040300b244d031406040b4a0740302da5112503040f254640510000c1c155540c40302c1c00502400f05014002030f0a0030706444035030040350307030a86103d01250170b080055a0f441c080c85102025070014441da540100303140841e13103040e0040d81e02e01d034058428480c2c1d541120340140c4e04001916440d0362070040050304d9a44a00b044000340a031030780a06a842800120719090650102c007e002e0064265212000504403610440d142e0b110ba241001007200d607030881685614010b40d00b00d81c0b140036202042103040c0ca0702307400c0308603102c40d035480c0300d260f0310005926420807801c0307591000600014101c0c0f8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 771653983 1250 771652733 771652741
    0xc2102070e010f0b0f120702250e0f09070302121f0b030304030f050a0b1302031b0a05060702030304081203011706010522140103060f06050306010b070308040309030f0510060e 77
    0x1450f000300e40121082c1d42400704030180c40c0c000c0d60080d90012021140d03d00310071700f000c4502a4441003601e0a400134400c0f1100c40d040c0607c8450310b02004c5602c52440088c06990b0a41030030a101c42c05044d2002030b000300344000025076518010141801d55000182c00e0100600b046040350001080911500505040f6103808641d80030040c1c500300c0340c1004034900c245200d0300c4d00c203042441c0f946d40200340c2c900c118240314404014545200f6002e20036803c0b10f0400c1e0b42c201d0700c000c1a0f00a0030000c4ea0140540e03d05015509290001c6d140071440501217030300301138689940a082c000584d000f41200ac0010004016186103001c03090a60384500c000340500d541000046026608002181c2c51840c02294048c1c14424407503016094404039009001c402c3e586a01c0d05002a10203030442551050038000082078528020030202d04032402104254078003401641c05403020039004005805001c1210390000100c1c104820304d01c103551188000c1c00b0b41500c0c01302c1c03940856015800142441c28500100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 771655233 1250 771653983 771653999
    0x60e1c051309141f03050a0b0613290409172101060f030203040f061803180605091002030c030424030506010e21150108012403060c0c2102070e01 64
    0x3c180c10160b20300842104191000380740742100d0f290b0340300030100e00ca0581e0020912046421441c0565011030301c501c48081c000592078281c910301000d40c1c010800030a0000000f271444408510b43c40381c05000410a18283d8a0740120b0080b0285124195000011542007000c111440362804000c00c2100c24129410900000d1455240040c80c40038160f002000c10184071780300041055a69100e10244400a40441c415001c40c159280881c0070404028401062080011810003902d10b999115800d0a0801041021059030003a00c582540010440395480c2c620900082c03020301030800c1c1420015108852040078100c80310860020940790a051150aa902240040c10054100d4002032a8466204030300e50051700c43c00c52402522402040ca0441140922014106e5456000030010820807028a000700000103984052074041d4680620001e02c3c550300281c40011585400d62510646e40e0300d030480030450300a007109150103243d084402035810008803014040300100040c0c0b41d450160b103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 771656483 1250 771655233 771655271
    0x15080a020a290d06050d0602120f070e06220b040303120b1e2215140f21030f0c16050105090d0521190e0d060e1c051309 53
    0xc05a000c2c40c001484403841040750003240161400070516030b400b02c96407030402c00a500007813035144401d90107400189200e1070103413103c2c46a0101e44130040150030540400443d90303c0221b66074034203c800000030505022a001075009400000d203510398a90039414050702c6c4212401c81c0514a905110341e8400b81c3c0c0f80c10710000112101454030340c0c029000040040d0344521503542c03d000d900e03a070b2140501201d24580202014074282c8010b0303515a81c0700c4556910380c40405503103540094011103460f02508154403d1201e00c070080c00d8643e030395250402868110303401040031010502004caa031501c2000c2c1404141c00b1180b1003082801080e140600180040c001c0c650001d1240810309511818044103025068620300301203203864801c803491700840da03149c01c1020780401524403045a03003100340c090855915082d400900071000d101103030b034649001d0314074030400c10002e009038001c0100740150344d241d1144104460301c038682c40c1c2580d4000c03084504510303400000b4890800000554115031220 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 771657733 1250 771656483 771656549
    0x50f251508072007050a0512030301050f0316030f02122b03020f0c0d0e1c060914100b01030b01210b0a0f080c09060d120f0315080a020a 60
    0x400d8105552401c00603100320303403960040c07040040f600b1000301034040c0125a030f0f004e0744e074121241c00005440f40144040a03480303010044031540104014416464040a01050304070010101c40703807400c950034030f1450002d07258012a043c136540036041085250512a01c245560440001d12164002c040604101100040c0c003070300049030210300c0054588240c040ba03400d01c0110030860b54410200070450703a10800056584000741800300340305128a0455001c9856401000c00b41e490701a0700d0705e07070304000c00e4050804c03100c205004031000380703262003404040c040001074400047d84034040780001d001d0320f817803143c0c2504000c64603070034000b9140446242075844401e02400603c481001c00480c0600146e40c00229820030034071070000b1a0380000800c480c108030169074500312034031000144107000c8420980244181985414081c130103214190703a01c2034011500c0c0c04250700600240042032900260000d6001c1d400c440c0d5a5000e605000d94142c00800040c6044801e181c01d0800e10054095800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 771658983 1250 771657733 771657737
    0x1503230c0327070806100602070503060403050a0207030209040b0402040c1422031b080f070f150c020a1401020129100e03030d0614031c030207060207050f2515 70
    0x3603040380c9040000041c000004082c408030b694660721100b00650358582103c07072810285209002048492000c84c401c03044800c050021f11103500c0355a0b05403003d402c014003501c110310609100001603500d0f4502640a40d01070083c1081504203401032205031181c1c0340b05103060040c0100e6008018061804591401388a810707180000b84d50203400c0d0000020381c0d80003910200740c4943c0300c81c0c03060301c441c240411103006000311820942e800000584940311803090b01c2201c91685030401810340722010f4054281140d251189103402d01c0c3d40060b45c104800d0708030b082000c50850b400c0c865960240308802d030100b207141c107004604840c1c0004040e001ca80b04c03840b074001c4040d400441c0f08140501c800010380a0020241d0352182d041d0500f2500402c09449100c800c0c456800144000d401c0202d400340c20401c05c2d00d100720740c290040005030080d500c000000c03603440c1c0e0b0810500010400a20140d04030b0390080001d0401404809446a40721300039600d111081d09101c03200304483c1083c5c103031142e0402014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 771660233 1250 771658983 771659011
    0x30a180c09020c0a0c170616080a02250303020c070b0f0d0902030307052b0806150c250501020105061504090b01110f01090c060c050312040c1503230c03 67
    0x69105804c0006070600146044030035040861510611504081601014411101190384d2245004a200f201c0121807010510384800700c3c407401401e40060800744e611130059201d510003250f56001071140c0150a0340000d0340415030070005141445000000c0117071220060804035080c000d80c1c0c00e0304c9848424110290f64082d150b045480c18415600201d03004420b542d400514010162401012141c180d28601c3e4001e103200e04031401240841c0c01500060300c041000d0f081241e4102c045c1d4811500581f440c4500c0c0b0140c00c0c010b2002c1101e0826581071300340d1807025403400002a00b07450004d0080380c450300800a0505520507020251030466602d4103003c03510045490041c1d50116a801320400c035070040140744030002e00150441e80c0c04510034a81600810769982c0211103090110100401c42c0d002000ba140208104060325500140103500141d00e00781c1c1e030a0346020783c0c039544c508040480c0d215481400015143c424030862401c203501144a2884d15801d000000d11005250010390f0b048 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 771661483 1250 771660233 771660247
    0x3020405011e3c0801030503070210090803070302010e061513090c120f030f080720070e0405070611030a08010b130b032404200318030f030a180c0902 66
    0x1281d04103000410740090124544112161007002902d4607a410079605240410b410041c03520072810b1358126900640550b041a109a082042402a00d4511000c010300d48001040e20202403006240b19886a000040e29001c001c22843c00e1040007808108504c001d540070450391b0312564442224121542000245802c075031400001e0390303859401081e00211740c1c1030040c1c01c0040c202c90070182d85000343c81d101c00d94854070004554445044800d031001605480d10210043c940650510b45c2400300c0f01682d000640f1184070b070041c1c80c0100d909841f5030303001d41002c020541d042800c078920700d21050091407a2a12412002e401c942042c420101071841c00180d8800c1c59205900344005803d0202500c1c0e605c0c204506038101c00b41d0030246040c0d641100c01d40100b800d1905120301100c10100700c640548002c0104100c000c980c1000703000741720708920418102010142403004100a4a040030348030b4490800003101c000702c2c0d07800c4180c0e0b500200800248008100c44500000031141c3d0f0030000343e03403070741 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 771662733 1250 771661483 771661487
    0x11203051603031b21110412020a0317040e010e0103020a150c020d151a030601120f0b090105182e0b04060b03070311030c030f060f0d0c06030c03020405011e 69
    0x92403030150840094260800c04e41c1d554001c8042c0b02101c5552007601445080004c500116141102d0040e0003031820802082440d0380700142501d1280010144a10704d80d403901d4450a41c00020310820b043d800004d0117220042c243d0556502420044074005001d40c190360201d44041024085c0b2000c2c1070140080f02c00881c0700c0d086450100f40d02501c0601c00545500d440c00380000703096810045207013084902c01040b40d001405078842c590090082c03940741d01e0300003800b04403100c0000550b5819070500007100440e003030081c010700442446000040a1038041101150034582c3c0d0125440f42d041000104c154401d5100c0c00c04d6411594003003241e290001c08407501c01000c0700c884080e00141031010001c1c50f610041c014501c600010f88051048905000120005100845500c1d070404014804550001030000c9042c1e4800c1010b4030310a00b00000e4800100f181d100114100c072455240c203410f10041e9454011007032101650f0a06508240c2014006030282c0612840300c41c61031000b0300c810f01c20364 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 771663983 1250 771662733 771662741
    0x51905030a200f06070905010513090209010509060c06060102070b030c09011404180b0a050105040815190f020d0c0801080a15060e16140715020306030106080709021201120305160303 80
    0x1140e490116040340340f010720311a88445046428002152500f04002a15400341048450400440180040c0c49041c161420029001004007504001302405a50000c0d102e0710000d10140703402c0c000404040c0b0b4420002443c2c411903800138040d00c401842480000000181903e44400c3c037400d054803c3e559400401e21079000701c0d4050b400e1403804210850080c5e91661080003402c0040c0d501c0031a05844a005681c0b40c800c42c40762024507440038049a2000070350142d51750b0042a50441d9800c0021000340642c141d9071240e010b82c5001fa4001110411320b40c9030311581d080c51106040c030240310761411355126104ca01c04ca001500034030041c40100c000032450751003140508001900410706052544d500c0020f18416044c3d030300850f04e50310584214130500303026603032055403000c80c100d071800c0808040006500040c00e229059034803404045010981030103043d000e80f011440050307d40045500e000307510181a44071201442424802002003903009084032940322203400e604292104902d0124000c4c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 771665233 1250 771663983 771664037
    0x7020f03101401150906110f070b12060a03120c081902010903180311010c060f050a0b210a0b040318060804170c0d030f020f07080304051905030a 64
    0x6000310509110326407440c2e80a04950924601040364030303030301c800c0c4144051482e10300c068040b6107484010080540308288480c1d0102d0910160382c2c0c440c0f00c840380c2c80d01e04100c039041007a8210020a202d66901c20503400d0b40d9110004680150030740d131031611401104641400f040082040803e22141405034001c21251070403140d42c0c41109103481c0c010001d000b00020f00d02200040e0f08081041000c60509a801060343c2d00071032201002c140d014015506840540030480c0d030325856608181900c802449141c0c851341d000c80c0c01040e42940030b810840c1c180c40c0c8950f9811000b4600c108048550302c009225100154001c01d00345581e20740b41800c0e06d503a06880c800c034404d04801403002c58400d90004200703010b144103144241404501744000e48850217080b624402a078480d42c4418481c500c40d404c0a5001480d00034010315005040b1501c29247c0e2164800380e44420002060004022081100c002c2005d00380c00800052302c00b0b503907110b8980c4280003a0200300078201c20301103220f00d2410500090 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 771666483 1250 771665233 771665239
    0x5030703050c0a17091905060610140405040c090306020c0601090b0d08040312030b03030d0608010c050c06060f130c2001020f04090f1b1107060306060e04020c030d0513060c050406120207020f 84
    0x100c98414035002d0303550001114014083e2ba154405043c60b9801401024510040000031505042c140402d010080c41d4503403525042001c0c10310000b002c81d00380d100901140c030341503001e01915810103060000ba29039400c0c00760300404880001c440440d840500f07440c1565841141040a1001178800b00c02034220080c4641d41800005030841c04a4002c0d4410012201500b0081c4218482494281d41c540600c1480307010303581192000841501e425800707800700c464000c1412628074002030002c000c9070b48010b800390105a020101414001842550450081da0480250b1524428206c0d40b02a4040c510a40121a0f140c4403a49560042d98000d07885600140e00c1d461f4030420160310040c1485051301242100b401503d2021441c00c1c4240920804d0301e500e500c9030040c2c07481400c1408001c0d804509140810f0200344040401c1c2e5a6500030340b40510706903100f01000000c1420484211181d451901e401d000c0d08100070042d040c0c1002043c1d00400410380010b803292a24004540c4007402941c4083d8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 771667733 1250 771666483 771666523
    0xc131e03050706180f030804031115130501080906070f0804080706020f0405011d0a180603051b030706210c210f0c0806031b03190305030703050c0a1709 67
    0x40c601da0004101800180004e150340d14195241c0703032038982c0380f201d010103420b1400802050000c04c03413190650402e114080d01c254000c80c2c580c3e000c451260440d80800c045489094401c004540c0e103e07400580103440d81002d4210750801250282019a1818503101845400c070009414401d514041e501c50680240d0295940e4000e0007000d29141d000d8000e00b8045051141111038150410030441409034000d4012071a036400e01c008481f0070480c0102e0000d1744c90b110040400051000d00c80108a070100584480c90400c51a04043c00c214068000e007041000c0303000641c1005a107481c55000340425800009003108800108848104156806100d100e81030700e20503102c000d05030f012125842ca1282e0411425503014000c403802c1c1d0050b24007a0381030b807064003260f40da90115507606500c55001021100341c1c8101418514240d0301c0d05c03c055020600200400c012541c042c0505070740032030100c14181c0f511140c0400038002c6440009030758940070040340010420103040280907101c04410054803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 771668983 1250 771667733 771667739
    0xc0103360b100f09091a130804080304060e0d121808010212010f050f011211120406140109050f190e010204090b040c030b1e01171501080c131e030507 66
    0x240d158030701d03031103001d000f200072500005098889100d80703580b081c0d01100110100d101c5103041a0201406880a5508407503003070860001508071000300b00406100001c0c40c6c80b03d16051004d001c7d4040800c28a009180c440020310028102c040d0502d0041c45505280b0108042603134080b15040ca20380101c203140d03100068100303070b0b090b9401c0030604a0b0300c04a00e801038a51118280701044801e507101e07d02003252151520400b042603003190400a54107444a8105020340000850402e42038500b60b42c05640c8100a180c041d90440b00030340035004098060115041c18072100c01c1c002001000135000800300d444c4814240610303040000040003d000a5444070b0300c0e9005100203180c03000005100700e1030403611000d030901a00440d04600001003500229499029001c81e20b8810001014100305208520031400ca003031070001802000b080b1040c0c0070000034800050480040505001d04014040c004444040003040c10300d0207903030b038182041e014210711030490011050607410050030f42c041d0310408 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 771670233 1250 771668983 771669001
    0x702061602130c050a0324031b080a0b070c050a060c210605090c1b03070303020903061008190318060f1e0e0402090120010e0c0103360b 60
    0x100d22854001c545581508a004000e00d045450203da40700c081281441004c200d1800307a400071074044001c01d00304107528204a01003500c007805030000c4031503454507020840c1444000c01e01c40080e0888038010b12602c0d0242d154040b8890b0002c284204214207161590108038052202c00089079005c1d4050140b080d4030715018140c050301100d00d0203c0c1c1d000e00c805c000c0ca403c050180c082210f03405000c000581d1191100301250764030600490503052031012080300307039172010001482c0c41ca000390303030068a445c0340408050520001804100c1001343d2084144118200400c5000447d01e01d01200c1803174a01e5071030290740c03610441a82d80841d6442280c001886604604c583c00000c01030f940c0c1c00d45012510b2200d50344125285891000078001c0003080b01c0380d050503401044400d80504242440f0350f0340d428030000103119000e00e410265103035403180c41c001c5420032245040120034282400403000c0300d1803091007010201d102d5041c0e0800118000d22450f641082c00c04400c0d00310074182d80d545046400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 771671483 1250 771670233 771670267
    0x50c2701031a0a05010c0311030f1c0509150a06050619081e13150515010221030f1003021305010302031504031d130606020c040b040603081e070206 65
    0x1540401d0500c0ba0300d09490398042c100052034040282403801041c1854011900c403000036000b10180500007205501c00d590801c0a025130303c41e9101481e80d1694440d40000c0c844030031540180c0064201310501035a050b005c00d40480f4080e8540050805a441c1c0407068007800c0030350300ca00d4104900080e0b10041100100318452055410707296001030351034103600d020750300c0c82100210314000c1c00a0f01003000e42050003d4100c106000385c1910aa940d13804401d141201e01c2500c1c8148500c0c50340301810f40c01d580512000402c521901c0302841c0c81e24808020450520005064030983d143c150f000400b0b40705200b0307079200070f51b0300038180c14181c400110401004000c02e000985c421320607043c101c2420320507218a107124a60594a0104942d0300d01200c4032014001c0c070000c0d9000d10720520f070f607060310541d205501c0240380c1c690082811040355001e02c01125a4030440d503004509182d0203101060950003100c05190040034041d0745103550300640c0e40d09000d0507900075804000000c44010340d0b0030002c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 771672733 1250 771671483 771671557
    0x8030301140a03051c0504051806030f030c0316020d0b011d09030f0a050a030b1513080106060e1003271104090209150d05060117060a1e050c 62
    0x440c44080007480c6040081a40c40e40c84018140d5100c0380b8040c030b400101582d03810503030510b03060150503d915040007500d44d615620460710400505c000308800c915081180480318071805019524040740d200c01030b0740700d200e00d525454182d42654024006c54894524004100307410040c40c880035612010a144c481940074204c08030b40d106030780481c441d540c0c0407003107460880c44d81d0500c915240407880182c1c1c5a8002d2740c0c0c0c0100345565442d20f54110344586092884800a0050442c1d464501100c0c6045540c1c1680003c00c03280c1c5015424402d003500070b100f101b500312044130602401600000100c0280220003d4104c801080084241d204050018010b048a22034440000071406d09401d000840d03200704400303907010311404041002d0b07443c604600b1000810140c05102c1085445e00e50314034007002a0b00866035000583c00090300ca0109011181d08800c180e04207001c540f00c81c0007072240c503001800041d140d40d0355480108c2d112000540407502160303034608001e078800c58a8000401d02d102e0b010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 771673983 1250 771672733 771672749
    0x20092407051203090705090c0702130c030c1e050309070b0c1c03090215030a060e04050303100e100e131505090d090e18010e070e0601090902040303052b0608030301 72
    0x811204850000401c2d030b8851491140146002c51504007002001f40b0058a64002ca0300204125001760b1105144408183c10403040400e0a1003068002811600200040c174100720044000719050b1103000b00703d054980341440d046480340c407102070740c41c10190079911001c0084c20021300c080380a00040744a2508512008840d01c1c04020040207600f5501507200080d80a10a210031102503076010001d1030700080359100c0040c406499031b0841c44500b1003a0340070381d010362000c400c104c8442d003102d0100000d8540581200300a0522040050a01106008189032140d4a10016150000981c3c20440f010b81045801d000481002c840000410055a01200c54000c8110844d0043d005c5c0c1f4a1400301c8000d1800074456580398622b000c40816211400ea506540710f11012108260401c03551000d0910b848004200c1d041a1b000901400d809034403210805005104c2000030a40000503100b2158981c0c10000090200240000094003410700c801059490050003068804c40007000d0b505807280c003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 771675233 1250 771673983 771673993
    0x3031b0f18210303020906070f0c060c020d06180c120c08010e100203091002070b0a0501060807080f040f120e0a0801020f07080a0c12030b040f2009240705 68
    0x1081d40484620714012107401d40d072001d42c0082820209500c480c60309021345401414001c070440040e591347d00c5660207440300d0410b003c0c00c00c140b02c12001184001e00c01814408200309050b40801c000010681d000b4200d1541d171101215200384003c070303a08025038424103004403a0303203960310040398070864881520200c204034000706191078140301b03e4104000d0b03000207000c8104101042d40c041d42c00102000c0c0a801040700b00c1041c1000390014140301c51160b0030301c4540740317040d2400314201d0710141c0c00307034081000d428240044d00d41c06c915426082008001254070aa945081001507100d06410040c0007413090a041e2400c10343c89030888012032411078000400940d03405656080c3e0040c070449482c44041000b40100144540008104d50441414080680301c51511001c803d1081100700c03902182d20b90fa100341440c80c09115142c0004000c0b1000c12020541002141070411182c0c0010395458002a18000c281d950280b01f9241100200303604c84410504880a441c5402c2008103d4141c891 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 771676483 1250 771675233 771675257
    0x280b2701141c06170307030f05030609010b0f09090f10120b070809190503130b0315060a020f190506010608091f06030b0703200c10050403031b0f 64
    0x31807105614005146140305090103880e0b07007440407003812103002c0b08803103a80324000901900340d03000300c41040c041c2e940510f0300c440170340c05c010307201401c00d0070100c080040030010001980e440c003a078141901c10f0b034100c054440c00108010380707207032090a030790603404cc520f5800c024030b0317607400f03503541d44182c808400b444d2196607030304002a8010155900200810008000614064070403030200d40d02507581005c9030141c2540311030345640d003a1403560903142c5400020381424141052883c41c0000c0c401501900d1031032800152040498a04494481c440c0d0b1000a103074580e18820000082040103407026511401c1d40301c2000c0b440341000034002c94040c011f0000004815008007541031082400d000070f411000c0c41403c43e401000c1b0305100600c103007a41e485011010039412000d0500c0344000d5280000d071488552030015544129002086560714104007101c50301c0740118548605070340e181d40219450316103103402d4020300344030304d45200071842600d00000041c0d0301050380054600b142d10b6130044400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 771677733 1250 771676483 771676487
    0xf030a0c0f050411030a020a02281b060c020d022107091109060d1503060c020313050a05030a0201052107080a0c0c0c0b0a09180e0f03040302280b2701 66
    0x890f144400158000500006c1d03140c6c00190000d2890550a02c1520711602c40007408105503441c1841c100040c00d40c000c507090030846110000070f45580e1110b90b05c100c0900c0e02c0e8004200c0a09400001d01880d0014404021520760340060301c144410201e41c5003108075151003055030b68040f0b01c200342456007040004c800f160707aa8800c031210010041d09a5140507031650071840a000840d003125500c1d040714000001080c660710400e03e100c9150b50280d42c0e0f03082e03080c00e04246103840d07400103845181e020f0401c0282d41c0d0300090300884164282010ba4440c840307000c080c41c21140000748010381c10402001c0214003507100140138412555500c00304011200c950381158401512400109058031040b402e00c9249542c2001d0036941540307140241d040354850800c40d040082c445007220000d070f20783e40c20011850b410b0100c1c1d00121481d10045092601d0342d0001038403a240881c11076122030001c494403c6031004962900d010b01040d0f59003070758030341c0b0313441209100d0043c02c000300354141d03040c480c20b80c2d20f58 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 771678983 1250 771677733 771677741
    0x14070e06042d0e19020904080304051c03090203010b030c091503010b1002060601080a09170904150905060a08121b1207030e1507030c031b020a08060a14010b180f030a0c0f0504 77
    0x907802800c107018547d25503079000b06551003c0e100791001e124409a5045480c91004500d803000120380d230103d5407480310b10506007546c80d500b64081c440e410001c500a00e03500d4007002650304c21410006811002c4c40c82c00440c1c018100700110542102e03262a4040d481500041e400c1c0c000c0800baa100ca1403680c07030040702c80c200c41d01c8180061501450303a4000b01044001805008540401040054414040070741c030468520641e2000250340e03110030410820f8079058401d0801804410080d110b240001c48511041d481440e070702d0740040a80b010607103000c59042016901030f5060820b034035622a15401d01400c6869043c10a0b131040b0107620286402110203016100d415034192074030700100000c4d54003922403200360b400e4068500030360700c19031015958079503080b0001c1205038068001401c082042c0f00a0320082460004149160300c0100f1803901007904841c807802e0144240c0c10152144000605010240d032030a5515104000c0041c0520440344041d008071100441d0a401240c2d0310700a100683e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 771680233 1250 771678983 771679033
    0xf0c060807090609030201050304060b0d1407051002190f05120d0c1d04050c090a0f17030c0a0305090415090b04060504110405010e0d0602031314070e06042d0e 70
    0xe032a0f02c130100b0055002c0d03070140d07800900ca080045920f03503544000c0341c49001c080f2000d8400d107501010850080c482881758901600c01603c0c0340b02e2000452501941da51b201c1c81e0b00380e000301c840509010501001180d0a50030b258000181c5411003000f00d05208190402d6450b01c069619111082c51058060309030b11800c4120601460110f11103c01008010900144a6111030204002030f18140e0343d640381100140414680402001c2c5c14200c42484621090650100320303031040100c50030f0184005061950690b1501e0a02c2e521840d01d008500a040300300307080c0322180c807861804100b104007a0004200a07006440801c0501c3c0e5401c01c01084d40d0030b43c40655242e040030001400301d0b510544412206010240030270924410580e9504e0032603000315107614001000b20365200402017603280c421718803005000209000790401d4110207404001a011503c01c550740c0c1d40040c1003c02104003140000d440c2d1a55410782d11042c1c841c403018281d00f81ea481d6241c0200c1c003288007a81d602400c40164 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 771681483 1250 771680233 771680237
    0x30c0307020c0f011409030a170a08060913080f0904090b1801060f1205160b03061f05030106031d0105090c130501150e03070f0b1e0909040318030f0c0608070906 71
    0x440b00440e0702445d01544400c8215405001d00003544000c00c03041c0c46080c100341e085011040da22049410014000070002e40380340d00c00e020000c1802142808a012041c2c020780014003582c0e0340c0c1c01229588014414603001e103400c00c1c10074508000784000b00707940301c2c820101e1544000418080c13000e0320742216034a01a02107a4411480c0902800c004d07415100b100700e10410858450300c80c5e454480c400004c031548460482e00c000001c00009080c101c024014440001c4240d8009800c4108050414041401050304141d13440350300d41001800144c2c011101c42440c002000141821074200303468241085030980906031a08880000c0a05449494101c030000c5428502c070507002030003144c04c0d4030b00c4448194076104203180130924100b440b1401000f0410140748942c0d07440408418140340406101043e0307002c4042c0310100194480c154034a50042d0300d403405841e1621898040203003910540c0014003004224145901040440603102040d03a15984844000e41c1d110f000c111001c200074020040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 771682733 1250 771681483 771681497
    0x1b100c110d08060109030609050615010504030f0b0709030803070c050d110a080a030204170c0f041e090615060c0519080706091703190b060301060c0f1502030c0307020c0f01 76
    0xa0740c40e1094075043e030491014076103022619505e48948081c0c0d00b410f1025039040c0c0080050180d20015040300d006180820f0030040d0070140340d80c941c90203005407402c1c050010000d150002e154144191180c01c0a03503400800e480d2281407826005000580b500000c42d80c0344907201c0d01014090281c1f0802c448402d07810b004019404141d41c6809540d00140000320078107409200105d41207082000a0007000100d5000301002a21030040041c48030f095120b0f14012803415094103010640d84449811400d041800414101c0b0185012001044a580f0100b08480130030004a819a40101e00051290050b000c4a54141c0042c80500c010348050200500140342044524009007080d00702c00c045901913440b0080264183c2003980302648211103d4000740061080c55a1a0b1102e11420101a9058508034110340c18614054070380e000d002030203010750141c0b8000e54201b208950381d000e02c03403030000030a54490410983e030084540081c0c50002c09409505402e2545041003414582080016903e0318 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 771683983 1250 771682733 771682753
    0x10080d03110c0d11060c0301031101080601020a060e0102070b01051912150507050901021005070534210305060907082e06090501030207080a030b061b100c11 69
    0x5402014000600e0034070a10074008012000d000340002e64031280c01d40c0300e0910b4402000c00150a2030720007448404e201d0028801440418482c0304410038111003820401d48548842c0c0050b4a0072610301c200810590618240c00740300941034000d00050b0340b080c041d02ca040c0e603d4070100050101c120380911001d80250f20f0030815241680c4500d203520b409a800b0b070014603180203000341503400032980a03002c9140098000710035607042144001c03018003200b04000900b010000240644200b46d6819103503601ca94000190f001c0d0070302e1410380c00e001c158440d100010a03142c0400c02001b01d0b40c104141b00b02e0380b4548182a1300a000d06485600c0c002e124030b80543d112030041d00c1003580a445a1460803028082e504907800b1680340e98601c07220704584000c1c062910600400006030741d00301c281098014050703400000d23042025220014141d081c0401c0000b03113800414a140588214404201c56800700d06105501c04180104041d203410424045002207180c03d071006d4040d0304244683d640892207407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 771685233 1250 771683983 771683987
    0xf17040f080c30031e0c040b04151b05060718051809190c030f170a030b0406061d040c03020f0a020106051009080d11210d0510080d 58
    0x21110362489603040d10b05092108246038900714003590b15a115050080410507109100c00f14900c500303514980151640c40c0440e02c40b0052160250b85121000d00c40e404501c0074030401080d58090003038914056142c654a8000c4e22401d003141d01854081800c4000300e0456110b0505004201c94014004000c6034a800c0c60403254650b0700700003020800211100825580e0b1080c1d4000500e0842c0e1011030680d080601b002c034148000c01c14420400d550f0031603070a0001e800700040318201c90304070a0403e0321411a01304079080401c0d5068403c0c8507a0b001420540c1c064150784803d51070582940d0810132280c440c4029034400c2d1020020b60310320f00c6018100005454141c01104864080d40b5001d8240031009800105540013291a5000f50b5104d11040c0940e0901c0d20300e145403a01e05190044c0298940100d007510381c03113142010020080000806801c0359420001901b590310120802011401242c2211400d80c0010740009806410440403c0d2592300b01c2c0110307419100b8101c040c03c2500890f41c01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 771686483 1250 771685233 771685253
    0x3020d090b0411011718120d021b0607021b060415020a170f04051905040203010f080c1f12090507030b010620030904020a0201060506120402010206010b0c07170f06160f1704 76
    0x1074003800d1007403140301c0c61031f41c64820107040d00f00050303000035032914402e283c81070041040e080d4003212030b80301408001c51180d0000d0381e00050703544010000d03070f01c44020000c16803038071482d0001140030112461984407180d0000d03841c6601406a9080310100882c012130380458460000c14008c2d4103000d000900c40380ca0000584d810203601d500c2c03100718981e43d40d008170341681c0090f4070004e200780444004000c41d810500014207140400c6500c840c00710f90003406414044c800070881c104016a0038240c0030411b03465031000460b03581110403500c00035540e203031411048009000e400000b5090300a8072590264075000d003106134806501031401d007105441844002e400c0090f102c1d0866403100e800040ca0b03100c420007441d4030f1036041045201403906000282c900041a400311082900c10441d03907203010300124442040c1e5481e20040e2855002501c0220320b0801203c4a42e59540225028004151008040e100e03c0c0a6561942c1c18114110281a100303e900034020406200d5005c0000740041c410120f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 771687733 1250 771686483 771686521
    0x140c0306030a060e0c030706032c0f06010b0d0e0d090302130b0616330504030507080a0201060603150315020c121908181c03020d090b04110117 63
    0xc00c03a42c605009888050a50b443c078480e484107500a8940039004c0d082c1880300e00c1c064140c1e42002d000800a20031040501c03c401c4040c05803420003056440f541200c140940304001081000300c2e07460b940c5814100c006907120f448281c0aa81c5080b0400540e0300011402014280e1280c54014070203103940c0a00064507105001031400513a45d1686d210103a8035400a4126488001c800554011041c500340420102c81d40480e44d07182204841440c1e02c4544d081140c1240880c2d140c04211500c951034140e415029111004042030008500e4161180d4154082d0049030925902441003142c803485000c00849940400303032003c4040c03d80711700f84a60940080100080040450303403418506101c000c0540c10407944001e88143d07026046090a42c02408960860006000c540b22212038104055646000302d1000185003035548500300790724025410349980e220700c100117000383e428a241c0b08501d0042220100c0740418400d1280009501c1050501c1d510310f600d2080004030340704c0290b6140c09901e105 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 771688983 1250 771687733 771687739
    0x509031303030908010606020c090c16020a0914010b0426120703080406060801110928080f0111070b0402092a45120a0f120201140c0306 60
    0x8244804904006003000450007a501e2046030350900105a0a6403006d90041c030445d4031280c6141101c0da9402c85480d08a60504040360b03482e01100d41c01c0c00d860505440280d40702401140c0003509000350742194003030038240f000c450301581c4c03034515803442400390340241003400080e2030b1001ca20040d82c1c2c4e191098031304428211080324a0002d03202c42a030b40407101c1240050540d0b4107120820159004203409815004000c3c401507260305044911400382c228428450f240c0c0c00b03001100111180b4945170b1444404070507980190b29402000e564a100c1d00d184103a5619000002c170740042403000b940e0840d0f91100d0188200d407601c2c7c0800c01c0603200a0300c201c40c1d0b2003241510f2205010003070b04c03050600038407849441c0c98201d100000d0050341c803401c845a400b085502034400e180c980e2503080104002081c3c8010364101160804504042200390039000c03a803094821503000d2092031269205103d00c01ca0381d031541041e1100c0202c0c00c6c0c44046100d20050001000072071005407a603005154014806 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 771690233 1250 771688983 771688987
    0x1b0e2a0a030f063c0302030c060a030e060a020a0e0a050906040902010504171c0806100302030a1e150f0e04151b110607031a0d03030605030d030b010e1c06050903 71
    0x1441e044d0035004240d0881401015810b140c00e42c10702c030301148103041032000c80da04007001e4034680219031103c0240030070305d10402002852400c0180668805650101910100d40b00c5240c90303c4040c000f5441008000301203a02c06103458100c1c0341140ca01000d99001500c40603546e11103009102c0039201d4290103d0502c103060001050002000318403014a89860b07004051460a5140540450b03100401c0700007000480001c111140e15031120048904001c1c2c50010394a6844e08004001040b025003100c40401841004103074003003e9410003060514090481c0241560302d00807111020040d00c981c41c550400f180028022440c0a09001d41102d80e01030003003122030103445c3c41240081d00700c02c900d02103070301c2c0c88890900344010001d003644108207050800021100214044088500762407041c800c0248203102002c0500c603400c0304000740b1014080f5441850f0150021f406000b9803281140001c04c1c1221066252138500c034450034005080c103101e4080c0f0f040303417503040142030000e04480c082d20013 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 771691483 1250 771690233 771690239
    0x4140c1e1210020403150b011d030f0709050a1b090b0307090506030f090f160509090703020a081b01090b030406050423030c1614010c1b0e2a0a030f06 66
    0x800c0c0a2282c0440c042c110041c0d46604515041c00303028401c80c100b480c0a031402d4100181640c000000c070002881c0c4c1d1031885103000486001910303003222410803030b0450140200c0001e0101c59608010b00411140700d050000c00514004815240342060460b070018040c01000c00110051030011a0040040d1030030a494946410114001e540103a1704000c007040d22204008261a00307114103160001c000c03002d04150b0341810a22a4030700034901809101e00030302e0020800d50603042109100655001d00300d1582c1c9035441ca012030b111804444151b0b180c2c141517625500e19845004034906480c14001a2410b549994481400612008004030f460150300303107041d000c511900026425030001d400065690b80380c541102030400c00d01480d0b9030fa20000102d0140000c480b0a000c08000c02030070703e000d0001d80840d007406094039010210340800000c0252000c5015020100c3e0640305610a0b41c1114861955440389400702e0111010b1010424044c40b8041da014880e030011b610240c10a080845c0881d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 771692733 1250 771691483 771691519
    0x1020301060e1c03050d0b130c03020406020f0f1506040e0f03040801060b040e060f130f06060f0c0b220501050f040209100e0c160f030804140c1e 64
    0x20080e0095404107561461a00c1c041c0341081110702220b0410340034040c1400c0036070b4003810f140100f20410051548038a011b034016210382c005484548100003052100203c6d00001a00a40c072600581d0300500034504283c00d003200000700b000e2084503000042500c000451500c42d00d0040290045a00680380c9120400c041001c0112031038040c80000515551480c0030862804c45441e64800c04101c00e023440200f104003542c0c40c001d584a6000c1e03542104007110381c00042c0003054100050003076135280802005c05c2d290140d100c4010345005440d08950407500760010758004103d00001002e99820500007041c10b050014454080f040c52807030900c02d0411583d403203094510854200d0880c117282c604010540c0350030071070290800c4402d01d50034206401e0068031503020b40001d219400016000032815443d0f00c1c60701900040a070814200c0e0010302c428a401020507806441c155100c00401c44001c2c1c44000c0802c0b1001d44040090940e115070100128a4100c00303030304110f15500075099510420144 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 771693983 1250 771692733 771692737
    0x61713020d031701141509010c080c06010315050603100b0a08030c060a110a2a240f06080a0b090102130f1a040e0411030a3309020a0b0304140102 64
    0x24460344074030800f88104003c004481c0016481000785840c81044a4141c0d00c40c0f18201e8030440c001c0c40703003d40d140f1000300142c0342e41d0f14000000742241c000242c5c0e413105290108586040c2c03031181040544140c201400001568000d40380142d0540202c031000310b411584c0e510141300008c01a200038040c039950305e101811900071240c86420394008c0010050741c1a4503118800c1300700165800282020300c1702100030010a401240d801070301722031032011640d440385030303411070314043d84020208135000800e180814428010030021101c28103004030a041c01c032003401490140c6081100034030340311840b41c68000400901404031402075608000305d0682520900c2c5034000f504800440c2c0500510f1710601e00c1000c002400b21002501c401e2100340b2003241320b00c100e160001d030481031003100c0812201c002410032052500c000c00d2500446c4035001400780d450300580b240403402500b0a000303080340b0315210558080c054005e602c98881e038800d000c440c208602441d082400741920049148125070000e00720703 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 771695233 1250 771693983 771694009
    0x90a05091f06140303040b070308091c090e130b1302010c0602160203060a0e030a0f02100501030c1a0309070302060304140114040c090218040b0f13051803030106171302 74
    0x2003520b50006018890070a50b0881080106500451415150a041d500319010b4590000e0400415001250380da8108000c65218401e00041c00c085503c0040e0001c1d00354901441400131204100c030004061000c00100c0700c29840d000b892a0805964114443c140c4454044040f4103101003440d03400d000c1080c0c0e101a01e0f550512901c8500c142c1c4460040501d00f0000504ca008031900380030b54010f946101200780c0c1e20956103400c00403040d440e0f000042c3d00b04028601c0c2c080f0800e1500c030000003400b2031170503190103c0e41c1890748001c6240c80b0545500141c40101e070030101713a0303020300c10400040c00c14a00460b44603018907d082c0394070200220450a450102c0b0030040403000c217006101c2440f400710101030051050300811443c110030501043d048156220040c1d00c03480c0c0e40e1800b24019181c0350f2410386003020082694040007030700c090300780040000b5076103076403484501c3e01e02c0413100c007000007224160740c0162114101c00303c480004103400070000f131941c25014014400c0b4001038480394042100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 771696483 1250 771695233 771695293
    0x90b0309010911030a030207090b1201020a120c0e01020318220f05060d05060f0c1c0f1b0c11060d02041d0604110703030e030c060709090c020c090a0509 67
    0x10105403402c007040f103d1582c1e0b403124401d410001c0480006500095a041191050440450444c030a24009040d0000e110f00d12501940009501c2d140745900c040380010001400b2000c110a50000744211030340c000c00c0d002c1a026070f02c20042118502c0214944074103108000388141d0722411b0075014150308a001e12400107003070341c484910801c0f8081ca03000c4c0641c0400142d4030141040016141d4a40c2e841018040386040e0700408041841000b01804540c249180d40340705031800c420411180380281021010132001030701d00f08a160101c101032076046040700c0340e5940c401030020b01d600c8080c40e18004001c0c480c0d025404000900710142980081c10081004418008048803030b00c1a03407454420080c0450700c51460030b0507826a2406d4403003036420954042c500026a10201c0c00b034246188600031503800f00b480b0321010040119404030180080d240502d105002c1260290400d0380d030342c801c06483c0d03940302d2130720303000202c4034040d66021750340c00781191080755140004030b604001ca40452002c9650 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 771697733 1250 771696483 771696491
    0x2007170c011509060501030506061219051008061303050f0d0212010b04030212070503030d0f0b1f11010c1d0d0f060f0e1203040f0201020a0b10061106090a03030b01090b030901 77
    0x505103d9220300d070010b10083c01c042c0183e20740303c8000b41c21445105900a41000d8820210343d00c8814078901c050305e1204240c0802c074905002c04424205041486010714034818040012419035070840e84200e0b15034544c5480b824800007210401440c2c01ca2541c00d000d00d6803d01850300d44a0410034094001c0c4a0a45c82e5542d8a0030341c01440f100055403007540380396901005003009141c800104889004130000d0000540d00300182d150f4000c3c0200d0260150301000c003020068034030000059601e80641d40c0e80b2550710034141e84e071401e403d03604001d0750b02011400d048003803500d07101c0064910541342c000811310000b0056941c1c82104078191b400c41910070f40d1f998074406003c4501c0d441b50a00e440c0b219401010070704401c0003014014800203100801070301a0701c26180841e4020002c02c891550300c000c80c0200c6107001c41c0404040141841124002a022241b00c1c80141000c1502400303441d001c00a02292050740d00c040d00074000700303050941007011500c0002440421100510301a4503418008a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 771698983 1250 771697733 771697739
    0x60c0503070b070806121c0e0a0e0a0501170a2402040306050a1a0a030b0c070203031e071e03020307060c0e0301062d060c0b0a0603021201050405012007170c0115 71
    0x108020f48110581c011f0ba001c07030310413000251502020b8004081500d403007001401450042100111680e0000c4060f01c40ca0041c401480d44a0f08014140c0e003032080f0010f02c0030444510039980b0f801c6d0308000f80088401c1d0700d8009603a4940112010780c1406020090305c2e25a0306c2d643d074802c840c000c07100d102100740d03030b80f08000711300703a019030000c002c00402c0340d0500304a4107585072640d8050000d010000000c40024040d0110340381802640d413825907184100360329000402c0c48181c10780c0311280c101ea83c201c07260070540a440e400a07071075060607010342c020b505003401030781e518004291018296041c0b1840d032600700744d81d40d000d0040c02d016200805030340c0804091103203034010701500101000303100380b03c24105008451348040c00021660b0040e03920021a16015042c0700240415000690080c1d4a0314400501110541105010b984200001c1150246292000a03201141d21105000907410400240802d40200000941d00302c203e0307816145c8186081c0a80c21207043d895603000341c001d41d10b010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 771700233 1250 771698983 771698989
    0x30e0307080106061205060a0305070e01090524090718060e040f06060c0201050a0e030102030109020306030c0a05030c040207052b02150103030c031101021c0609060501021204060c0503070b070806 86
    0x18000e1554a009210f0141090000350171060700915106413640d40c0c10000e0005d0703984c0f070340b03007001150440f047d900b009464510000210000740581d42149081c8404200b4074032480355603603070403021010820a900903e000f0030204141c060142c0f800c0094a55582152401c200c042500624154541c041c0001d50141072205880d40c010b05c104140c2e1418400308220340d00300c40072051a542c2464800d5540c40300903415201607600191540d007540c800307c0041101e00b500c0d4000d40c018030040f01250303900c1300c513101040240d00650140940640116108012034105034002c0c00c0c40364820001e54400382142c8408901300b0a100c2c2c848100b0b07040c24203581141d10703014450800d0740140c07418150340e5581551000f07452202c10080003020032051075002d0203020001c0d41035412005007160785500d003c0c143d14400020317100d507010b4000d94030302d0301c04001072540c00003489400c1d0500010718503041030b00d0502e05980c1041555819505804100310310b8001841c40c0c2c0c0860701c940442e4407031903083d08040081c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 771701483 1250 771700233 771700243
    0x40b07030f110d0c0804021c020d06111c0c020c090a0906090515220308071b0c05040c051608371b0503030406270602070b061f0c1a0103030e03 63
    0x180b800384140403080c040540c2381e01c011104c26000f20080402d603030320a480400c066088582d0050110342c64286072540401030fa20003402e40d000c00c284101040ea500c0c100f500d088500020070f075405a444032140b000c2c00e0900e0b039207865010340a040000b8880d980c68440c101602c075140c0f0100d8903908000b10004030013604110450300f0001c00d01c0031444260101c0d07240e11a03074454840c0501408100c0e0001441540700304240780d130500c80700702d243c60301e00742078038126146800c6402818411404d010750103440c3d40c4114203131441800302200e00011a0010303226100140d00441030a85a9a0004446103112240b40300c2c5101504c200340322a00c2807407902c40028119110803000a05008410780341c07402080001054a4004c1d41103000020783c81140c58128010700e07020013a000a000750f25481c0710a20817580e0140003401d0040c5034040c519035440c000c1024250341d035466000341e0001601c107030180a05c07507a8841045881462040da442c106000c1a00e403544090f0b1080b00001c110710420907080c02c0a0007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 771702733 1250 771701483 771701501
    0xf10120e070e0a020310091e110a0219060f050f0f060616140a050d09030b0f070512040c050a1719050601050f01120906050601090f050306040b07030f110d 68
    0x81d06019091102009014002925101c00343d600440401c0c0c05d04102c050040050003250820040a0f8500c0380c0342035401c41c20740c8a904182d1074410900400c200c0c2c4070403138248442c680d001d0444002c0700105005140c180d004c0a481c40ba40d29298090340c0d61040c850340d0301810207031610515518200680780340e40b42c802088140101000d12001043d4150301d800c812403154000609220001840002c030300e80070b0446800f41c140d102e1990712a001d982c104948102b981c9c05140e60794659985d064515144210940e460400108100200000c985c070060107550018407407003644180310364500c000751281600350010b0b401c502c8480146445503100300495411200b04e10034194100c46a529029202c500501c41d0707500a405d00d0fa05200c02ea0300c115000300c4601c4071180f00b00301919003410000e0007000220f40d00c5010514004000c100705290020300d1007120350007001001c46941e655580d903440c89025080c1d9007450b4a440ca01c0010700d441e03004900051328100c0741035440740001564030064443c001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 771703983 1250 771702733 771702761
    0x50c0702130902240702030706030b04060f1d071b050d0908150a0b031207081e070f20060c06160512060607050c0307060807080c120a09020f1012 64
    0x901c0b5140141c440d4200061162000003140c5008100d83c00c1000a9120310301000390302d4001c0341e0004c030788a50035a21010003000152003c0104540b81c070304080e4240c0e01409194503000410295903401c400c0310865680c40718091a00e119610701c00c001c0c244840041050840e0941c02445c0001140707540100b07948000c0100b0001070904502500041b8006600a041c2d0002c0310346402414025403810804035400002c403408803943d842c2e5074204000c140e041480001606070506a510442c00d080340107565521747c201c091920400c3d03559441802004090201486010000c0d091354050340c2e0f01c0019001027410340d07026108500c2c0c5003050190400d459a003a0080c000b0501c11000e50510592900b40c1c007000031703600d0958610490030a0341c0b0788943e086030180c0c10310031503801148013580242001d0281005d921402c0250701e030301e02e0900c661f01854171452014003403c0001000c01c140c5c0c2c1c205500303071030019010350541c0c4c407410041588032940c24074001c0171800323943e00413910700d05a12408000b0310315a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 771705233 1250 771703983 771703991
    0x30f070e060304111f05030f0903030108060c0a09030210111c0f0c0f0c080f0705030a11010315080319120e061914070807180609060f020709050c070213 67
    0x120300092154000070b000a000c42c2e40007116a02c0a031a10b030301010003002c80084000a90301d850900600c03d030300444003e800070441c00082a982c4400206482c141c031440400780000d5075402500c5139803070300155078250401012500010160305e0764045440e42d40343d9652540d40c501840340866261004001080050807001e2507501c1e00c0c242e00100803011600985400a41614507080c014101002c1540260810030000000100c1d20300001303c0c1200c0944542c16140c2c0d584c1d071039041648600b002003006d070501c844015804940d40c400d030b010030030f103203416640c141c022510f0f013046603d1a0807901542c400c402d00b9208040950360414410b03030800c05420b0050100641c07002259880d00005032201d05212104403580c0036022041e0894005548083d880c000186008a0004c04020040c2c512401151102021051a8122111a600b030700c456448050340185013001c119911a1a4a1f01c80210f024130340740458464110b001c0e0a00504454407403548070302c030500412034040c00c0002501040703458 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 771706483 1250 771705233 771705257
    0x60e06030f0d210f0617060c04031a182d0606030a0803060d150f110c06010605160615052805060307031103040303060906050f091f1a030f07 62
    0x1108041c03074038803d4a0800358441d01c009042e58400342c115070400b803030011304010f00030503a94686603846001410140031075215032a201b504442da031045000240002c40e12400c3d00d41e0100b034080d0240d81100071403405030041d03051782c00000e0815402c1d40b42d000b4494030707038004014214104044134014490302e502030616402c00000080d910620f0321002020103030007200080f49540d80307910100083e900a14a02d5030300c0c05404403400206001920b0010640c9480f00803040a40030405a0f5000500700e401081c0503420481c05844580007108901800c07085848400700241050203603140700128507132601302c214240000c020510860b0b050842c20200131100c500100a000103441c02110415522a55a6290744d03c044016040e10511114641400014082010360651019040782c2442d80708011854460080150110002641035480030015020507109091058241462000e52108541003075603a106619100c002514120300c0c680044208400211160307101588091a403803c1035500340c1c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 771707733 1250 771706483 771706487
    0x60a09151205010f0b1c091b08070f1d06060d15050f030d0507110f0916110309060933041a0313080a1701090e010b030c010c030c060f060e06030f0d 65
    0x404500410746c80003032040c1c80c86a8207076401103420f160000f080100019040809410150b0144211181c1303100e01c400000302202058894070681c0c4178040da8404000030044210300f4110064021580413070108050a00103201d0311500303204582003006812483d140c54200703c5181c55090a0a0283d00000084000c49501508981003587c4c8035004490740b117940c0010510020561884a1300100d1001c01c0c002c0714041c0f10901041d460a40c0e480e454124240c0034580c1e200d002d0f5032451900248180b103501040e190004941400400c0f15110040c40740c80e0199018410407056405200140300090a00c00c000340c20746038072503100080c4030300d81c0b8608100b0050040000c11f2a4081e16246c004200700842c0f510441083d10302059441a036507080d61244030700c03c028401991804200d629145907400f0505021442259a1105841d6031403a8000d03510103aa94000c0c494080b5109a51100900d1914407988142d1001d88180120384031179103020001d0502d42a6850700780007880d0310041681c82c0303482d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 771708983 1250 771707733 771707737
    0x100b0f0a0303170411040507050306091303020d0e0102100c080f010f0e0a0b040e061005031504080a0c1a040516121115371409060a09151205010f0b 65
    0x2010418050f0345544608050780c4031401c229080e0780c07040c00e0805000c00706030300c40090b5010303036400c60704010542c6581159140e155103910005000d87c1142081d03005042c0650b044440028042c01a219030082c2c2610850807540020460f401081d5214244440800030b503440d680946954142044001c0c00c040d43c1e42500c03400203000c0b82c07201d038507400c014080e07403140e400140301c1c81d089108640c00b80c2030101d140d0709003010a0043c680a0300c201c00154440d0007000707144901840e003180c41240740c400c0504003112a4200e840d401e94015101030001c000404030303031404501c540d004001400143c014880a124040016801f4002e0021414404404548203441c1c01d4a100011180341c250500005010b2045004a0000384800c41c01000300c2000500d2541c0ca001c2c2d001001400034803410cd036041c00b911018941045a110000140b06030122428103c006008205590904000145d9511800c80c10007604103c540d00050003800283c0c0c44030b03c0c074001c407070141c0740c41c0e05915109810030341284018 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 771710233 1250 771708983 771709007
    0x9060b160602090d06020c010501051e06030a090c030206070501020a031104032a090e070828031809020d0b0a0b0c0d03110f0705030c0c030a020a030204020d0e100b0f0a0303 76
    0xc581c0018120fa0756501c010710b4015070381d4850f006540350328000c00000e00070078091080a001d49900010f100060344400f0f1041040307540201001d00b151a04110540200784c100c004640e041c0c8905004405603407601c019041c0b4920900003d03940d40340b142c0c0c008013500e10741c405413404030000344014800034620840092440e140c8c00c4118400440390228111036040f640e00880c030240c90001070000c03042010807884c042d02c0c40002100e01250040c046d1640c8101c098000bc0c00100c2c01c41c0e0310400181c420f0702400d01030220486410b0441340c07641031010403a4050280c11003800e5a030700a28501c0e0404c0320f10b040c014101285018100308000783e040f0385a40c0040c0125003019135545448800c0007040080c1c501d80340141a075103855810920344607039258040c890203013a600c41d14200780958540090001910b550141030051668a140d09100c0603401981c04170701825268011040c056130100804404c4081c1c541c030110b400c1302000284440340b402559181d0041014840a00100750403840724510 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 771711483 1250 771710233 771710243
    0x605030c0d0b120a0c0b09032d19030e0103090c060c060603120203120f090d0e0103020c0d08060406230f0607080f070c12030c030e010311070c09060b16 67
    0x2844048540e0700700204520034240350301026031000c1c4507514100160181110f40706a00c50b180e40790321450558200d004441c2d603a98590301c40105804403c200c0c07226480305010030030004075102c400450140c2000c01031400f10840400c02c0d44114249544032403c142c6149080c02c1c00c0240301166200c001c004141d1340900c0c41401080442902005460b911202c001c0d81c00500703444046c201030000a481e944000c924150038512000850390340b41c11884198000d1114000038001500c0f10101600c41c140490038040c18513a00f03000f80d4002c0d0f0021f0141c2501c4040d1507444641e103142480801c0221040d1340c11900d403007001401071025400d00940c0d0b00320f154904451088604007160300142c19803017000c1004050050114840411030102005841000d200e8240041c80545401724078801150181018000449644103400468000d010b031261915042c540421849100e41d03842d40c1d940e00c41181240d1041e07000c401007000b030f01c0c0c41c8110310140580ea21054503016804e090a1801000d051010302 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 771712733 1250 771711483 771711487
    0x91306050c040f0308120610050406030b150307020706022401030206070c0f09271a0c0c01060b03091b03060c25051b0402091c1106160c050a0605030c 66
    0x8074951448140e0700144182402c1141d482e45070710b440c5180d03800000c883d100c00c0580c1c0300401d81c5468400a1240300700620303075545060500d0520100c0c00313000800304040e00000c2d140103601810b450b07080203621950542d002007058602e084802460905001c400251000c3c01c00881941c034a0f0301080d4070b045a804036041c6440da02c0324280003812100390741c03040c0840c0d106124005040744041c6c0010121030f082c0704d81c0202d010031400196040c01c0c030f4a50003d0601d00320070900b5000350440120540c000803002041402d0244801006007140c189400c140ca00b402c0200402900400c100700c890104002151510f411180d8070020940e01c000c054101200c0c1030001c207550071502e0540c8200114010040d980243d240e09038140291115800c50464020307145804120040e4189402283e0503000c014054070202c8014440c070800da100005c4080300c800f8031001c104c1501d42c1c0d40b076014044103180c0c034000e1940e24400e4980160045455840a4060585164100649900071060320745c0180c08513000c88d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 771713983 1250 771712733 771712741
    0xb0f010305150d0c030512340b07031e0c091203020a1b03060c0801061407080c010518060907050102031b0a020d05030a0f03020c0c0105130f032009130605 68
    0x1440c0002c0803515150890000c070280c8050101e40039881003200d01800c01c0c0e801103a800c5040880502c01e0f01401001c80c0342d044420003190410803842c1c0d00344900b10480c0c10b400da21503643c5c0464400207aa64100007600c82d03c3e482402c9020300d118a1451200f040200000b4000d1b1074080c16100d140e118001c0d4024418145005141c000e00c6111880d643c4003d00300c5a001c50076060f185900201d01003510030364a07000000e10494056103c89040e22500e48401814040000b0325a10a51140108450680c004e02c5401480f802c24040c4030302a201e01c81c0030205400b2128405407800300e0060202c0d520740c3c4008820005a43c0102c01c941d00c0d000790392800d00041c6107401142d80360030b00d03107400250030011030903c0c1c0041c40400300c00f800c90009142c3d503d160103504848200d059024000c101d40c1180c001c85505106076000702e00400101001c106160036042c1d940400c0c0321909850ba0056943c6501b07a4070705c2c910b80c3e00034480720000320070445da440e086003400e440032100c0d6040214000c2226640e00041 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 771715233 1250 771713983 771714001
    0x301090c0f061b110622030303050702010e12160b18010b061204020f1203031f061110091703070c0203060601080c1602040b060703020f01050f04030f03051003290a0b0f010305 77
    0x1a460700f034100f14401c0c000b80b186c0b401c1e01c8640781c00e0310007580000c1c41e0030302040c1d40f41c0c03060041d52680010700c002401000780ba61115038031544032810141680d401240144001400310203954441e1005080c000000220000203500b95a0340c3c0700094440d4a00700401c001ca401960307070032500303d601030f030305001c040c0c0d2020301243c41c0c00500030f1019440c2c0301c04400c01c01640c01d5425408400514400300300c0300241d8585041d154800002c02c90400768104641840301c41d84503900c42503d5500494040e0340145c03d01c1e80c21904e40e8002e403000000941081794500c00c0d0f0504000403904440b0030318204920b458481c549074264002c41d91035480b203908003164401559160380002c00d035400020904d42c2d0340c41c22460080d42c1c07005044c039503405a50030480024100b0004080040c45960507854880c82e007480088c00b2001010020003907258106802404404076552042c46049500186210485150f0511025040f42001860b00c000300f41020340d151041d4031103806822145000b0300303000c200c0b40c4030002c130 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 771716483 1250 771715233 771715237
    0x209040f0203010806040312050702070515041707081209150d0b040501090204090e0102090f120106081903120908092b0605060a0603020f03240301090c0f061b1106 72
    0xc4002228004000810440804180b250007103120b62140001e400403e000402aa40112441c60243e04008801c000d00d00302200102c3c1084400c542c1103141a48802800e0f02105140c4450f00340703580700c40801e0001d00c5082000004c20180320003170030709004444001403c08403e1681c03419000d480883c42d044c81a03501c2d00500005000284148a91f40c0c4a4141c1c10003900688501281c0038186040da410740382d0181700f102e4103603401901c03000001d40d00d041800300a082c9030000808640d0f0350840000c50300c1007804456440780c1c414400750210301c100e04009001320441c001c0070302d1603403078500480c000910b00e00c111012a1030a40d5a1618070309015403083d1509042d01001d0340550796540d541c0104181580f116100312030455241e907160b510355104038100e0180d080c1c0c03e4884001000486c001148903000500441e0400c0c10415003100c60700301107421354440c00e000725503d40445c14140301042540e0ba400001c0c080768644604a100ad1414540882e03c410324040e01d496048014401d207502d42100b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 771717733 1250 771716483 771716501
    0x30905070603020a030c08010803090906032e06050f012f010213030308091501050609060d0c033216110706080a0b0a05090f0c090418170406050d020904 67
    0x400c0e00e0845a5949010340079602200041002915016030051081e000d01e8080c3e040c2c0e40704ea4000d41c2012801410300014490140400e0381c540b0804000c01101f00800c000003a00c3d410107111401101441d43d0760000340c980b1900942d2142103410812040b45e40d0100030140d0b081c000030f090f80145a401c5003004200351079403503034032929400050000c021041102a10007103921940c0c07074050540d1590000d58444000e50969042e001500c0300412880c90500e01a10582a000b01803034a00140c442c092400c035007503040d104021a072911080d80d05260710a4405680f014241d00041103d601d006101c100280010400c0101061008044000521401486024140c48011034000588644015107120b10848440542d181403000b004014180f9041c60401c50b20081c250340416160080740c1040302070005c040101c03014050141e03035107594850243c0364916807400303103034050040c07030341464070350140540c007031a10040c0108410881107a100c4104c42c2030025282006840c3c0b000e403c009400392210390 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 771718983 1250 771717733 771717743
    0x4050d03020a12020723180a0515040b0f0607170a02030c10061d281a0d05031207020f01051008010b0102210702120a060e121312030309 60
    0x402100406800045000c211402030000000b21800b49404a076100100c0c0220b04040d0651481854001c2c18a4001c00701c100006215003401d4070741045960098900300c901018481c0c940c42408818000d825083d8207148050320284414513011000c65030017000d00125030300030540000c0c51014410500700c6603802e040070b52001c50307980003240002940e03508495000c003d0350150b1000c40c52040300e00d10403802101c105000d200c42c0846052800c911a5500130f105400401030031183c4860240405003004001c1c407000c07000510b00c0000c0303800014611503224a58026103c8a00d07880c04100d0010035903104400245000445c0d03a101a030490901c030358010801c02642c01d0005004080229001d1842031381e00410081095680d10001242d44907210700000f01440d070b000103291024140400144403090001c2c01c021400c2184600b50351034500c0f0b011003560341682e2050701c00020b043c144401e40d600c2400340c0c0a0f070706212156810f41080f2803584900c030981004604000105130007608601800e903005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 771720233 1250 771718983 771718999
    0x904060305030703120608150a0212040525030b0c1308150f06060a080736060219080a0c060902060304060b030d05071115251104020f0a030504080405 66
    0x80c900320703a0b241c00040d000c80204020002d1180b8482207442214121445080101010009000002010074002d010345032202d400300f103000420f0540d041c05a0013140300304001d0070030030b8111100032051514503070680020b40a0440030004204070505103500302c00c11000e00e07543d64040d41816000720b0210760000159004102c41d62500059040d843da200f103208400e0b900c0b069407194204502803003800065404210084040750266116003846d000ca11175080c03041c1e100ca80312100303181828000c641c03102545100440d003840140e5040c480c034044a002040d0800c1800c1c01070f03542915038003c035210002001b0340c0090b41400c0c000c45800840c5070319009004a5624201410407001900e11000503600900c1101c005a49075480f03081120781c0e458009520201c5c4400031010401c0d103000c41981285245c01c01c2c05008078943c40d10307000841c041c0c000045100e1015451074203660016010220034861441408600008503055007290140c0c90036182c009000e6480d86003080c01070042ea040036030003800d2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 771721483 1250 771720233 771720239
    0x706020a0e100c020301052511070803040b0c3703090b04030501021201060e03070302011b021005131e1413020c0106030b0906010305121b01050a0c0e010804020105031b090406 77
    0x450f009460751070082d0001d01c034540d00d0080200485400400d0b03005038030440e43c07500440d130780300303180070040030740002c1c286d80105540d00361807451600a9005803060800000c0c00d0210040c0c100800e10700f1545c00c503c105c54001c180e0002c0d0100580f40d212030341c1d480c050b843d900320425220740c80c11405440300038052526191039040c100d0007500020703142c0300b20039607003000450360501410007d21703c0e40d0004d0003040402e0569004407032078008890307010103052040c541100103030742c2e0803403c10b40050035a45032070300c6680400c1008140b0f0025800140d203000d00c24a0300f440d00f14601c0c0710740f040d6400880c5e2480d94219000100b845005903030071909080b4800b0451075010401908001d040381e00603030131072040ea111190b009031030314420300c0300400551100c09080140384008000d01101e002078035200f244040c601d168107081d1001184d10788000d95940d500d0a5034160070003c42c007009202881d0985c028507140d40040c1c814071010304142401003010380090765030300c544005c8178007843c0054000c0c058199 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 771722733 1250 771721483 771721487
    0x506030c0703020c0103051902070f0602161a24010c06110d0b0103020f0a0f050c030a03062c07031107080d061d0c0702060a0302250203010f020f0706020a0e10 70
    0x81d0304074014000c0481c0c6145540c800c1c005c80707000f40c1c400c1d00c00006001304582d41e00c00940c00500200d415010740405035011400c0c500c090200c9810346500421094414a000100c0321901c05440c130b00c011409051000d0410406200c07004100044c01100200c00050016960740142c0c050091440782072035803074082d440017400070745500d440400003440b0301c80f00140107405a0090401c00e5501450502070745c0943d510a000084101e0715904005190180110445003581e0292518034082a141c1c401080103615414040f0805880c950807000201c2c00351200c140c14803030240480d400c154a442170444c0001400080380c0b001588405074aa0700d0640c44202030151107030b4800d422035034032000036610015001c065404e100340c00c1102c0492030301c220b80d82000b4054200385240410107500340902119403408214244032410b0451403400b440c1c501703104041c00d4980490300303d82e04900500020312909420001d44040991040c2c1c096114140004200c900c3e290000d001640070009100d13100e1f88076 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 771723983 1250 771722733 771722737
    0x705070813170a030305070905011b0204060509040b042f0f0307120507051207050102250e09010f1b020d0e13050106090603060e1b2d1206120c0907090506030c 70
    0x940710361806d00095840c80e42c192421800c40c81b440e03020070084c1a82c55660072aaa03000c200144c80144001090f58840d000306941a2003120100c0c1c0d0303411780784103020502a4050a41e0b250f91926004410f001c40d00c030040d007400c1c540141071540116121920300f000d139503090041c0f00280c643d004042518903480c1c00c0081d03651080d4442c3e0340c010f46180fa1000517040010030303031030103071001a00284102c9100a08101c0c0b00701e59250050684070800c00b0100b20204842a80c6014503e003100100c1c02125100004088810342e1003807800301c0808030070740302e002030300491310b80d0703400105091680158500c6004030304d070b108240c0c0c0d54501b00f9150400125905070000d03420825900190740400c107080e01e804c4103075003000c2c082e20035031600c01c19655034520080000303005240400c0d1845008640b244403000c60304148070cc003121000414008201e6622150030306440c035a20220454a480c011085160b416482d5560b15841c50300401800002455850041c24030f00014100504919500d1070b110943c07894607 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 771725233 1250 771723983 771724003
    0x603081c051e04150204050604090605090a140601050a0e040203040609031101061d1f032009060a05040c1106010b030609010803030f0a0c09030501230906070507081317 74
    0x414500030200d05408886840c0b0390380300ea482070290305a5101c82c0c81d943c034101d0041400c03c4400740c003040085001d403901e1010344014904000f010605070300308420416200301c01800d0100380313442c0500c80655816030102c0d440d0000020300b41207036114101c100c100c1d01c07202036103c000d80060000003800200549a408088118020f40c0c6055442c11102001426100e0f917114a4010040c20b4071501c244083c030004058004803c80300741c1c41101d590f11450026011564401e59402104046072003440882510307151015004407031010319450010000b50b2660510701405009560324009c0301e200c00c2c0034410710702c08190890704881d5990313500c40e0210001d034000c07a040d074080d280c4480006082d030360003c00e80340100804249020213540301c00c3c0c00001800d20502c00c204020a940d40000801c0017031040c84400c0f143c40d400e13807180034002c00b54080b54400141207261554800e1041100345507100054a50482c4d00121940d52050440107807001d00ea89900b043c0b090712100d20710300522000000e050718007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 771726483 1250 771725233 771725287
    0x5370f03030c08040c030b06010e041d0d02030c030f0f0f1b1209030d0c170d15080f0601120804090f020309070e070203070201121416020c060301032103060308 70
    0x85400503140860b89524142c50050894040960620020301c191450591041043c9803201c00f4102b42d034001815a51112903902600c40c0035003a0860100050100c20f05070811400158030b0080d00b42d19072070740da1180101d0146458000b09601c0c144142600464241c07000c050051074884845c1c0d0f8524114500e0004069141e200d556105651803403144107a40385400300402401d00720403988025950a0075604007101c0e282a0f1511284030a01450301804840c0c40b080d000064660b541c0c501c4004c0c0c444c15401644899000b00034400e40c08800080c00c1c2d05640780c410b60b07402025090b280400b6a1b00079a04982c0c003450421070145080505036001d903100d211900c040301d940980c1c03508001c1e64014140c66070303001a0010004075000d94060315903410482c101d100300284010700010354500c800d20a54404a003000310b80320481c00d490341048411400882107031202c1c07070b40d403555944003408a1012040720010050b0300c0701c5040613001c3d601c120015500110b42d2a80e614035500441c15034001100f0000f2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 771727733 1250 771726483 771726491
    0x50d090507030524040c06050307120f091a0c0405060d020f0a0c031d03060114131122050a1502030702030d080603010f110901081305031c1805370f0303 67
    0x83c2e000c4030030136503d00558020010700c484906200b01140e0b2503100924800500011201301d4424810301e220704c00c0c44680410001800e0582454255040071120410003c0b4069800c28007031441500002c44049070021601560380b9141c820250029004e5602d50344049580032a403411041e0700560440001d61003031341c1b644440ca1450310302c4400b0310b03881580350b60568801c02c0140102e282c00c00c042d60031060700911842c00140b0f01c00c511010364100d504120714603100442c40e02c80271440d600d0b01c95007903440c00b1203001580d030404000c40d800c030000e44a81546594540f0320314921a0007841107404180d00581505c0ca03200c40c05401510011042d149140a586000d00c0101407184500c034a104e03645210003014681002080115560321005c1c201e40c00d00b040103903004001401c1040140f524032003100e17501d03030308034903030000003040760010807040c0d10300c81a40004400003000890032680e408212003100108900161a43e01d070346103480c0e51908945035035a19001480695540b14506270310a5030180 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 771728983 1250 771727733 771727783
    0x120e0304090608150a0c050f0f0c0d08070c030f051c1a030d020601050402250b0907050108132a120606060528020a022824050d0905070305 61
    0x65518041d468820390420031100100b41050b5140e001b0556540d0301c0e25020b030400000d0043c0200d10f600651111007400000034441c1025003060051030515941c030b05050030a07103845134020303084521103000201080b44461030b0059641c040c1c02924038503042540d664040704008245d100c0144480d4200001280542d4018001c0d03280009201060002a901810741d603444d040602001e50032030030f105941020b0107241c01c042005503420034803a15000d6100c040003800c224a17500e043c00c0154110504111611040103a00d40c40c1c8910007040c65030010a03156001070304031017800d007418054010300540b24440400201c18214841091115009100402c00c2c4ca940702020b444901ca00e00c45140e16500c1455800411016115070f00c4000a00740160307070340c2030307241c1d40022250030340e0b42c4151031910314104035001014011480700019005094000134450203001d0702c3d800c0040060400020007500180f04800b400c3d06c2d030001900d20f60f021045070103507600c0780351164a802007640c1c40c420101c0c0b500000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 771730233 1250 771728983 771728999
    0x60a020a0e1c0605040b0a0f060302011d0a0f060203071407240201060b1c0b04060803160c031a041506060e060d200307020f0a021f120e03040906 64
    0x54545244640300c98190080d804184802c802d403403005810114405002c05010590500030340384a20300c999110b148515050003e1002c69000070440119a0720700501840182d0b0040004030f40e0144110011000082d8880094010002a00001c03090145035900007005600007005d0301d10b8a12855006501000c0f40f1481540d50b0006e1181c8240c000e51101c5050207000e400c0c0d80c1c915201c24510002c1201a101c2407040c040c0e40c4401d2604940f284440503c902111036403149140d081c00451307040c03200310718203c0320959070700411101143d040d01c000c03100c2007040781c501c018000540d846401207900084d002407030841580c04403001e40e015034404d0005000600b19115180580f8459124a1000022074003802080d810401b0f030092001d5495211244a01d954410300014004000016940b0728000f40020b0411985d03070010760007076000d80d062100696491250b05000e00143c18400c00580841c02c04460300030f200ca00164445241c80389400e800302000c0001c01c2030f14480e0105003c0b00d41d481e040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 771731483 1250 771730233 771730237
    0x9030806180426131203110313032003150f131713120615060c020f040203090102041d2703030708280204030b070504030b1614070b0603060a02 63
    0x100030200e0f082c0d084a00310a0810305040314000110036801c0e030034092039a0340b60401c14100d402041103440b020407044101a44455911054810b140140d0b06144501e46c132004041ca4900000f0000d12440108041e80c1304610b24036482d2000042c201ca015030038484001100f0002a02c403044201417900c00580e00302c10794068560300315405580010501e4240d2082c115a4110300c1032884e22203568070001070180005004100c0d4203005040018030342a9505140070b480d44181d108000b40301c56a440320025981d900000d10b0622004d84015076203640d4040c1c1e280c020f1085412202241215000455560028034085846441e0900402c03503a144055041216030042100c10900365100304001a051032180b00041d0f003213180070200f800d02100d020b01c0601541151011000c0342580818204148061f40b81e6440e0854280d0030a20f280038103580700c0900400c001001212034280f240640d048041c0304150b00241c550300515000c0c1c58441502d802110800117590542c402e100e41d5010801d56112882 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 771732733 1250 771731483 771731491
    0x10f03030504151b051510050a03030c080d151703091c060b0913061410060f0509130b0102010c030b01021908041208030702070f030b06010302070809040903080618 72
    0x48160a0510300145482c402d2443c074060000c0000401c062001400c0301410040241c0c0f18001411208084c20600018400c0007041464603074480c1d20700700545d4950b0302c458001c0c2c0341c141c83e041c0324860440c20003c40500c500c203050016240f800c1c0e08440e02015803000c020991710302c800382d49008416404166500c0c0500078039030380c0c00b07540010844504007c1c400341282c018481c0101081b643ca58000140034a9011180ca4105561201c0d40600b080694800c2007070007c88600000503a04241100c3c0101c0744a5000708404d012001500c665014058000e840c08080014200c4041450f078103405c03006030134001400c50143d801c04c0c1d01c1e410814000c0c041c0e00d400380b2042e0300070200c400c0ea90b103206140404001040e108030400308004654500c07074290250455005e40c070107540c0c908001c00000d15144096004140840a40506100140109100e00e800080900e4056152522414080c4a51164000081d481860302600008050704107010f948101c0f1b081761810071a01418504144452040f1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 771733983 1250 771732733 771732737
    0x6091d0105060f030a090b01180c0912020d03090b03070e010f023c15041a0108071e0801020c06100b070809040e0c0307031a010b070b1302150a17010f0303 68
    0x1100f5003074030b4144030b40955404a0b18950100d2a205503448036004d0704000c0e008052140d035812040380d030b5221b080c09205840c103100e24100640c2d610301488070028558040c0024480c014910380a801e0610514114018208036460700d0fa0340e082c400000707401082c468184178007048000881c1d40c0000d001040706500c0c502241800060340682203030102e01254291031240807899080800040408200301540441512100c0703682039050134101001c0d070040030b10070340c0014140240140410380d800300d004070440c4c1c40d002c04603074482d070740441c80305000d80d468110040540c408102c20088907400107405009440000d0802040e64a958900c14288208403010708803420420030b0b1036103800c1030381c00302c03110401901c1500c02c045520700000741000441c0e441641d2903080c11007491042131030f100c2000c2c0140060081146000003e0b030360000704450080c086107203840d1014034031040d07484900c1032500071181c02690700d65510740014040e04404201c0c0e030207022842b28034004240c001076000b170b03081074a07015 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 771735233 1250 771733983 771733987
    0x7030308150f0d02061306030204031e0f140c060f120705040f0b0c030d11040602010e0c010c03030b0d0b090d02060a020c0a120c0c14030d0c020a060f031506091d010506 74
    0xc209200000f0590a0102e0300850300b000040041c600c5182100081c041c150345c0582d82d540f450800071804000d0b03611140300b140601004800243c81d4625480030240d004007901640505259054100104030903040d0300303c4000107407100c008010000070910345504103500d801c00d4442d11400c41d2107005600035020306003241d4105100b84a180b034050143d5042000880b8038080c50814400c007030b603000341118550b550300400c0c18080190280142c1065980d00c000425401040100003002d00ca86840017400703066546502010320744982400062050300816254a103082c03e00c0d1269680e000d441c00304006005400200d04028070900032609901200c0e0000e05500d066500d0700c038201662000c0300030a0022800a443c0060f400c07010100c000c0030850740a0b2000c2c0049814075050440221071710701000a2450401c00503652022050306480380c92030910b03580f00f01c3c100d082d0001c10100c80c00c440660048040010307100c4d40450000180e411000180504000340c0183d008c580c042030195540c00101 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 771736483 1250 771735233 771735259
    0x3150602190602131509090c050306100c060c0e0114031603020a050c01111314031002090f0d110a051e04050a06030f1b05030a02060418060509090703030815 69
    0x10000440414000d1000602d413161004908041c40c1c810f038000c1d0110592048410312007600000030500829842d0030901c6105440c01c0700400d42e11004181d140b16240c03d0031420300941c40703190f20001980d80440100003d0a420901908081d42da042c1d0318000f503019000c0394052004203058a002e000c031441140328500c428001a8043d401040102040040620124112200c240038080f07000014518065841c070781d003101c000c0c0c03000d6143c1110300e0707807001840345030750790f880000380d054220740c40070707401a21980040d0005030266500074200d507000d864031401c0002e10a03c0010001942d000f00d4080740b20541e08c00502940c1c031100710441e00824150455941c0c14105608446e5005410701d0340090255203a82e034030141031030300c400180c9410948000c0c45150745002c0010a010307113001c4000344804001603000807803a102e94014540380c090942254106106583c02800191500800007461490044104c40c4ea034503003071106070000303a140004200d840510344100716503020b002d407000c884005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 771737733 1250 771736483 771736513
    0xc080a051005150a03140c0604060e0d03020c150924041e090e0f120c07420e010e090c070f0b0c0702180606221206090303150602 57
    0x10006000341400c4580d20f18280440e0f031500c0801015505c40ca4860346650b00300300540385405c3c4031000307007809900104014056241c0021022814400841c1c10255900301d41ca400c070f04000c6041f1946400c500038039641d1881c04044809081c40f1401540e40624004802012080e21a1031140f42d030104d01041200b403140e00840c1c01c1300c114145900e0b1301c005005982d80f101c3d4040713544219603511140c0103050180c150180a01203038035210800d40e89541000040310015440da001c80c03091484041303002c94102c1000a620b140c1c030b041017240c1441d0440c2d131203209414805d42d07424002d01c80c00080c0e43d540442110340c016a40e9002c8008080d100703256982d92101231006981c0b0181040d900d21000d0301d8a80002070504c0d00940c400c0d120306850303544416440c414800d8542020740924a00411310003041029140c000948441203416400b044010310001c203101c8101c680c0d42c104964101e0310290071811f015140d040780a5180c442e03902000f10a0071443c004106841501882005030024030031505c100c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 771738983 1250 771737733 771737741
    0x180504110d060e0d0305011d0907180b1525080304020405070c020d05211206010f050d0e0c13150e061305010e060415061421130c080a0510 61
    0x41d00ca507000042554410503451302d413100c0c403400d08001a1b201d800500549400c0c01509903e0854010207880c5428000b0710107886074400c0c000c403101014401c90b03025a11650703401c00b507012040540b074610903495100310080294031074103540d01d40403641c880c402d85003844602c0f180c024a40040d165419a1100c8d42000080d1001414040800c40c030310343c0c10009a51409028284a403041c40201400e81070794080c01c01c0c108401c0d039a4481c1e80c10910644010103418003d2652100003468a00d08072003144e0b2050745d140c000c440e00040ca80d440d0080464501c50001840840400101d4510202011020707143e411f139088214403c5100000b43d90400807c0c108034909504180000c00c074085034890242001c041b10806d0b40a030b441c051140c820b121803402c0c503104100908a002161043c020305281c8081c1c81605484100202c004001411080d201c00c82c403e0320010480004040066040000060b400d0213401501641c0a110215001614480004095103030590120140a120400c5010f1070014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 771740233 1250 771738983 771739009
    0xb0901260a030c030e060720090108121603020a0b0c040806010902091e0402040512061e100e04030201092109090b01020d0309171c050105010c030c021e03030a0918050411 75
    0x3408403500099011201e940031401040540c0700780b41c4054204101c2d504180c0c0054025004222001c0c2150300f0cc0084840c2143c41642c00c907441055860101d20304010480041d01031806103082c0100800604010000c940c40c150850300c1e0b80e626890700104902c6502042644030f1422003e0741640b4118181c0006000d100400041c01c081d42e031800f1684440004115403825000102041008204262401208000e28444440ca480c2c515010700c11441e680c082c40491020540010b02014402d41080760b4055110101c1b8414080d11f590019404215049031004210310b46000304a01d00d0038403071010000300c140d004144000c101501a401850f544030180c5a06880b0302802d1900031001d07006100701c4c51100c0070b081c516070002c101c060468030182c0000c0d040014401c600c030046a80040c0c0f412074240c0498480f00c0c82c0030135509600c1c0d2441d208600d44c2d05400301007030192603650000d6142d001c132070000c1518038100c40100c0700e04c000ca81c2c00b210020615240d12f0400f003000d0030000514090 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 771741483 1250 771740233 771740239
    0xc1503181c02010606080a050402030a081e1215121222060203120c121909050109120f1b06110c030f090a05030102070b0c0d0b0901260a030c030e 64
    0x2050300031040e00d001c600000845040941e446038800c1000c0c9903c500c205600c440c01d0801089282820340c0029224004071402402d440f1011070a2800d0459208070700e005403004d0b0304516074a102e00e907440d074a100411a0b00c13006030452a2400041400e0144152240e01a00e1014014004107500a03110310303000107501040d40d8405041660345c066040f030b0070001a1003650021505e48540c2889100c11040051081180140c284089030b0a820100340481d0014007000c0c44000380140c1507071080042c081307000040d0507503003000415000c0c001500c00140340031031640d0341c400034003514001c1619903420300713850b90781058600d8040e41e0104a055001a0280103200c10542c80c140b54071328000d10303540180e50355880e440c00c0080c52011625114001c08010302040e0029401c00585494000144000030622482042d001800c1c100044580c1d0040e4103200d401000002c46584881d00c0ca0003258010b02500401714587c1d0866504580000310a401d45e41e0640d21a159501c5a036001c8035040702c00107c0b10b030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 771742733 1250 771741483 771741493
    0x9100305070b0c010b010906020c0d1a04110306060324040602120705180d08070209060307080d11010e010e0a1209120305210118020304022403010303020c150318 71
    0x4001981800400d0051100c4401d142d2290740c4010414210790170421046d06024261104001c1d80e030b00402c4401c11035408840c0060b800e295411f1117610314022100503012007151408100070090b400264103681d02c4241c04072407640e6030303203800c0c15601c20b42ea248170000014400080c000b4400401c007041d901c548a4240513080007154458240445010354450700400c5010403104500095010b000e012618115081d06030460181c90f03010603031003000c8001e8020110b26000403800e44040208000034011602100c0c4032035030801c4010f09603054802855065428080c080400c41c47c14010040207203c0440034210100e0550340303d40f03200280ca10381c1000d0003181040014804840060107041d1030080d200c0a42e0350f41c01d44000b07450406140115501d003201d2400502103680e00c0210b00c1405100c20f40e0040e9252500d0001804005007507419243d83c1501d040143c041505c0d00d00514101d81c42a0204c17219420301c8405c2041a00c110300c0d10741000c80003480050b0383e070f481500d00c1d0700e82c1e40012401c1d20 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 771743983 1250 771742733 771742739
    0x406020705010e0703050c030307170c07180b010e0411030705070303060510090e09010509030a0c141006030b0906010b03060405040f0b09030a18050a090e1f05010906080105090c0910 80
    0x60030b540c3c014018100580140e00100207000341417161690a4408802461400032540c0d5944100001400020780020b400702d421010340300204006c1c00501400460601202b00c9850f4070b2000d8510514020b0001c1c104c11404012030910380100031651248490041c1160b4500d1401c03115900000001d800301901c440001401e030300d40510a80840c1e1407651484a50f0741003c2800b2078040c409800d564045c0e00d0141002200790010082d1050303d695807400a44800303c606060941700c102c0c0341403400c41d0041c0b104a070b80d080340c0d81c0c1c050340c00c072845050300401d80d907a550b40043c0c40b8042403060b00d0840408100149281c40e266001d25400382c400c40d01000903c04507100c84491080440f10020150300005900740482e03000201ca072228070b01d84101242e42410103000c0740b42d84000340b143e44d40c42500c0b182d00c1700c0405e0082c010305030307004032024280c4103090214000314040c200a10510f00000d15045022a4001c0d060103050b10803000e030300c002c1c043e00040009029035100c000302443c0c0c618094503008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 771745233 1250 771743983 771743993
    0x14040f08030306090705070b011502030f040f050a06020a15020d0e0303130209060a12080c071206060918020906130f020a200f1b0f04090303020c120f040e04060207 72
    0x4080940240c00040d40c880c075100040c02000ba0002c0c00d0001804000e100410009080c00c000c1c0703041d10345e5220850703602e142c1d0400c140d00d1400b410030f1079040108040380c0820058805ca400c14100d800c1110110401540e4500a03600ea1015400190004203200f41c0c9455220079070b00244510b52145000140303843d50100900c0c1140c00235030300c2c40000081d80526030150316101b00034a8201c90226943c00c0702c1c500d010445a50000780d07840040c644400401c04404020061089600a0051500a15039800740c1e14008000f0a00d038040c2240e003034134141100034400c2030031000030310642d4047d1404107075446031410050056a8017059407a03154031440c0702124007009001038080784500b9142c040801800d074681101c83c20459010400e81d41c0240b115440e01200007a0300340d007600324144510380024814001c9404030450102203504182072800d810201540345d401414425002c1003510001e00c400034030070344c6038441c03003400b00651002803106118800c50a8066500140300314401171510600d981c80c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 771746483 1250 771745233 771745259
    0xc15051207051b060f011707030b1812070506090d09170f0334110d170a0c0519110f0d060f0b12010e0714240414150306011404 56
    0x141c3d8040e0703001502806030328120b0b01c2806000d040740a181800b6054440e004c180d507040300c1d22020301104804c001149980b00c0c0150651000103078441034440390740c00d1560301c070025071117440c040b0740f81c0c4600c50001b2400135001c5400c1c20f9002480e543c541c80546031902d0b64a051030b0360401c556150007034580710440003004100501c100075808454800005120039969582503040c600340da4203c0c05484000700260805000f030243c6801143c515020400340e0a008042c1301505050705061040052a0840e81d034121000c1c8c44114031850072501310154103100d40031103c0b0100e600074601c901c40aa2058103103040d5200c030400703a0000e04a082000025240c3c007007550242088840c006541ea00b810030759051101e0345034055403e950003401601c0703070411000ea82e0102807040851500159022001c640c1d10000442c507190310900810003292000e0111403243e501900c070307419080f6041006084c1030f0608201d4990510b0100381001d096a80c1c40c0e005584201d40c12031030b140c020004010200d040031050b04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 771747733 1250 771746483 771746527
    0xb010219022d01030b0105040f0905091203070c290628030c032d17120906010e070e010c0618080a0503010303030b0103060b18040b0301020a0201090c1505120705 71
    0x1448000400b82e9000140448507007100031810880c04100500c054614000c00a045580f0710301f00085561740c20b005242825800e850300b2201d15000014400129440342049010760701504101c0c0d2444e800c0c08590382120760601d2030b10802036030340000504511300420413040702c65030a070045c014000300e5003054580d64071075002240d000076000028010301440e50210404ac000380114005039034101d401c0d03c0a80c1d07041c5000200b203030242009014601c00000196000003c05c0403e5020078140291440d40301c203001d000b5100b05540960000300c6e014881c0041310190300060319480d40721859130b11800d015009030f030021111f8542000040d000240c8000052140309050340c0c42036100d50441c40c2c010150384041104504145c240f440030700071100400225640c640107800c0c51041c0303c0000000c24040e0940c4101aa41948045003406001c0c0c1c0641102d0300507486641100720058861003040d030950102c51810f80058000c1c807152603041d44010342c980d0031554600304103040880320300ca000c168812001d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 771748983 1250 771747733 771747799
    0x20d0c050a170609011e0905030403020637120b0a0e0f0108060f0105130c140c01060806130507030f26190c0503030633030403120b01021902 62
    0x10050b80400c003802e02006030840020002480a482d00c04030880e0500c070034840c280d86d40e03680c820b1002c04001c0100100c40065502030001c6032504182a0705004c040c03c1ca1070001c0a8104030b00d800601c803c00b11540f1040302c4849e8071186c9681410780e003e58014004840c15503001001c984003c204032191403a164840c41000e0884078066041010950510402510810340111030381c0040c410340c0c1d190741c81c1c0c104000380d92200040b0a410180c00300c440e03a45890342d0900c00741001904040006064114105440041c2c0c1200c4950b155095001680301040901405a8120140a10004001500500c41d05000d101d1160b407145003141c26000645034001d950000100024000035a60b00400d00e45010f080d8904201c1d04e882c54a8a403181c8034070000300214410340c48406450481070a20000f0a1044480c0080d4626240c14060171000390b0700c140c400f0303000724400e2083d101411030f860040c0e604075103041c2d000e1704060141da040c504811441071400c80c0d00409050354031403004020703845080e01d10250 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 771750233 1250 771748983 771749009
    0x10f05010902131502120c030912070611190b06010507050d030c0905090402010f05031902040e01081e0a03030f140901091e0305030c030a060b180f060406020604020d0c050a 76
    0x180b040101e004050b50b0044c030314222000d034070203400780e00403500384140070213031490342c1d80c17005903901182c01c1d40f0514001d50b0b8032549038101250610030004000e000e0300c0700b54941946504461066a564652021610442d0303208016813500042180f003403950802c106050907810300c0025540d15081c42c001000800000c3c1c2d070307071918a6030706520440320802404240d40305821418140c000030705850b04103404c90b040c880000042604240d11520b80f110a051021085489039168080e0b110380170703400c0c89658418450301c101020841d03620b19600042c02c6880c0c0081115070050303038041d40505440050002802e60f00c101804064960500b21485000c405000140d214020b280c046880202010070105001403078603034400081d001011603401c000c0c256526512030790f0f4000c45401400885d0062600c00707001081d000364080d40c480c0b801c0320012045607c000c0184480003031207440d0145103d03090050740864042805400e145030070b0181107000f00e0003810016100e0010a01a2010390301c18080c09400c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 771751483 1250 771750233 771750247
    0x103060806151f02061f05130f0c260408071a0a06080102090609010804080702060427110904021308061e100e190f180203010f050103080a0c0203010f05010902 70
    0x195148440038152207800c3c0e290401802e10003940c45a0007400c5010350505417101c4003641e50a900c0450003082c009004880c07c904407803600703010b825207070031000c412810301d14804525800b4240c2655840001c8a052540680d030458078034030100007070015903501e401081018081000c802010741114012013907468142425140c942c1201c1040e40180386036441030143c0440750ba1060100c500c88802481c103c031280e00c0700e0030881d04610601c40000e43c444400200020b5154551050b00c401c401d4098103134114022828451003505d540c404101ea01d40d900704080380c050301c0c0075809404903810351382060500544032501c96103422400d0f5903001442c80c501001c031440d0b0701059601c55100c0965040d0b902e005203030108401c118440a40003103c0a1202441c6840f6001c1c954482418840a02802d2008103203c640c0c1c40c414081110703080e8040e5003000c01c8144685810300030941225404008545054131481040301c10207062841203030f155480c3c640025200300c0600543d0701800d51040b0040c0e42d681 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 771752733 1250 771751483 771751489
    0x1503071413082e091a040501051e01062102160b150402090a06031e02130e070807080a021c110919030c06030f0207021f3b010306080615 60
    0xb541c03c3e500010550300e0f40c0c1007001c0b903030a0746a01400b1030b103044000c038004d604d5241c03400b440050b003502d003d01e243c0000b00b040184503054200900403115421071154030040c2d400702041c084800d00414000c2255103d11400c5400d80c0e00d600600b000c23849600505006406440500425588906544419a00d4140700d1101d240c03441c400070001c41160f0861402c0c1d0302001003a01144103205134400d250307507104a00564041c0d12903500041107451001c40d41c4030101c0c14840100842e44c001d6040d1311845100007003c160083da0000e01a08142c0c031903854564030701d8600b070082d6101107101d5140d0f440d0701440c10042041401104a690001c2c00e203540c4442c482070600c180703008000d1b1406210f00c0010f130108041448403130f40d6019140546004581982d050340e82d94042e100340034009401003582c48449114048813002c2d0001d41c0c0c0b9a50b101500d14480302054000c03140803c000100740f44c041c000d4030b8290007544003101040e800605022401958941c42c003403c281080b5000300f0255016105154189 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 771753983 1250 771752733 771752743
    0x70314060f0a0902030606070c03050a0309050603060915120708010b040e0319050a03140403080a05070e01020d120e0d0801151809050406090c081b090402150307141308 74
    0x11041d81c0e00d60031454000700150b40011948038940c0055400000700300240c60b400100c0724219005400c407114030390b0b20310f001659a106030030705600080c10880041040c1c43d2441c00c03203008a100508100440d03c61043c0c9074096850301180f542e20800b50010341e00e00403810b10096008001c04800000c07440301c83d4043c002a01c80052640a0541081210000c85501c1d0780340114218041d1501a843c0c15030b4803130960041185801c101c015651210402c42095803290a16100318050f07001031106880d005400d030f0300500058a07003805030b00600b441e02030301742c80f403c42041d1054000d24007180c100d484121a900b02181118960002504100180220419910520310f4140c0c80d00d040560083c0c40484807084802902503080c5840d00e07600868184062500040d98060b004031002c180959551010707580d1f003101e0491058408881c0000700ca031482e202a980d4826500074055101050b40e51044843c2a070004040900340110696094400b0403040050914034600300406c418050401d11003c0c030707007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 771755233 1250 771753983 771753991
    0x9090b0a0e0a0c1404240201110d0507121a06070f020d0b100b03012105031201080601055404080a140c070501050c030c0313030b06010815100903050303070314 70
    0x1184c02080200600421030030459509441000f00c1820410302000490240c0190403008031103003008100c81d50b152200ea88201e001c1c0c1c41d035031a00c00700282003c6010b02a20042040480088545035000400741403201c010030070284207600b503014070b92030784e0b0010b9030000c40820b0070342d0050300d0380302001981140d8001c140094015001c409043d0340c074140d00305400c01900c02052030299605c05114081081c20010386032500d00c010a48042503840302a0305507500b10034440c2d20f12440100b6020b840911141e84d0411100a4107424440c052510301e8840c4a205404280074052150b05407071007000750030705580d0305d0082e4030400303202c0e50f00c40c00200010f20a9601c81150000100e04011903540e03000001000c3c4112352080c01c2854980003000401e60550080306400c010300c2c00b00150480381c0030b50880990095a20410f44000c031500c0e800c004442214044541800c401060440c260b034a1822409511460109182082500f52650303101800c6400c1902d4440100307403034070544000743da81070075074580c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 771756483 1250 771755233 771755267
    0xf0d02250c060e0f06120901060504020f070204050402010509031204051f020c0f03012702040e070b1206061c0b010206060f0d0b0a060902031e0f010609090b0a0e0a0c 73
    0xa029601c6042045a541c8074001c10b0081e052007180441d03c403554a0492030000030440740c0c0307504074200f1541911004540d201e02d41d501e040808661440c1031710035074002606601c450ba0824509500340f100618010300141d05214091249a400360fa007040300c9001603407540306140c1c4a07851301d014882d4294405080c001d20002614003000710319800600c2c040008002c45071005003291a50129005220b15401c401d910304d5030030010046503e841f41000c2c0313624400c0d9020468040700348010768035400c46000c6e040c1c03d1841040103918640d414450180c0115004010a183c1419202c00c642d5400071121040401915488007986941c0c051041c680e02010a45418903480000c10004038a0114044000d1a140c224008100d1100c2d050384060040d0002c10411992403d1034131040c2a41e50b4240c481c10780500c1102c001480403008140864100d802c9034541085450601d01c441010300110441c0300c0d04600c1c81600041c880c032144141500410126000059111030000001c0c0902c0b814006521 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 771757733 1250 771756483 771756547
    0x20a050712051204020d0f05011b20150a0b060a170619170f06150901060e0303070206090102030d09060e101a040207020102071d07030b0f0112020f0f0d02 68
    0x42030b0f400551010380c041d170704130780d107250180b810329110442800c6900050115840e15241154055001031414500c0d41551a0195041040c41031071000c030443c40440c903e15001141c22002a400d114030341d9810885030039001c14400c2400d4081040c541298a0a4001910003078420200c0c0d803158100b01c0d0050829030380180c1003140e21051400e5048140b244407070b0240d4001d0703220328014091101480306074810094541500784201c15180c0c80407100c58507886468500c000084450003110804c20965003c2c0c0514202140c0f0b4081011030340215007a1419404200601c0e10010030320b00c1590140361081e0000a440e210201e507c0e072800210004400b141c51907c4048103003100d80c0841c46005820448015035030b90100e1004034205881e981c0016a8040c12419078a0002c1400340350720b01c103242070b507003c2005992a108102c180306000881c0c50100ba481135800c81050501c0e001040e81003050a000d902e00280041a0b00069201c2c0c010710a405502040b494406d80030034082420422210350108 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 771758983 1250 771757733 771757747
    0x93001020d0605010e0f1903050307140f0601080c01050313050d020a031e02060a050a020403080a0503190606080609041e08090301151d09240601180807090b0f0301020a05071205 78
    0x1a5074444985109104507c44048007440300200c02e80140a168800c2c127880e140c02c040d10304094011085400103485014141c168900c401002039103604940d000703001400081c00403c0191010340c80509552604803003030143e4400700f042080700300d41c01e241030741c02080d0000b82c40c14000c0500d0841c0070045110718100345440c030041d90014040750000c5040ba000240b5480740c00f0f04030000d00c01ca81c0000d0400d0030204180038420b0708000a14440e01d0b0000da402220401e05550f0412200344c0e000302004100300c1d0000c2441c0e4202460840e82c00707449801e900505d00141c54605002d070140312000ca911070b0000822100c9803c007802910495610500c403840a42c0c2041039036208080816010225810990001020180b08110303840001003003036803019140d50f0151480002d444103d47c0d0320f001c240300e080350815144c403140e9418120f54541001d030000c542804c0c110401b0301151814183d001440310921802590288018402c0c4034070380c1c0702c860ba200c04501d0303c2220300540e81c10200501100b48811 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 771760233 1250 771758983 771758989
    0x7080d0b1c050c011d0405180a031709030403020a0618170705031c0504060c150906050a0e0606100e041d030403050f0c0a05040e03070c03290606093001020d0605010e 73
    0x803206a4100b10780c01f10b141d95505078070200441e6200140d40141c4140101c03103062640049002d0444007200c4054186543d404108503030380e115600c0b000350800c0009034200032003071207614019808007100c0251034041e550350b602c5d00c42031443c02c041044650005081040149020031a40c5006020b205c00410340e80c3c65010044e0050282d84180414040c0000f41f10341042040000c0c1d03a0075440404081181461600348000144000c1752540401d91502001c0070000000003200c0c2d1064400400541071f00c802003030b0446040c3d03074205a4135009a01c9041020500d500010701d07464154840009503201c0b4518144540750a00300204220a82c0040145412f181c542071420400d4603c25a40442c041501c2c2101c43c2c65403042780400361250f40b03010400300411420b80f291000e0102544205c1000f1000c0e031240c00c142d006c069442c15840541003040c01900e04041c81800c10020350014541228000070251840707410604c2076030f1f0480c1c6d60000310b115503948039200d1000509002e2901c440402811008 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 771761483 1250 771760233 771760277
    0x270c10301a01020601350f0d03180c090e010f11090a1703071716030f0f09050a1203020703080a12050c191d030111040503012007080d0b1c050c01 64
    0x7001070443d0181d01510801903207107501046c0c0028000c81d980207060340d640c66241d45010701c4500009080020011540120b8180e064806400c14010b005852071300a400b00104604a4000d80039500e0f034100100050f03445c4106800c840306050b03d85d030703244815020440d1001d899000040040c01030302880510310340c0007080d40d19141c2d200d83c03000c0850642c1040456907008541d10b2900840d41000c0702010540e211204024511141d1652940540040010744011481d401540e17081080500100b02c801c00440800d18810300a0042d80c0070340703840e42c40341d00041c2e06c407141030000301d40c06005907040c032416485216401900c103035000317080004201120b179120710720104c80ca0410001c3e418100d42000e00c0903265441b0a40140200451600c0520101082c1c00a1260f640700e07511b80f056000e891000080b55000c03031981510a5880c2c100c0580d51011250804080342e41a80e42c1c4e02041641605e800540c203018003481205d80c040ea00a520f046840c4c0b40707440c12950f0410003c210070b82038180c0080300c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 771762589 1106 771761483 771761519
    0x31e180e06030a0807060204121b0902181003060b0c010e101107150906020403060911040b09070f05070209270c10301a01020601 57
    0x4a403a2444104590803501600b14489540000789094002c00b035540c8540d50040c1044e403a440c0302c92042c1290a022241203007540208020355441e05802c034024000e544c1c0642c902403075024400e006a02202d00c0354050380440c0719150213140281c0140003c1c141128016403159184000c0c0c0d400b0f0600c0b000f4811090040c400c181c003070590a401040c000303140a6058614000596032070440041d02d0300781c010055981c5000a03000a90035000800045000340404a1118042d0a02d24809101049018859450000407080c2c41e21100941503021826050061080400e060140e8003480313802c400070341c0400300500b04075405c07001c1c10080b20f088048220205445100c1240e40e6628801c400040d0307400442410074810303c0d813103100a80519190031038000900c5582d1074005051101501c4088205074450450740e51609040c2c5045080440074401401b4651401c0466569949000 = true := by decide +kernel

theorem cover : BRFrame.Cov 771582733 771762589 := by
  have h0 := BRFrame.cov_init 771582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 771582733 ≤ n) (h2 : n < 771762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
