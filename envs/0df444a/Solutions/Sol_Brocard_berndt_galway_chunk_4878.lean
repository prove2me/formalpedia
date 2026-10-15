-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4878
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:01:49.320204+00:00
-- url     : https://prove2.me/submissions/c15148be-5597-44aa-8579-8e7d7757175f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 877158273 ≤ n < 877338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 877159523 1250 877158273 877158281
    0x1320090621090f1b060304020406050d2103090809130b06030109020705010f021804110904090510050105060a050f031003020a08150f0621070b0307081801050403051b0a06020d 77
    0x60081501c03e1100c2c51026040115440d441070580315500700d0340d045410148002504014030907680107548040010b907135211b850100c12814030070345111405a44200050301003691410940d8101444c1018100c0000c0f000403c0360010316044a0050503450320483e40c1000d031600224460300460b010000281940180d0090b04205103c0c0c0000e2140710000c5212000320300801c00301e04408102103170880300b5820103a0042001503010003c1501d084802404203064401d5044221a40d070310500380d035600340b07880d40b1a40c1c0c05042c040341c16514008034104028880e015141d8846841c84000001c501c140500c0e025580007107901030054900aa501c0f12080c0d203507400601d100701c0b403951460008002070590340425110382c1c0000c20320103610b031098040a215440c1800b1031110ba22070414085042401d4030051032013100d25583e241c0b0383e8071f00041442e025240501030007940380e041006001c0002c1c0c10809480b00b0711034074103c051300002d105c240580f421030308982c0038148610001c1c4441ca0b410310303900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 877160773 1250 877159523 877159531
    0x120e0f07080d080903072a150c03030e060903340602030403120605030303010614160f2307210b010f06170103020310020a0c201320090621 61
    0x83c2c0f40890360391055159203901c15482d00409010581041282500b60030305140b0403481d05500901c001070300c8003031000d43e00c040401128081140c64040a0800da418000c03010090507407009410a0300342005066900e01030074900040350400c3c00c00c00c2c045101c800c10b501c41c02008400ca401e03904070707007400c010b00258400e03581600007c60124150079030303162502074541190800381c029031440c1c0c03800b0740c103c9955510703483e03041c205001002910661910031204560440c003030301101000c15001d203499000b0b03684d4141c100c0b1540d00c050103119114400418058200c0302182c40f2141440701c1064600b04c42d0b44111700c000d10400c42c0341d0001c240520f04002c1002564001d0b1905100e821207125600d0601c0f40902c4000e40c948c0c041c508a805035016a006414049011b042044204010396501d4141076801d012040e12000001440b94451605030708001c14a15111400c202d500002107050700d401100c088420b401440009600480d51100c404841503200b80607864040541081e1160082c10400d407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 877162023 1250 877160773 877160777
    0xf1b0603060e060108090d080703020405060d05070f02060906071b0609120906020c06030415090807060903020c06190c170f04050a0501030b030d080c160305090307060f120e0f07080d 80
    0x4800189513500405171280140310510081c89001e1720340c3c400321441e000081451042540030b0100150fa51aa5406404114600040882d440c03030700d101d00078003255640c800d4400315840201400460320b00481c0716a0880c0b0300e89803410800030450a040079041d03000344000d01c81c2c1d00c0d081c20b900511000315030000a010150f52030b240c0b05692540120fa60f600c042c041194012000c2004c00c000401c40140360384130001d20740d00800c210f91140c88a0400740c0152a0a54450f031300c03083d0310000c0640c18040c00c41c82c00400c80c1d02c0d82c00d00300c20080e5807090307211400e806000d2142c8488008180700c04021144d806980d1f640d021513031110500d00c00c0d00f0759001845104d000d0380007048082072641c043c2c02032090000003d4000c02003c60304460855411074040c01c01c000900c4104802c400a59243c403c020b40e06000f40c030351580e65030302001814030304041030b48070345e0400442151000515502012000d000d03040700002140700d140d60983c80d41000105a201c0710288940e400000f60200089540341c0e081e007160b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 877163273 1250 877162023 877162049
    0xf0f0318050108010602030d0b04061523030c0a0c02010309020307230303180907210209130501080c22150f06020f1216062d06080a0f1b060306 63
    0x9070019146103000b80100d0002d0380042c02489901e6101e544110745115008102061407070b910502c983d0059181d5401e54002800140d4055840311000154000f1440405e06c00e4a185040d1000725002d0003900a008200000000c0314070640e81309801c00f031401b540040603103080c107540b0850400d02c003910789a05820a202d9400501d03951a020094070132003038903154030500800085042120200000b021101805030100003030540203519460b4011001410303c0c0165500c84040c100603070300d0f4584c10426003241c146030042c462400040b03614411404142c6103480c046908111356404a00c1260341920031901d001655003402c001c03010407104070b400e0918008031064544004980f1a494440703480040c0c2d05c6880e5841a8504032001041c41024400a1854803401562102d05481d0b0781c18110302d4051f142d410a12180100401c079070f5042c21a15410013503d40341072b0080791150302d450b102412882c00051400d0500240000c500c7c00d03e08010460318405484010190080c01c00380039600c1451f4034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 877164523 1250 877163273 877163279
    0x140313060b041e1b080f07031d0102122202010c12030b03030705010b09070c0b0c0702061b011d0309131a130f1d03090925020a20060d090f0f0318 64
    0x171540303035000c0c4851340305540c55540c9001c810340240c100a0b2940c2d08070b2100b10345071041c10f5001e1001c0e18418601c01003906045c100001008000d154031800c1401128411980f000140c0e007280c1c00d5501733580d11444d0704540841581080e802030404c064102c0e0075000c00582107081045c10341c001c6040e25000c80b041b101640315074008444082d003072000144106051004101605c0c0807601500c0340360701c0240f560746010700b00c41010714007010328000390044c2c0e0f4442210000072031142c4094840d43c600c0340000e50414640000244404d9400c041c01086203507620034010503102c1107040d030311051030b01030f01d008459081d44e0041001021500d031001d80042c90054542c0b21503500c0e01c0704081000b1030304025400c001c0400104019400050002650141c8001813551003849110040700241401d4003c1c280300640303070411010084d2018556540d031460644802c03103d9441e80e042c0d604416600301d001424420600d8080d207200380c5c2d020041c0010380401580d000b00340d171100054032041c202e9244881d001d69 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 877165773 1250 877164523 877164527
    0xf06050a0f20370f08090a060305100e0c180d0210080103060b030c0d03030213050405070509090a02090a2d0f08010b0d0201120207060615030606140313060b041e1b 72
    0x21000c07101c0c10100030301c0f8950401040d4102d00c4407094601507035080e0b140281d04e0340084c0c01c0c01d02c03561100001c46d0f142d600708a03c85481c11b4443d80100400c641405051405506841c1c903485000c0500c1e03400e0303d001d280d28000e130f203410303041c401425409004052a070011041c090700405007403008807500c2d8200000ca2845050104252010301006804144846101e80c0c00390b0180d00b0024070b000a041540000213115a41d81c022680540e0795500e445a4030b41054040c420324150040034408410300401080d410b03500c035000300760120748c000724583d01c2020710b151115640410228500003041c5040c0400b08590b060f0700d40d520100c955a000070080f03861454140314031a07804140c0640400c0d4190303401c43c841010b0340c000f070034843d1140100241007926940a140407941c1c03d0019030000c1d58034281442070350381052040f00c1040245c0d03211811031414038001401e07180340040040c11103803110b004905e10b031141c0d0003564052900c0180e4801b0b000031803690070b004100040b180280ca1110b401420701c0c0c24 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 877167023 1250 877165773 877165843
    0x911031b222a020d0e010305040809030706030209100302070c05010c050a051219031404080903011508010504020a291c0f0902010e150909070c050a0803100f06050a0f20 74
    0x4c1c00d0311a42010b00c1ea10300194010b0034024000c2d039045004004c600c0086d0382c28007500c80600f05035200103880e4011041401100c9114681e100107061042240d040450300c0c144603c2c0442d0400d00c0e0251904c0c1e1b1500d4180e0030034988190083c03580c425200ba03a03841419020103001e09045011010320459000c403021800d484082d480e104d40c02c9031440100d03000c2a840002422180d0014002044890746044803450724100c682c030540950b59604203100841c90002403080c010b0040440c0700d4200d0101e642c400035012034111010f500b4490014940c0c0700c60480b0008111803001c460400c106121028403140c0c05041502d1040f40000c9540c003120505281030f07900342e101e550050034014240114001072000c40d00e80030385101e0505c114240d2480005104000130690305103d048095142d0400e8850081c1610320381c1c110b064142c0b03040c1d00520110307074004103560505400f49000b01c01c2c0100a0400c0c5c40010315030101082d48481d800c41c001044e40001540c4020b102c41c401e0300342d05440709589400f04c0c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 877168273 1250 877167023 877167043
    0xb0702060c040b1e0f040b03060406050306071b2d021207150c0807050304031b05010f05190c0b011502060c0708040506070602090406090911031b222a02 67
    0x3e001484540f000c0103110b401c28050203000614186014003098080c403003500954801da551440020410800e0704060040c00024001680184881d007040785002d4141801000e981030b0080c0007200c00002e0001d44d08110b440008141e03020140c110301d2800c40034440034940016400b450f0040720350400b000b000100320044601c0d00c0b11400c07a94600c04000c0350885c802c00400c3d50040401e110b03003000b01d4070500003803008501c40d407007042c1d10f5610b00d03080454000840c0d100e02d06110071860b45084460b00801150490300c19111304040860f444c00096907103109030000a040100c84e030001084507280014110342110b940d4003202c00076030314402100024495807000400c1040140010006402c0c6800900702c0346124000140c24800450042400c41e081a400b0700c0100352103940074018407240640303292f0300b40b034154050030a10b0710122120002d80c40401c06a405028a031211180c0e00c100c1c00f81c0440034000303184081c4920030310341c15050031038903111140d9030070360f0540300054000500000303186081e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 877169523 1250 877168273 877168289
    0x4110c0d1d060a020a05060f061e0a0501200d080a18050c091b19140721201506010f0c1506051f02011d070e0615070b0702060c04 57
    0x1d1640780018400c40e6045580040250300c0b6025006001900a0007001d10072005604207029525210341080300e600d000e25071010b00c01d95050280c021503210640c000b001d8030b0083c280700d00c03456442d00310044c0d18502c1d404a18198000c80c0d241d200800d030f000000c0ca01400442806000305411010700d510302d2a44040018002d6000d9030041c2c101c2c0c01c141c0011a482004011140008801c80071904c1665001c8010b24007a6404806104941d03600500c0740000610108101400c0aa4640d0340c031001100100e2020f004800580030010550721955034803060010702001c034200c0c511066800385c0c5d00c556180104146035130407000a08654411040c004610099030b90348a0741c0d0010b41c868200d8480503803442911142c440801190f552525040c00040c0a007006080300060070085009007107602d07102201e04280d50060300e24800340b4000641800b0b4840100c45400e280d02d0300000651104807010b0368890b5400040355500c00d0000791540540702ea421358017503843d03558606080007400d1041c0e0103400c0c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 877170773 1250 877169523 877169567
    0x250503040b0a02040f1413050603030304110406090c050d0606030b1309030221031e0c121f080f0106060e060d0b0109081c03150e061e04110c0d 63
    0x1040d01c5510345500000c0310100140790070b4650380300355602e250a400c0b060404155440380400303404c018800d20286096250108010b0070080c0000380c4a00c00600003404000311121b280c00d007070391213030311003001012008010404400d6461000d040d68205401c070051040c0f42c0540090340740c1c0a8010310800c108028a208032044428004e44000c00a00405600318411581c50380a5081480b103909006034003821175035220320f005410790800c2070011400c140c0c07100d03001050101c23800c142000d90720030f50500790380304507250740d400c6644240c0c10062078050743c4940d40e4100001c0341c407004140601c082095400a103d02c42e210790054890300c0c80c660603541c020a04106010354080d169001d5004118140344c00c0403803643c0c8461141c03034030319011040060100e00b0000c141c0083d416118004030320300d005407031444643ca03140039148040401032007a0b00500c0050140c5801d6811000d8224141070b0081003041201194031004500b5040750201b002c181c403c1c1c5004806050045d561140c80d1401254940 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 877172023 1250 877170773 877170781
    0x51c14130b190201200a081005100e2d01120216140d0512010b03090a0b07080601021504150b12011503020a170c0121061d060901230d120305250503 65
    0x11440710000f070548c070040f0580280441c043d03403040c194001c000c40a42d10b60080300349000400500b00c004e032203a400310f45a03480a030303084d81081300c00380c0307800c0b10007400c2c203014400280c034114001e40f048146d00c0c803801d0b10b40a0b0100030042924004a41403071103400712203082585d01c000780d8051240010703204500c8441b40c010805144220011079118525409903905460941d8901c501d094003646c074880419004410007040c2d503030400c60f0b904940c0c1170086010032030030140c440c002d2282c9000506400203071510b0789170f119512450740d5010032004c000001c000e031140c400d05240c4800d1180c00228440d09000c0400038030a42802603081d66014420050441049030000540740c031420180400506090711180400d081c1c894864800100b002155404981400e003401602e500c0000b40007501c41d400f024014040d03682039408040002c10301a1035940003050040010b1420881f0500050002c103142d491540e290f685500064094160010345681070380c0e81c00c02405110702807510348400184140005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 877173273 1250 877172023 877172027
    0x30f0306191203170705120c0d11040b04090b060702060d0e1f020c06070201020703200a080a030e060a110a0309080403020307080307051c14130b190201200a 69
    0xd4081c1e01d4401d10807207041d6640c1e110780485014054401e80211350070040110105a40c1002d01da07110215103811440e10352052a100c3e603ca10141241d201c8400125411b100381000780d0002501301d580200306c44e1115514401c1c0c0e00154094004d030380ba40350500442805c40d040500517102c10607402480d03641040790b428a40c0340100b00c020f86400f0203110f480c03a220f4410840c10294416030108920140e592000180000e2501402401504c11a071040001c6000311350702c02d802c40354603080d591b0040009450548400d00e08540d065000c1c1c146040003134200481d50301a401050361180b20000d6810b5561a84c000314101c42c150703500307000e090301c04020ba02c028520035407000051a01c40d03025103003050b85a0300443d1810161350001d4419500c00510394040c0401003186041c298403852580c0d840842d0301400401e01d802284101c007400801013800c01100c0306c12103803038020b450001c60080d110b141d10384e0f20328081080c003a0b8040155203007400040000b240d6078031152025050f080200c4c9864101707802 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 877174523 1250 877173273 877173289
    0x903090a08030c0c03011a012d03020a0809190b07021005152e0e03030403060903081009060b04060503060301140f011a03011a07030c1203141f1a0c010e0717030f0306 73
    0x34034502d0545d054a0001540c8a119000789c0d6002e607070390016200c2401d0800500420409008107070654008400216984040421000719503401382d0521002d44481c1c0c01a1f03d09015400048216424802003151484007a0284001c810085400207200c1c015013000404200b0140020064142042c28880c0c48500590038140300c2c07500076085a00e810b9903a04e485d0100c80c82d03948101c8c00aa103000601101c04100c0901c600602a1100200302c200e2a141039243c043c840e621422040c4000440051f500f90b90030741c042446003914068031b00e01840c0c4014912000603090103806145240460311204508910040d40d058403da4000c5207104d03042d480c0700310920b0b00100411010003588040b4070b80002c00c803031300e01000076070240c40c0480c0d0141ca1080f540540d0b10002c240340303610b200c0c3c4108280a0700440c41001c0407112182d6100c600c0b050008480e0070648921540c803440c540c240840509445400200d01e400c44481c40100c1680c21000c80d403d85d00c83c89500100311407117101b400031078824501554 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 877175773 1250 877174523 877174547
    0x907030b0307080313030b1627091407031b0e040504050c120f0d0c120e060c0304230307260307210e04050c070305030903090a08030c0c03011a01 64
    0x2101c09070b642e5051002d14592224002d1010b010f01613804004011803122201c3e0840300701e0110003400d074400301000306990b030000701e0b1000e003240329580c02c40c840005c004281c2c0504065001403254411002c01c5c401c1500059920400292800d0104186100b00090b031a07058002d5607100300103100790340c04120280001600984160150300341e061034075680e031107501080c8031f81c03030014104440d1210f80d01c40c10301800c01440320601020031104e80000e01941008004000e4904001201d0031341040441c0d0f0300e001e161442d840a120001c0d0101e0850042805086c030040721010f007030701c4496007506243d1521100e01c41e80d010021582180b602c505010183c09501c1e0401d102228101102d54a902501f2031003101082c120705000d0a0026015074002510041d524090707a06202508001210384a40d10501002a0030450041302098070f52409000315180f04c5801000303940869281d8011945a501c800c5542c5442d101e075800211442c1410b00524285c4100e072080804229511001501ea02080c08 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 877177023 1250 877175773 877175779
    0xf0504020702280314211b0708160b07021c060e030409060e0a0c050409090206040305010606020d09080105010f03030c03030b09090c010f03020c0c060901050c10090c0b090907030b 79
    0x80903414140d0b201e0300f42082c0f00c03142d00c801502071a20314201070769429400f0302134401c03070782008684403103e80300c85d403030b090f9a0000300507801c2e84c5280205400c810b10b550480c0760525400754900000310a0070009503030012010480c003540d40d03180d07a4205040d00d03224004000750041d0410581c3c00c028031200e2590154903000b02c1e000b05016040344440f0342143e1046d00480c0705640ea43c041448580741c4e01d28156032103090158204000c00003c200503089005074410000a2034890801d41c0031500c0d000b00741c3d4001c41c0c1c404000c0c06100e44400b80a5125075042107400c000072482e00000881c1041401000e0498110603000386202e410750320200d8801c0c025110980c145a2038825a02c6070791160311038680704021550241a4403002071000407d100c0034251241c04060060080b080e1101c0003041d08100d03042d0403113405aa40b034000b00140c501c5d010f81920036945000c1d22035103044c00341050300580d1010340325001508519440d09030803a01c901030365080d107410001c80c00020340210b010b5030049a811b0b20003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 877178273 1250 877177023 877177039
    0x50d030c11071404110d2d090f0b06180c03012103090302040b15030907030201021c021902010908070609260c010e0604090608030d060905010e0708150904050a020108010f0f0504020702 81
    0x14041000940e140c16611301c05004101ca80300547c41b0303088040500182c0c46150512940c00c440d1210f00a107260558050f00101c09407000c14440d41c1c90040e042ca40c65800c00b440e04140c43c0840415005030024494030141c0c48207071070b030a6501c030581c03510784a207554076031501c403961404c0d9000c2c04000c1c500c0c80c14054011184840300c04441d175804001c0c0d0b1181c116240180300890441c8002420803c003d80e18541c20401c01c603403441e007190007090039030703c079a9821707010000300c04607000482c2d01d070031203910941442c045e81001260307071a0b0143c011400d41d0245004455000d030f456001f10400ac0c030601040c00640c00008001d00c1030b611400c4c80745030700d282c020f03c0070b41032948071600306d01200c040341c1c010b01c2d4991001036030900510050040300000d15030b0329801c2045614009012031880801020032042280100001d86618407600600361a540c003c1d02c0d042c95450035250840d940c2c1c2c07200c0c1c3d09a0101d08604000110403143d03400312000d48001c00e030520501c910385814030000c2d4005100407640003441d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 877179523 1250 877178273 877178287
    0x6010b0a02031b1f060b07060b1503010e07110313060e0a0f06031401090605061b0f010501260f10020a11030a03150f2301020109050d030c1107140411 66
    0x14200c5000d40b800c80c4038026011090801a2111002c003902c034104c4540760030240c08104010703051040d142a42c1c1c010b98041102c02c8050700003024002d00305120f504c405004070000c00c00c00080e2030001d100e1000d64a620a040d40d008a90030b60b00e01444a11203144411084c05001140c0b02e00c104486001d405040c240c6000d4650b41040c1160440740c0210000990b0303022840d100e0b640280c1c50a00400000100308500c500300b0002ca90395104200001d60b59400c084071103104c0120410a9448841048000b04040c0d40c4078503a9041c1b8407003040c410191603031281500701c0d0320500803070101c928003010303030080031248807480b0940d000c1d4000b0581031003400310f00a80b0001681042c0300a00b62009569400640d0700f00300180ca40c0b0202d03a90300160b1120001081c28440d06e000d00314545001c0b45003800704000c0c4100307000100e01401241c00018540d0051036540445c160b09900800407000303450f154459003200d8103d0b101e0740d1764243c1c482e42d0091510060450241e003450350003500700f80e0040381035901d0300507 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 877180773 1250 877179523 877179547
    0xe060402220e03270a05060f04080d0c170307081612110d110c0606060702040e01090b04030e0f01092d080f070603051e06041d010e0c0604030506010b0a0203 69
    0x1c1d07596002c05594100181c601043c00385825103080c40b412005600c0019100c440c08221030f0345a600505d805580c00194421b004160701003503400404418040301c2c1c01480507103006020a00208044480646c0c0c5200c81c0000c0c000035060764031914041e80c50b981260b03235a4445502100f1a00200000c0c0007402511031301c220000d0186038000b802e10038000e5030703c1c0043c181c2c4804890862182d04401d034002c0c040c1c0d42403174030b01107071032500b1000454030240c4814850001400909260001400380d620300700404041114461165104502035143c100a1540d120140416070080c000ea0900041640000740f220112013400320f4800040d8010701e815a0072442003961500e841500b01d2401a880b03c0038848040808003c50006440706140601c4941449003410114013000460b800342030108900154941d15141d101c1e48c641c0080c000c1600d110380c1c071400100d00a01f50203c05003010b00842510403518100241258201d0350b004004102c907078071381a411742c080d4025004100840c003040000329006e0f9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 877182023 1250 877180773 877180781
    0x812100b030f1b0d090b0708010609151b200405100e1f030b011a09090412030e06071805040c0c0b0901140a14070c11040222031103100e06040222 64
    0x704001c00206440f05d4100858a450028003913020440f4130401402115440300c0c03410211900b100651400c542001015241000d003440860110302d40a049d40050018801034164480d070a501030104800c0d1079814441501c8007200c680c5d0b04900b44040c2000308921a07080d1030b0380316818403a141880c02c0c040405c0702d281815a401510000b007000014801d50365a401941540f1925805543c03801d160f5101003442047c00030700103800108490a0126494040e0b040340d421680d080b0169040c07480c1482e0064a070030300c030714039040b0b0003103090302c02043c10709251003083e100e030805840303542d8402095603c009901e00c0080c4030039010b540316807030361005007983ca43c5075006100b442804158034040a08120442d080100780e0300400c0040390410000c100b81044050810304240e038056520f1800c41081c0d042e11b00780350282e501070101c1031000020320821a01d048a03d6000301d00380ca18008440180f60203640c100c445411031504608042401841e1000300c1f08414511048040503082203030726004225 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 877183273 1250 877182023 877182037
    0x181d010b091302040e0615030d081003030503060d0c0609180209030304210b0108330604051e16020118320102030702011401080703150b040b06070812100b030f1b 71
    0x1f1049440d21a03064a41403005864038070b02440e00203640d20381070240c59031480b000c0c4805018040000007090954030348560000084d900300841c1d8220640d1148028000156441414801001784840e5001502135000b08c550b0340d900100158240384c10100035140c03505074150082129440c42411074005540d0344803150081600302c020b090400f8440303203940e080c40c220b8841503400360940012000c0380441035015682142050381c002a5584c2c032600c1100c146007100b4549500c035440201040041c07000980b9002000300d01d513000f80580e240040c48c0000104030040300a264201c1600c0452070540308101c800c8428020031480741100e08944209822603000b6148540140d440f20402054403640e082454010700c801c074000c02c829803968131569003080308540514412078941c40c030440260740701e8104606410300180510380d40da400e8542402c0c240d00a41076015048410380c00a0521032003402c0d0307881101d000a070100e01c3c40c0d03107800f1881600c0c6002001c007400403030340d01c2d200440510804007900c01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 877184523 1250 877183273 877183291
    0x60f050f0109030f060c03110405060a0c0c080109050604140105010b03040f1a01090218010f1713020603090a1b03350d0b0103050903090609010c0507181d010b091302040e06 76
    0x15101d0406c9004003030f504000742d40c550703a030002c00040000751522801c83c0c8524000d40342102c00a03601d407502404106280d0300108081d820142c0040030300c040441c42e2405144603100e00d40c86100047e07055800c0e40ea092003104402d14090000402080c4011103101e5003500c6803125808408600b400344e00401e00a80004800d19808035200301480c041c1454501000c4003401d102d00309601c4010004d08401880040c50200d103c00300c0402c0311a42c100311410a45a40149661389a15244010351380d24060640296841070b403003489030304031684684030305007980d8025100c600541400016001414a94404400007200c4407500960030700140004c0c054a001d000404201660100001815110041c1070010a80c10030403040805035a03190440300021030a0034803a8138070301207007459402c10181da4031100d9514417101050111060720391000318184000d5910809241e4224092400c032844e481045800c517825202041c10040c0e00c00485403410710003807000c100090403500007800d201094901c540 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 877185773 1250 877184523 877184531
    0x603122b1d0105011a071110050c060f1003201003020d0e010b06030f06180a06030b220b0603030c0714091f03170f181003060f050f0109030f06 63
    0x8005074464186410031440d290003480f095040521402d03240050312101c080a200025620003000004d02030401501d40c000c080c100381c00300f80d8401a0440c0c1c03120b821078020317000f1200001d846203e00200c05000c5d10745008445201c5055070780d2031410f44010901e10390380b01030708181001203a440814482c0c5d600c1c130750b680c05601c5d2840c052041c425200c1150a00c002070b4140814401c01b41c640d0f00a480c0c3c8401d58a41c100c080e0740f030319004078a010110070034071103440b03030081c003080300c0f0040c2d682100c4200d0380300350090400f40d03880040091954040815030a403142c48081e00c9008104911801d6410050050903039180035058002186008010345c003d11a0400d0a0014410703440c21281a96210031000d40e900d00350b95070040e101c2c0c038000c81e501009002c4580540c0c0011705c10404811f58514951003001607694560329480c81d04105411450903108440da41401035400e44030340900c4040320034160300b0610f402e0411041001000002c48200d040005110740080030401c0c040f1284981ca0007030900003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 877187023 1250 877185773 877185791
    0x311130902040518060903040e13022404181127031e010e0304050d060504060902130f05010602010c0e011b020607140f030703091203111609050f0603122b 68
    0x50170004002c1a06005400500003041601c0341c09813103640c007550800100d81401c03003620009250160754036001c0c4203c030900c0070000440742d16400070015240e0703480c00604548412400442079422150032014640c03800c2c00103100d8100f00050265164040c1d5100c1030003c1000c2c800300303107807990402c480310708600c0c0391601e040b50300f201707100e40e030700c08102440550700c2d00717081c272000c940020003800f00144020754504c00a010b100159100c02c1d5215801801802c0c85812220707840080c00c1d80250801103145800c000041081c014450032440400c29114110058040001580c4049903c2d08400038151400c004a0050b520b000050108910039045d20340d1803011005042d28000701c1c0c2c625004030b0790040200b540440e0300301c1180011100c90035400c80e00c8122038501250260482a6501841e10400c800d08581205100304441501e82405041169603910050004450350690381107070181c205183c2d07010991503c00040400c5003c03100c100080c514a1301d900f4801c04401aa148203840e5100200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 877188273 1250 877187023 877187071
    0x821090127020a051003020f0d0209100e01140d0618020307110d02060c1b010f06062c040c1826150a0b0a0905090c120703111309020405 60
    0x7031240c1c14000080c64a440c100358045010403066018503071041c48a046084041442501121036003246806840e840b5007007141448042e401c00c1d03210a00c5000040c202601161040d2070103441350300140e4440b6603504410030010041d6118600c440740954803403501080410241c11400404102d6490041e6685080326000702281042d1050411640103405503202e03140e40040d00e1034121214280340c5a42c1d181880c640994407481d441022010750070210050224442e5a102108443c81900d640d045101c42148160000409100c103054403261041c440c2c0c3d15040c15404142e400d2040d060503204017a502d49001700c1c184996000745040369400c0281108000729513000f00d0350144140c000d000c071031814031642c0081c603001001030320071130703035400810655a40b8004000e0003041180800c104d01e080c82101c550300c83d4545854180111328880e0b010f14004030026200080300d4000305c0c85030f01c0b6070981c1c0c10850a01c4115802c0c40780162104290340150f55984a440d0059101e414408041003580403c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 877189523 1250 877188273 877188311
    0x2412121308010b0a06020c01050d1b0f090b0405011b0f1707050705041a01030e030d090311010c050408060408030604060b0d1b0e280806070507110f0d08210901 70
    0x5850301504280701c0c01c1040b203400081d40c07e1031803400d09009480d0340d19440c0100c000d0020980f9140b96558000e41c40300f042d03421410482c00c0c2c03009c95544181454a8402c030700d42502c074030f2080e14009a6000c40740c0090034801d000c012810b900c140d110100359030320b5071289000e403a0443e0710b0031070300360000640d48104201004031500511742a941403042c203400350084022041d00d401041c1c14580c440b200c82c40000c9091040782c62041151078200150412800c004101c4581000034081562805409480c050701038003d44049810b110010905a901d40ea52200d16400140a90b078205480b0f04010941840105c083e1044000458000890001e8a10032402d002540f00c4400240107d0781280c210302c0c0c0b0341000171007900c07140006100b898541060402c0b1003802030b6001a260780600b82c00d0200c01d5030311000900e403080c001c82c1801c60422000b010442f100e400c80d05080d82c4240b100500d040010501400b4162000110114aa8142a81c1152080800d0440b440c602596591420000c08000020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 877190773 1250 877189523 877189541
    0x9300e030106060c0807060b03030c010608011401030c170715050d14090303060d021c0303060303230318030702030604030306090e0f10020f04030519020405241212130801 75
    0x4001e02c0351610345840640a0140500e001d00000e0000580000b03015542d00054486071026044035960025420405d009088901a40c0055420440482614001201000c0c1a20380080082130300600c2c102101c074a100034090303410114040c6600000d40c0c1082481c60050360740c070581301c5075030b1044640050304c00c0368074100f194110742d2031031410301130b5200001050b640d00200560b45002001400e000242190800201d00a000da986e0482030040503030542041e0105c07807283d1100348100c080401c0b03500117038203c0524040c40301310900001d03003401025400c4103041c40100d000d99103840540d401081c00d00c442100c0c25000f00307440d410308109820151040c0140d030002e030000b0305161058001019114441201400b081c20b030080f41407034a48094504031030007554000120b40c580c44842e002c1c2401444030403400e80c4140c0c0350400080c12201440a045c3d10f10307813410704031124810b49004015007858445002411480b9000316018810125401014141103419000d01c10314641852203013912500a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 877192023 1250 877190773 877190779
    0x1905070e0901150e0a02130f0305071706061c080c070626131a0103051f06061b080f0c0309130b0108010905090a06111804050c090409300e 61
    0x102d14201880f003400450305407880011520a661a800b0398000a802190282803070b107009410006482820490a44201c9104500381d0b0a0309540e0302c02040d022041c2000c00c8400c6c2c0100c030000d1002e181210108000084000303610141901e540c0f1650800d4202c400c8080300340d40914020302243e40c004180d403101c0010328400565100344200400d6800b04068502e091030904402e1800400003801c550f2620040840da00a4656a582c280559501604070842c1418440704482400307001090082d0010b554964858400e1125410400a4505407507841a10985020b11040c80020541310040c440c0345680c000850311807407901c041040d8281ca00b03001e10030485c0742843c00c0c0c0c80c40e60440c840d54110340e4001740c00a620340d030340b68660b420a00c0c0c5860080c806440c2c88404096030540c500900b03c0c3d2504440440501100b80703041c041140da090700c00c4440284140306400c030515143d00040b089600c0741240c86134259011817111196503c03400d034200d0b1004a42c079100140e0f94040d8000c000001c0072 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 877193273 1250 877192023 877192031
    0x70503090f030c0312060418081312020d030f27060e03061b0304030908070617060a0326090a060806130612060e030910030204050f06120a0b031905070e0901 69
    0xe80c0f48280c0d684103410503a10f60502c51720010390b060307840754030404901000c810503512103401490510301540c0403100b003c6040701801d001180c600d09114098220341e6000d00102c1c407945840d2000e0702c0030907192070003a0400c0703a00c0c1d9600c1c14909240780c404640d200481946101035041500182101c0d8042c240240030751b000104010f90280401620000c031034012150507500e8503181400c4406060719044424684950741002440942c40421403440a40c0c0d600b2100c071a03200c41040010322010b030310015114060000c140c06480c0843e020720002d19012040d014030b0500130002203aa048181d90200d4042007840702005154100b4121a8004c985100030801c0703800c2c105516090080701d584000343c0801d68503c013250071210100b045650010000b000840514013444000f40a94003038003e03a4012401841441c4143c2806d0060704e22400304601c1d03101c0c050b59090760541c000c2a0030010340d50b152254042d101450418207445028890084021340201d6050013006018050090403005003a858 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 877194523 1250 877193273 877193287
    0x140f0604020d0308040c0b040b09040f0b03060601052a07030b0c03070906140c1005040c06020109020f040b0a1203020a21020616090b0c10060803120109020901031103070503090f03 79
    0x20b0540000429a41410100e866440350300704203c03091709a800401059800040c04103d2003003040c060300403444101e40c140705401c40162082c00703807102e142a90b605a4040c00c08031300705c1c0d801003000e45146010012a01e0161390720480e070151540e40740c01402245e4100345401c1c010300085480103640182e45c41e003154918200001c00409d80c0703506101c5c01d42006150310040303041c3c010741c0046900c04c1d603408045503e040f0344c01d40003000030300c0c00740c400301e17000c4200d40000910f05006001c0c00c410300d81c006080782c06078120401440081c0c47c00e030b600d16905c20340480b4040740e02c0c003016100407000d0b0302a6004044002c0703189401007016001000c01d0341e000f5101e020741c00304a07500003052503020500003100e1144030703030551055900100540090354a0000800c620555540000703101e5825008101c0901c007003075444030083c3e140d108881c24103820303607a2100140007510054000741021901890b00145400d0701070a040000e800950b86500001d40000c00e000c0803030b0080244643d510a5040510301c1c1040c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 877195773 1250 877194523 877194529
    0x2130b090403030b180406050f01060915080903090904030203030f0c1204031b06060803130902090a0302061c0c1e021b0d021825030b061c09020d140f060402 69
    0x10340108001d08240d211316158885840c5c01d030028440c2d0910a4904441c0e0826150510243c40101c3e00c5480509a0b500002041403048083c4011598000c0d2680075130518060202d80d500401040855544801c00052219031039004c0541c4c070581c0642d010315107908044519064084020b00055071061040c444140004445c1c3c5d04190001e40c54240745900c0c5900b140031190024100c14003403d003516003200000e1030b00700440140b05900c083c031001920181c4649100d01240224001c16402000c0030a007400103040c0000109035126156040d01503900e40f0b400710b201681c2d406603480c0c0002e000da0080d0200f001e206003c0c1c001200d401d0003c1e0030004100300712440c0702c44820307050502c0b5001003141c0c21b0964480d51141580d80d0008000f0868a160590b12a14507112841d041c140c40007280301e2310040f062080c0b0840740301040c024101850403441e01c0c0824600700745040c40b000340075994142d0b6001607480c0c80c00240160702c51210300442c4031600504074180150920301c2c1e0040e810540c200001038ad = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 877197023 1250 877195773 877195789
    0x230a0605072012070e01081608121b030a020106140904050d080615030a02090102060108150a090c1701061701062105031b03040504200a0e0609040c05040302130b 71
    0x2441c0440300740c01c100c4200002952a40c80c3c2c80c2c115003540190720012900c0c00301390210b507050740c103610215030030a01c00000b44011031409103d5800250000c050f004060301c50b0400800e200307071024500c5220f07451a00d5a2609507400101d990015030b645980400541e81e0400b00741400040480b40c41c0c0d65882c0c640c0700e03143c071094204840020001200c1c0010340c503a5480c1205003d0b250021580c584905e00300382c0100c003d503c030340a21800340c0310300d000010f046c150014013030481201c0c403040c3d00c035541c075202d0403840038040481e0121103680560700003055600700340d0340400c269100d4000200b000ca00d0080d4480c28801e44011581207030341005400d01000000c030300401c0d203000c003c440501c207012003800e00314154007421640728004001c0d0090244040c0b40000500282c800844007003004030865502050001c030110394400c84480140301080c8501d010ba2115480040d001d06000d00d0081c10000180850301c2c4084414041007012a00b4804c1d41130002c0000203810098608118050300300d00000c40107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 877198273 1250 877197023 877197053
    0x1d030c0609072408090709090b0f090105070512070903020904261e0f09040c0c051507080f310b060a0b160809041a130c05030718230a060507 62
    0x101001c400411417440d170800907a801050ba20408000c035015074580b40015603c183c4041c88000c07035800200e92400b4040c070519014280341c2c0c4901d454200704220715155503c0c020b240390207005142c000040903840711910248120711505d8165060003a0200c6500000003008c4140d0311844240b02c1004108000c0c81341e07072529169088850384030b0384d601100c02094426440425002401c010703203440d01c5a0050b640500c0b0610610640d108401e81c4200e050150001701c9414001614540202d42c2c03034010304050301d40180140d072100860203150040b50311b08221101201e610b004800c0543c0090111540000341c1005084030b880900c00e203414124843e5000ea80d80b04244112041ca4840400c90004200d40b40544e02a01c10b10030000340380d00800075003401c50920313401100791141008407079840d0b100d0a00d200e841d42d21180e0454455000031100b200f1400205075146001e44808218550b0152051400304c0e28008000c40c484c00400030f000801701d030b550014050150501210001404128600c290703 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 877199523 1250 877198273 877198277
    0x50903160e090d020c4e030901050a081e04050f07050a0302030a020405180d0c06060b0a081b0715060603150b0322140c0108061c061d030c06090724 65
    0x543c20030401c850f5844082002e0795117400198100d0580d0038100d0700b40d03620b60201760588442d000340642c034160f0b1f22845038406142c0080c100f081035223815406550701c90380016010041050050f48910102818139007a9026a5194818080303461164000c00480f00500029960b034801b0fa4a16404a9610960540024132072916600010103004075081e80750924a45a01280e501100f140006400306002c0401070342c1944c248034000c6051807043e001c8a512584a5450b0006030b580c0708bd00c1d2129411148150901060801600e00450000d60405c0149030351f840f000100710b490180042e0407521421607038001021684c2040040c611058183d036880120007511854103203001b000345c00c2950412070014000c280c00d1400c82c10b4040c0000744140b0380c072401c0e2520305c1c00307032030f04010000c003034600e807a04240030f1545051030707c00164950411404807035100c07644883c81d02d0400105055410a0240740d000ea070100c801c209200d0300c00c0100e84010300110420140914001100ba20403c03a45521402 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 877200773 1250 877199523 877199539
    0x3031f080f1c0203090a171014040f17070602130e0717041712070206100f05060f1e07110409020901090504020a0503010c0207080105010f080705010f050903160e090d020c 75
    0x83c0c001c1c03080312502080142005040c03038840707400442460004c03411000c0c910810074174007101441d502c100755560310941c4040d503441e80c40c0d0351254104000800c040318162500c410490142c039849003c0d2210f10710601e80581c0300c4c0210300c88059143c0e1540d2092a088a0714018070124940000b01c40364085800704000d40359540340d00703103a0200329401c500c00a1007440003641000350545488514003604065080e2585611a402c00035a030300001d0041562032100144100b01c686400d0008000000001181904200c44159049110030001c6050b454040000608108000944212021500d000c907000c00c401c620b01c0e000f2840c11101401030940705683d03000410203544d02c40c15003400511008009228022800c1c100a4070b8000342e2007400810b600b08800410644040000305040d103e180c0010060103207403000458201d15103035085800e2020820070080e003601c040c4003070818071203102c684500b502d140402d1030003103000c01410788045030085400030a0032503001c624043c105a044400127 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 877202023 1250 877200773 877200823
    0x1b010c2a02090103060e150702120a1107080706110712020609030a2a05090c07060209010519032009030705090a0f020d0902010206101d07090803031f080f 68
    0x9001405a006944858404000801c004c4c3c41d81107a1441c0c980002521800200c0c403802603040e69060314241d0141e08080d0a070b00b140e00c83e070300292200542c1403528444000881070cd403401c00712241c0161b8125004002c090000c0e580008a088070500c0d02e1000b84100b0340b514604400282e80d44100034885c410004a0007100e40c1c0c10000242c003541c2081003040c522016041440c8410003801188041000094000409180040c0d415100395180c1c070103203190070f0040d5a130000035130049450302d05001003400f460342026a0113007034544041d680d032000103a001c80c2c07000c1c1c409139a0f03c2c022407003501d00b801c21404c0d0980e02c000c41d080b02142e0050f034503203c19413070f01c090041c0070704046d440f80d41680f4804502626aa10907030807071282c150003178080c2c40c800d4032440c90340302051440d4000c03109482c440300d1095011102c0451040d6011059140013a80ca82c0c450349032904552050700c0c1025203188403164022400c038608003000082c030503a4001c00a801c084140c0f561201580100000180072000c804 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 877203273 1250 877202023 877202087
    0x50708010b031b0d0f050402030d02070e0604150b04060906021b030a12032003010e090a0503040608090a08030103030e090a06122a3317060312040b1b010c 68
    0x90744c1d11350070a01d0b060042010703007074504004182c121001c0c1e100348100401000700a00102d12396040c0c8201c18451070107a50341009000c040e00048000d0041d030381f0340360030001e180110344000c1c1000e4030041e42c0b1a01800c0c64a01300928050641e560381c5940703c18000242626540040c0030700405a0001d07255600c03035214101603000f0403c071400c5c44032032408450503540110210340154180d48440341c0141280c1c6829001d15560050b5001c01850b5905c00c100521169001303448850b030109801c400c84030a804035541c5d44189410a0384210045480314070724600314607021b248254810b8155104015191906000c000d40740c0788040301418640c14420a03c406201f032100b420450000d00a42070f4506070380e554080725050440d054110403805415000c0040ca11210f6075010a4980d60f480035560700c0d10309240e2042c140007030000c0780c0c54441c19900016400444002e04010040781041c20384130002c1c131440c16044030446142050301c0e4500b040b1461a50b400c00c03c20680d61643c0150007260020748446 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 877204523 1250 877203273 877203277
    0x1110705030d05041802130e0907050d030906020616020d0f02071d010501090e100527070905101106011202120109050604021314010501030b0307050a0b090103050708010b031b 77
    0x314079054090441c4845101d60040020000c440318000103148003002c4042c00c204901420142070117003680ea4800300174203c11241c003a030b004104442540e00c1d095441000a122002510701100441d528010800c40250180401b990181020300e50081c03010340f508009444148000d901024451b449840380c40301c600c20001c600107071880520101003041508404031401c2801d1080314002024180c01240a580d070405050241c003e04e245240031b03904280812940601000b0742075a80340c2c00c980080441203903103c0c3d041c000c0c04281c1301c2042050800d000e00014000b140400b2050194000050140d1200084c16034111a103c40403084520000c2c0300040c11a4803024002d08158248031102003031002c04106a400349108035000340e51955110510010b56044100d400300801802c0d004004650083d00000894800201552081529400051300500490b04804a59140420f00300441d50301441601d4100100c3e06014180e585007100188445c0b20027040001d101034003980d000e03500080041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 877205773 1250 877204523 877204529
    0x10f050d0e0304120618080f0f0d020310090b010c03171515040501020c041b0c020a05030a080910180303050a05130e07020c040501050d0605040206040302040c02100524011107 77
    0x41566912913a400711941140c120305400d80e10189000d01010702c448138884d440303448036440040f041c02e2103800c60080e0025000042211490700c0c0401c001092001d440c40118403502d00d03240800345076410082148203d44680f45d095060188811120300802d80014450f00c0c140ca41c81079a181c0f6550f82c0d001d072440035800c000c407150405c02c0301b05a60940c911010240c4180e603020b030f01300c07041c4000c1082003200795000c1f240964050009003603d4003a280c450456000801d0014000d1026207983d200400c2c03900400d00030503102c00c070300420a950f06141c6642010b0850100e45030040d5400c807243c41d0b000c180303242440010282308001400400c014090410b5450300c1c1c0b071241680305044e58506074002e0304842113034500018001d00c410700c41a45490300c00d26061721000b804540c048030f00c5684d11401004040c1050307a100c1014040000103a50f103000702400c1d0f48055015201100e000c5603403c003901d601074105c5440ea20700d4a407603c000000401d003400d010a00b40790940e04000325280090820405030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 877207023 1250 877205773 877205801
    0x3030106210912021b061903050601111009110f06040608220c0302031603080d0e070e0106020312010f180b01030207021e0a21020d2414011202010f050d 67
    0x1c3c1c2c00721116008500449134108254003108108417038020000c02c2c1c424000801d4042c0442480d0900903407082d4049984506d041c180a0071140d07010300181d1070a40603d034040401038a0311b0130742c41048810f8005900244082e62a618078200140009020380558014071040060b400000f481614042c17007090000416030191128481d0181481d050740101408164001c0c07152850410080c10a03641880450382c019008a04141160394044098503400ca103030300d040e02c100200420001c1c03c2150490080586070000c55031410784030290041c050059000e640f0441c07032407004000030024001c2c281e0050710301c9040024010781c3e00700140d0090049040c042d40011a5102030254940c070070441040100e0115045030001d9070b1b80107460050004040455003d4211076042da00508064205c4403015106040c1301c2c0000c8076044003590054414280308203503a8031341d400c02c0020b00d0b520304442d01511041141c900e48030b04a8001038449800f20741440200400050011102c0d500c941c010030a5007800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 877208273 1250 877207023 877207043
    0x50c070b0406020d143d090b0a0b13031106040305060f0105011202130e0c0f120402190308120604020409140f01080607140c011d0a1103030301062109 66
    0xd04003007000350009000c0f010014980190300ca2170240008241c2e100303044e11611001501140c0ca03128101c40441c0350b180b40d40a0310548131280070300b183e919050160401c01070004110300c080c820041c2000455000760400c1104009a25825003100040c00035a80c00000c140003c0500e05c021511502c0390368800740c0b0a026601c140403c0c0103003052464100d42091380d4048225402e048104103d00c20100016110040da000410142c10a080c046500615441c00c0e82c1c208108082c001400d40c0c803c1040b901c141c1c0c4400304000031841c256401100603043d81000b00c3c0058290b659401003803281c0c0c00c80380b030105480400180f5585c1d4980486020380044c2e10140b14100030071090201400b815030740201550080c0002190000b0002011072059407a951040240044c40da00709125911070b110a803c1035413150028801e5031900078043d5516044038004010315196810900030210b528070380b803840380d041000100704141d40038050b0015000714600c0756840860550402c1c00070001808010490686 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 877209523 1250 877208273 877208281
    0x3050c120a030c08071409120f0307030c120302030f0f0a0e2515050f0304060e0d090504140603030d0f020702040603061b020a050a060c030e121c0915050c070b 70
    0x2154120860700d03d0140c88600b03042d140c40300c4c1621b10100400003403140440c280000c81280c90454075840c000c01d141801d4402d18005900002d00751b6024407001c0c2c001c50503181d10001040b0700c04900689e500b806107411411410f041c502108006005009000841002000b060020509910500d40034020100300c80c0c0e20a180100c103441d2003002d410b0811204000c1c0000541c020b08140e0b0101c400040d603490a1804070195150142d50700050020358520740e8a030390000c070313501d81040b40d10352001c04c0ea02c40185452501c42000b05460450303405240545842c030900c40203803400000d442e075001624901184c50503603060014002c6c0244d0101075809414507400206002d0303141d102c901041070840b11901c000344080001da9440101c000c0003800e035807204103454040340040d40300142e410719030b00d00801e050b0f4a4055652800031006844401410002000c035004100406004051203400ca814000909503803074000d452400c05412080c8180c8560001c0d14440244c002c58420550003070501e07001d818 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 877210773 1250 877209523 877209527
    0x1120e0105060a050301060b0a030518030f18012309010c1b03030314090a020105070c0b0a020607180e191401170c0a051e040605030f0c1e030a03050c120a 68
    0x21082d00c00c1402003111603804100e90038180121000d490048919a00c0e100303c222044004050042030700c03902e170300081c1c1d0308030843d201407005002038030203507190300e403158201408103e544280e00322440c14422041080800d2001c00090010385002d10b4591a072034a15140050310036803d010f5004105403502c844122546c07441130448000d40e4040c0c4d500300710261130459138003130900c000d85401466a011a02980c010340c4680002c10055203d1440a614241d03101402c0c212508510003d2015800c0f40c0208170500740c0c03000070301c6001b0101603400010545005001a0009c4000e4101e1000004020030203028203007035003084bd1419000201515103607900e49400d404615084100b01241c010701c0710824086c074060803403800359200117040c10321340d400401e02c0d58541c000515a4030b07002601c4000000b50785d41e09000e401d42d50680207001d4185080390808003d104c85290804801d980c0c2e0360b03012601240c400060300716415601d418040c0e036408040c008107240c8403141c00600d414803000280e80d10792903 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 877212023 1250 877210773 877210781
    0xe0d0c020f062a0f07180b0d1109100b0a0e061b101a060307111c0c14060c0912070e0103060207051006050f0402181504030b0f06090f040201120e01 65
    0x10350601c907010072900020b50000d0711044c59803501c00507a40403450034850400c0d000040d55050000100003e101040b101c041240d8059414098440e270f41c05008403c020b0421002e5254003400c4c20980300041c50618412031981d0149146050400894442004d01501c07104102d40326160021030740c03c010395082051950328811003c1d0820040c5c2400034940440301c000d4405110608010041400c1d41d54044080352041071004440c0c80c40c1c4625180080781100116100d0a941510381d2040d0640c201410b11800460941800c6061544030808006070304178004103031070b40503e04444003008643c0c00180180340030100d81080c000007502e400000100070307859004080d01071080f002d4400310b503520a0440c4c00c552039031042e6504008445070b100003918150740101109041071408285006240c004038950f03072500c4400003200c002c00a0140280003081d80349503440701c1e602074180070302e1508001044000d42e0181ca0580420100c4d4041021a0300820740c507070900004800c10040707030228008007800380c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 877213273 1250 877212023 877212067
    0x302090907080d030b0d08030601031b051e07020622030b01060c0c12020d021306090204030c1a03071b0809091303030506030c06031f030f0818040e0d0c020f06 70
    0xe126500b100b03c141e5000b03015403030308900b00414043c10740c0d05039140c041244e8001811541010342c2e810750090144541c10740c103c10464a945d8035600d5800c0c2250151150108103107802506078180304000040e40c84074221504201c1c0382804450130581420100312411058000802d5071002d80300214806da030000c2002e10090080480c40340b00d5640300060094060703103002c00f079000f11405602802504000c0c40d01e00444050540014985585004200490f042a041101d0309040c20034100300303440e1400042105100c0e54144c00d481d43c101580042d20401400f20384800018a0070030950611034068103454902070003401e003407001d180c48116640804104601100807901d41004100b50b8240040c4414604002030403080c03035507d80900450001103d070045180c01c0004c00300110014900000d400c1c80b2600c900c0b0003d0701c0342c403001c524400c008100201d2a02540c81c00e14a031945950000fa461105040c0b03041175a45994140045020301c80d42d841c0007a001107000070542071122200084510b0307 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 877214523 1250 877213273 877213289
    0x44b11041706040c120209041719090305011416031a18040210030c020d2024090604030c0b090a210e0f0d02011b050a2109030213150302090907 63
    0x1801c0c0d00c5041000c0700d11704081011f5009441400040e00164617001d240142c01c0c0413048e95410400c045101e00c0c100080c291078036002500c2c044040040001c00d005624a207900c494103c03205181c8000c800305c01e03034000e403046803c064540e40560035201c080c0340c5403000d500016010150422488482441e0b24505480c100d0060800c026036621881c03191180c064030440942c080c01c1800c41c0b100382240d281d0100030703440c903e0409000c20031000c00010000c512056142c901d06441030b0030401c64034101c0b510000c008071900c5c2c00220801000030f074030201040300241d2088826601d03846d6660107924054110300300030400c07903a28110510018164400100701240ba65901c903c094015083c0090340394107100c1c030f50300411000d05800c010340c0114080c2d25030b03a104d0801252010015186d05103051010341041c2c0b00b161802d0301c2e1070f29015402c00031203564000b5051488800b459540400c4003802411803441c0b400d5900c1403a6075244c103030387c03a910780116002424020642003559841d0b84801e018412181 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 877215773 1250 877214523 877214543
    0x7051c022803060303050409020702120114160e241207120621060903110102190801170d03020c0109050f24040c030b15044b1104170604 60
    0x1100d42d10034015142560744c540d403050305040c034150140c00a5040090100e90050501c000f071650715509205109201d03400030701400040c01d0400c0748180b041e182d144c40804010840328804019141d244281c42540c908a601051142c42c120b103054060003950040c000241c0d20605002c0b0040d40003001050440c1c0c3d610f41000b000d0b94401c03a121a41d020111604007802d4042da0714404199150311880d05c15010707017002d401aa01030040300d0b003241c1c85202c00a02400050300c4d035161040e801401c00e400341c4610981c6101d01e21070b4130b004507501c03074040f01130600701600061581c1039828203410040c0340c4c0d5806411100c50014151090341c07100040311001c2d158404006007181d00420480825010700e4200d5040f1683c141191124048010000c08252103411044001034041d12a84900e9528074107515840812401e0072510250150140080b040e00289074401c1c014503041c003500760010291000d10014a20809403c441101c0c02181d000103201201101a49143c00e00410070f00d00c29845010300705 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 877217023 1250 877215773 877215847
    0x21090705010909141b071703090c0103110d0e0c030d08180303040314070501061d0601020d0305070518190e090f03130b071401021602030f1507051c02 66
    0x4001c440e4404c82c01003160101101241c461480305040121344020343c3c0c4c440703141207225201e0f07515002c007040842c82442c800000704858114180700300960b804007440c041c404064039101500040c02040401c041306540e0b01d400e9064900e0401c52024450000340589015004100303020f001c4800803600840201000c0e81c2c16502e1810103c201d82c4610f51644512050f00c5004040d1032282d000484200c2d03142d0745e114804159160423070010701c1030b8a10302c000e4504a1914a00090a04808045842c141420101030008094001082c1c1d5485040050b0001240740358100080c590110303240744d0fa0030982849404246100e0090200d0720460340301341210a0b40e0f5001d100c0c40c2c1e880c0f090240486080c22800c3d0203010b0203e03603000810740c1900a00c0f4000e881388100c1100c5003281d0081040708908440d00106000314181400f019005024007030161072100030415120300ca8003402080704d01000b80028075840002d4010083c0e0346d000b16030141c215100c0c104103186100b84030b014180c0701d405244940542c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 877218273 1250 877217023 877217039
    0x902040c170f01030f24061202120703030914061b0a0c0f1508070c0510062d061115070c140619050c070b0408030106090506130b210907050109 63
    0x140c1283e5202031071801c6030880d611000301c01c02802480b0b02240d10f1005a80116480d280620b0025080e02406904825568030400c080e00b81140c1c0e031048680c02000c0f0410210307400004100440b12000fc240c10810000000203243c1d1107000ca400640103007070304100c008108000348400c0e042c3e03c540d08005080d900c481c1811260382503071149445200348000c0d0b9600b035074411a05250085c030a0f0400240d10012030b5982810030040e0b070300300d41c54144c0d00c038020090f20306080c00b00c05488000c000d50940468064104022100d01e500400c0300b405400301c0d2849040b40304229503440000c5654000c00c0c0e90410407170080540f0510101510416800104c2900505002c1856405148003c6460a1400c12811180e014200041862500c00c909110240c0818181c034800391082d4881c2a100d941c3c0d40c100117002c3c1400d04a07400c1140a2481881032a0075048101040c1c0180d4820b140503686800641c03a0b60b078484204410280342410140080c44850000002d2120555100b6203408042584522070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 877219523 1250 877218273 877218301
    0x10e0405061008061501030b090a0c09091a151e0a02150903070609021c0606081006050a030605040f170a031103060a030305030414070608010602010b060f1b010902040c17 75
    0x240c4200d500302e07030301145e111505e51540050a034010704010808698a4000544984088420b000c2c0244c0710051120960381c0310f0300b408090140110f04210043d10300e03206480b0082845402401480e40d48440100b03074000d8029141445040c00c0d03aaa010305418000540b03a401180000740948640e090712800c410103609464450382c042ca00560610001d0303240c4102800403c5800d0303030400c1c80b010700b0b00c4c80c1070351460500301e50750300540f0042146468402da0515141c0800000c1000358540304007840556a40030290301100d810400105480e141d500b01444000b100c420024445c02d618071a800c4040d0214024082000c01c60720100030010f402d0342001380510007161100d922203180700081c80004d0146000c0d41d0814020448944045a901420392400d1803c1d00082c010401c0d18004011313540e424019840d90960a07150275040000b0b020804a10f80108002d40850084a50b4204c81a050961000c092107800500c10302c1900c03000700c1e000d480105a003201c1e100206074040002c2d040d85488034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 877220773 1250 877219523 877219529
    0xd09051e011e0507030603080a0e120a020325090c0905040f092303090405100e1305120702120604060b12190f021908030904292106010e04050610 64
    0x3064580c0b03001d030b55551500410340240b0000505a8a2030040045244000034106084160b194100102c2d110001c006c00208603001c0401160b1110040310016180030aa201e20300d00c503034443c14440c4003039070144101034042d904080600303131038003001c0001190b20181d070000312076040d03c04011800d5411000c0c0207580a9907406040505a4201d115242ca0000d10030149592900183c0b420003c40c1030010f01501d006a8099407141101d80081c400c01d440c0d0000d254005000e00c59000c1d01c0e010540c1d41c0e0b40c840122204c41c0400036804a00c44c02035445280000eaa40c0c050302066034200e25182c5040300041079440c440c5401420307a1030700c2c4043e611001502c00b2445081e0b03081ea00910f1282e980d50303c040ca13841c250032a008141098a01c0d0080c0e076a55800c0302400c03184002d03580301d4040b03006210450f043c001c1079001c2612100070761a5411680103014842410035502501c00e03030036240010184600c0840d10040900c90314000042400c04d007003506010318030070340175100c1c6916100415080719100f80 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 877222023 1250 877220773 877220801
    0x15120717071d030f0c010806010c06090b060306070518091803030901060e060607020d02090402060702030303040b041e02010e0907050c070b2a2512080a27030204110d09051e01 77
    0x200340d020741ea6001c0d0441e1fa5000b03005151030055100590f40d440251203128408452038041a8103000151506101043c0e00004a10b0101d0070700c900d050504072040c00e010b0911b405001c0c00b00c0801c445420302c607043d031100d0101d001100d0f03903810010710640c0205262b1051618000302c610100e100b0f40303820350858a8094000f410749204106640030040402d2003c1c20413a801903080200d80010b850038070140d4072890241c1035400f401c1c40d050030400881f0045214035015108a0b0002d00b0041c2c0c2c0001c400415144259810702c420303070351b080c2c0650741442040c0f03000c9407a00c41c18030006140001030000b01005058905901105040074900d0850302140030314540103600180c407901e607043c02d03100e490041d4000110700b000400e9540e621719503007085000740942c1e011000190b0120407039046400b1410017000d0041c405000396204501c01200c0b051070000034459030b103070b8000d80c80115000080d140a802031700c1c010043d110003460980c3d0f40340d0081002c46440c4203040b6804200e91018400c030001031847e1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 877223273 1250 877222023 877222033
    0x5030702010915210e1606020c0603040f06051504020d0605151206011409041803110d0f03090c170f0708030c060c0a17010603150515120717071d030f 66
    0x182d0110611202c1c900d004c8000c803075481102407000c043c00c118040a268081507409401c0e070074040020f080c0142c2c17400c19800703000208240400200c150314900e20103074104e00001003c3c0c03070394119161004404c0041942c0280080b51441c071003c820b81c45902115000c40720030300a681c0300c5900d0341081c092a411881d207000300e2070008040394000d198007403000c00624022483c00142c20002000c42d2281201070f807580e504040900304064001d040700b148815498000c0c80358400054004110042141134501015210180403003004201d512080260040b491a04c8a40c940c2c5040c2e20f50364481081c2040680c0725090000640941c0032048902401d002000707028540e607111426415940310441110400c01c00d4080c040301110490b0109001e00842d0391302149200c00390b88650144155a040644244864416040d02e80740700d00c00c4400c0c407000d54544100390703603510800392951801c1c0c0c02e1800b01121400d080000003039000b009103a090f0302d0720f000035448407107030400e140d95004440c03420110781c1c0c06 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 877224523 1250 877223273 877223297
    0x17010306050603030f0706050105010f3609020f0304030206060a150e061213051e03121f080607021c08072a050309040605030a021f0302090d05030702010915 69
    0x41c0d0441a030220018003120300e081c4008418100c1503100d040306032000d950741c0006001560344011800d044121520302150040e00d18040b01c0300d607900311540202001c446503082118070001900c020010091501c00315201c2000003d0508285c1c030850301100140101c8000406629109a0403020395031010f034601c4248260007825500648008241c607440102440111450005c0000182c4a072030902c80d031103083e80080c40d28521b842d180f05014110380040144409a90710004141c5084146034212900142c8422203006241c1703407084031411118034181004a01c0c0b980004182d8014100e0380d080301c80c003407600840620000c461071544d00000303550300049807203030348a01424503100514000c1c1962810000882414554400c2c034211250b4001107034003441480c003441141c00800d42503003c1d0031201e149a00003a41d10301e950952180d0070000f0007880c1c80641c403d50607030302111401b07003c44800e4a01420000e03540d030413102041b400210807039804501c1401d81808202d8080b96602d0380400302c01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 877225773 1250 877224523 877224533
    0x16060506012606030a230c0306090c210d050301060e0f1509040f05090a0c080705033a080f160f0c020301200403120507030c081c11030610170103 64
    0xd4090716003540345c442d0300102004610ba600c0c95011407625030110180704290701400505102402107401c1c031940181041107400700001c14008490341003290068651070000f0034440c07d680c00e40d134607443e1a100f1030748800d05481c4c0040045050300c540d6104c041b50242800300b001112200c00000780c0d08441121260840d004010014080c0050b0040000c9402c54900302800c2c02c43c1d41c21544a00a50300c08041c802c00d00a000c581c40000c2c0c4840c07000b90411509010100380d54a40160551801c2283c06030b034844040018110840c20243c04d240040e15002c0c0700c403005241e21001e1f298005450321801c086020038502b0480c80118805a0b00c0d0800c501340d00490648004a15200903600f5540720039075a00c010394188045901060508402501c450071802d004085a038554400014403100b00f00c20b50109401c05c0704d011680b0342c091496030b40e440e551514010b00e90f0b5401e503003170101c0e030402084000c0104203401031440f0300380507a2145034083c4005421520311040c561000d5007819a00014404a1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 877227023 1250 877225773 877225847
    0x8032406070816140102091003060e13031709030d0c030504030225050a0b0d05010f08060a150b0309010e100b0603060d06020715060509010b03160e01020c061606050601 74
    0x503d025207031000303c0f50b107615002e01102012402c1c002c82c0c2d40c001a146075074504003840038101034241c50200107160801030064a50301d4050600101c02c00c1e42da03140410103120300300c211a8401c03045503004641c241500000da0b41d400158249540b1404e00d068610302901c288186440b4a40580c000c0810052035450312481308690282e508203001d00403404512074888640c0f800c02040c12a00c80303503885041c240c1c403400322181038106103500d802400302000302c0000090035503006000fa403030008d44a00e04041c502400300c2198040000c4a101104215400e48103501c82d082540e04c010586411400003000c2400b00d0b8510324174280e00c0501440800c00c4c0341003001c045800da0b40310703620052900c042a101e00c0035414440d2284c984103502e45100740400c0c101120520300402800d00745609609100140b5540ca85c0b80d1210141009002c0d01e0107020345e0b2082100d691300035005014955511150440c0000c1e0041c43c0c5006e0794018141004104036510075a190f03000070503100e40f070240005070160420040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 877228273 1250 877227023 877227037
    0x13030203040504090507030b100f031716050a020108090102090a03030e060f04030c0315050c03040224131e05030c060f04180c03050a0522021507080324060708 70
    0x520041c08080340c0340c0c0b10380c4201000300f030140008205561852401583c000d500074140e070001500f03200e007000f080c03d440e000c0b102500e50008140001400208090013136001d441035107260b000c2da0605140c1440b5000c50b59083c4a4001e90f58101e05664440000f401e0f4882c40e0402500006c0e0f001c010404070344035040c0d00042001c02015646040c011294891040d00580c0003030311a5243d02c1750400802c85c03051521480e080040383c0c24046490940620440d81c00001d0001c0d00444a60b00c15000c0e0a03448010420300c0f070a041030603a1200259002114501c13464021808034070380c40c002c0b070081041c40088030402c07100001c00070480306110200f84035540c1c010f450b005440d99801e02000c40d030442001485c44580c01544000540c6c0b4080c0d400007015180e0103042c14880ca072800c400e00c9032110014421401078003401c10209907607030441c4041010100d0a090f030750700c3c2c40d8011600e8410400050000c600840440d5080115000c0301e0080400225a42c10426481001080044005002e4030f01070561 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 877229523 1250 877228273 877228277
    0x1306140a1512020d06060528020a0807060e060f071101140106030c020f0319030f02070c030605090709110406090602030309060a200d060810020403020a05060f070f031e03141303 78
    0x404c4074003110702e819079501d900803201051010403013113141c441c0e04038486002c00d480309290f0030406071076901940303400e619a0b0140901d10005802c01c14003c0326000a40350802d0341003224654a0700303042c000c14110b02551540300150b80041a108401c0050160401d030301384000d041d15a40c0d19184081d001030058484440650207400c607034a000c0b1300103102030290f00f80090703010100c81049100c014111106501030070780b181c4c030501000700420a17602d082c800340c9501282c00210380d10703224120351800c509580170305091404c0c1980036901007142c5001d00100c8290340c035802243c07610380c6810398036070004907580002680803000003050981550448102c3c01c480c5a07080c0c0c40003404d150703180f034103078040c42d14681c400791a120300b042024020004030000403094036086081a055070300003402801320303208580c40b0f100086810703075410341d00c03000300d410b09640b05640000d14800c610300500340170551000c59001c2c080f1681c400400da4000d000301d04c00030f402141400e00580da0307031290380f420760301024094007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 877230773 1250 877229523 877229527
    0xf0902040302300f1c050a0507060c18060e03070807030830010b07030806030609031605010609022106010503040309030f050a1202030c0c121c030b1306140a151202 72
    0x1640d0074052000d41c03010300018003d00304030301621305000b0b50314020917a03800030804100070b84d220711b603413210640d5903056201c44003045d44078610300d040b80d101e00b084d101281500d00c2114002502038000010054541e4282c040d1000203035107103a5191200c0007480080e1103540100550000018070b20348070701c01700d030040c1c842800e0071080f65000e0b00321800907005058250b0001800300c003071541000e00542d1062007100200b11a261200046803240034000c21403054070f0014000c4410041c3c20740040c00a040649011512140003004110038500b1040400c0c0e1020a5100403865551052089138400ca801d40c8a241748540b941e51440c4034100e2100c0141c905020b03500e915400908002803080042c1d281e40e00a60311400560001c42c14840c110b41514803500c402400c11036010303004a05042d0710381c028032104488085212041c1c0140c82d51458055000303500040208c0009000c0e4805000e507410079800f070302100341e54030a112400e90745000b501e14007441501155410780c40b5140c9041807200b6408058 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 877232023 1250 877230773 877230859
    0x80307122a030c0308061915050c0607021c050403021503150909010f0c0c021807051e0304330e0a06090b041118150f03060a060f0902040302 62
    0x7401c460111400720000b40d0703020100700a145d40001070a4004004a503801400114648501d240140c107110f0b5020613012902a500183e004000b540c0c1d01140f503409440041c90000b800035246c1140c003400d00d40b00401c03600401d0045101c3c0c02a2803e803a80a000000d5028041c007015001e900300900c50200300c041c0450000d0903407078071800c00b070242c42ea410000c10020030b1120101c0c29298044004400c0100b0600700f1800750b5103180d44008040099030314042641c5a0800480d1580300c1c056112180e076040d1040c3c00303041e81c000310043d403065001d003c0b4800302c00c8811131000a0302c240b00c042c210000307070301c0c00c0401e201d84030580c40400c1c2c20b0210710840d010f422482c1d403080c05490b60442c050701d400340103108001c14054400d02160003406c04454085112800c0704652001047c080c260748000f405d0031540d240141c40301c42c40b4801400c801812250280b515a5101002e01550b009400a5010036200040c204a45009032010340340d004045001180032065052141c5807541c90310700910181d54011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 877233273 1250 877232023 877232087
    0x12020702040f0e0d030b210a0b041a010f05030a0312150e0a050615030112020d1a150604050310020d020f0301062303040f081b19030908030712 63
    0x100418455410001c2201816401c000d42011100311959052606006c2e070054141c0d2103598a100040c1c0094401caa07400301c0040d228a010000000181040c6500f0140400e014852640c80b181d28808c40c10422075031303201d61200155904512441b0f4060b48001da401002030f004486000403038509841c0040c41b940d000d80304682c2d0710700300c0d407000c03441400308410303c03802d00c51a0003a990710000c19a10030f20705800c148100040b07803005100d00c24034813920000346802c5546000101c1003a07030300400c900180180c504004000a2003e0f1442c0c00c58074005039078007409082030b8081c0c8049401c002c000d407600701e010900c5178010f075000891b00900e05508000ca080030380598405035000e01141c1e507074007100300854142c000109a6066007144850418010840010102e0880d4070803664401c81240d1103513031450102c6281c5402c011554124003e10904102510110b00360040e00ba01030b540d0601004e40e14903041e0f490348603000d00500400d42c0c83d03041c0c180550003580e041d594039241031020ba54046100d441 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 877234523 1250 877233273 877233281
    0x309020d12020c091501090801060e01030b090a0501110a080708040203060c0d0609020a051c06080309060a021c08191b030e033a1514031e0601060305010b0a0801061202070204 77
    0x60112030382c5c114200c5d04003659200d4035010207081503030004c000860030806840519503051100030000c050540000f42c138400709010381ca52940d403000c021300080b03440382c0c010521900134046600c00595a88005000c041c0b007031086c18051038001d0040c0100b511101140d13030302e0f40d01101c1c0070304c1065116600001d55504600c000c24204a40d43d6605465010300c0004201c84601c079134103450b0711070070b01000f0320000c000807044516070b03042214940d5551510b4ad00603401d040b100b090035181c845c294141014030581101072544903c4950020b504803512407600c0c14222000c0d400303a140704000883d00c4000043c0a544070358042071000045a040c1040d081c81031001040f0359100500d8605950703004106220343c02a200c19090388590107015036030045140544400161140040c03060500e072021020752800e218046071414000410300c100c0c0c0348100100d65402003031103014006447c2100020700380d10800207407540c0c100d0599440e4060307403034034508403480200441c0c6444210350800400c1d00580d0740384a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 877235773 1250 877234523 877234531
    0x206160c0b0706050c0f040905042d02010e0103020703080a2d020c010b0a031527030320071208060406150e03100b030d11100c080f01060309020d12020c09 68
    0x501c19520141c42c608107013580c42c040c0c0b900d44504018040d00c0400d95010003558251500d52000064a60311810103044200c0301c3c03c0c002514a141100d45485c0c84010040103e88174001e88803c20402000b400441c201d11402c54054006401038011941c004c10750303003090f0311040c056454281c4014541044a045c0091091040c00590b40000c1c40c01e4007850078000c40400e40400ca91400140d4595240c003504100108480814240d4401203101c04c0f00195800201140480c128500b850b6030f2454090020080c6c11100d0f0784085403201ca844800f031002d01210742403540414610040e01c00000305454441c0041c00301c40c0c0c4075480c0ca03c0807410a441c0405c4070280c48480d80c44005805801080c1814000b0702d54660900c41d0800c0c2081082d42c40004007a8860b0f1481d00c0d14103c01c8a51202d0542040001d00c00822440e0030030420703643c0d0680c480c00340c0b40a44440107540c40d059a80300410f804484100c070000350807c0742d401641c030214601680510f80b4000754015145680c2140f000946480c2c1d00301c0e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 877237023 1250 877235773 877235789
    0x40b03190501050f07090e09071505090f0901030f0b07120219080703200a09120c030b01080a030206161101060b1308030c030702060903070905010b030f0f060d0206160c 74
    0x408400d080c82401d020b0240c103c2c5505031400c00a080c0070794001c02112850203040381498203400031800c154400c0042d10010484417150b01101211140000d04a07800100450300c80c0025600d00c0b203581c50070030022030403241d00101450a080d5941d4600c175250b10000c0080d418416413052030100d20b0a240002c0000600e40f0420f50040310008102805040010b004841003502c0e05c0f4040d110f1444140d00d405030a8400c01c00f240c1c42e05d021840072181403546422041481003a0411613040003030441004c02620700c11300d4080110380c2c0b20101182c1d070702075580000c1c0c010780c40840400c0c2c20150049103491074035038034500700184940f41100300307007503e1280d800b245059200140c612012410240000041c06860000d90315051540907050365030f000399000070b0302c03903c000159104131307a604005540040c42825000c7c0120341e568841c51106030412559030030040301d218005000f840c10050b080d44268001070001400902e25000d00c6041e0300311419843c805004407955034041041c40548000030800c1c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 877238273 1250 877237023 877237063
    0xb03010b030402090106110a1b1a090103110a020303070503040609020603071d010201200306010c052e0902031f0f090f060e060405030a030c17090102070c08060c09040b040b03 77
    0x600c1031010140d0141d00c1a42041f090002c94018008041421004180c00042d110000444041c41c2111404d03594450340743c842d202201c01c00c0840d004009820a030400746c90401080d8012181010b0a01c0390306c8414006800400024440c02d026401440d00700d4012030000403821030f140d01103050307640180c0c0c900c40452141c040c500702c01c1c84290609032161000b88000d100b4214011038244003021001083c001da41c0c1c0201c0020000e034821070b44400e0664200c0c00325414801c004041c0b4107614659150750682400c0307220f107401c151043d4090344181d01e60180050842203219518000169126503029030016142d14100060034002e00422010314003800d249020a00240340c0001190038444050010360080001c100100d88040700b0740d80068568180407401a50300842158041c06c002d5003a445d0b401018140002c109055002d40300c150711545030601e01507140d0480301d40d5581e084800201030402004880160300702030f048261400ca01420105400c00c14600081c03c0084400c0003650325100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 877239523 1250 877238273 877238281
    0xc0b25060b030606010e0a21020319050c032404111003060f050901080309011103090306010f090f11031306140103030320040503031207230406020705030f03070204090206040b03010b03 81
    0x912003d41c00ca002402d2811640200101042c004000b9100d0291554608001481c510a0801131141000c0d03005013501c005460200105444a09052041d1824441c200440c249418005461940341c03d0003103a40300006008694000760510040003240c100c0c07000c1c040c000264544030091000c8500c2d80d1801700e8117a0500c0200680440a903000b14800d01d001001082014000f0085443e802001e1800301c0380098040e203003030319612402840a4042c40780600004010b810b5000e00010740340018020300480c003820305450155050001c070a02d02c035808101041c00342d14640070000d166842850046103500c05100c001e446643c0980c8140c1c007194480d203070039024030030380764000b000c948030102c609040a0801000c070b43d40c1c0c018007a00c80e00c014429004180b2050041080b00c0e46040038444a000c10b9004000c1e10030a07421900c0b0350000744c41405004502441c1c041124800d200c00349001310f044c662180c00b0803010300801d00d001da0300200104400308901140c2c03c0110301074007076500059580d042c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 877240773 1250 877239523 877239529
    0x5160b0117011404020609150c1c0201050f1807090212060a170d050f04080a03121a0102100207080405060403061b08040f060903050c01360c0b25060b 66
    0x10101c20035a031240d01d40807400302805154400b00b0340007078042d03a0341a111440f00c00403a5008098001e52800180702054046c1c07844000100c4540340c403601c4510382c0383e0f5581181c05a017a41d0302900c0d1050031040c0040003500c1726248000140c45030031860219a00301d50740d05001c400720307802442800c007040c604800b000014101440800001d0000c1141d120400e01089583c0d038442c0c03062400c94007000710014101c07525440e08401d84014202d228166408000e0070b141c00b030801005010600c81490610003050000c07003001e03191001c80030040c2c0140200001c4020341000070751142c0b208544240c0b05100c0850240c9448010f0405540306040009102944100c440790f81d5007024018400c0114050030400010204440d04085d0b035803102020454070758901d01507a4500804602219642c41e020a021807064060f881e0b0984c5843d0000c06184d02d60329048000701d03d1f08846015019040f4803400304030309850130000340074405812240d00e440344108030007c6103d000444007560004d440c0c0852040e645 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 877242023 1250 877240773 877240799
    0x30706020a0302070e0613050106120f02040602030405091914180304050d020d030e04110d0b060c2d0a0b180705030c12010b04090819051c0c05160b01 66
    0x201250000741426002030360b000355900540e02074546041c0004000c941b6540300d0009032001010221801e200c1581c495000814240d21164190074803424000c0c91031034242148215400e46185502543c641418042441a5403001921040400c50aa05a000b149056100d200030400c04070030050201d046ca01003004082c6000c0074022119007042004004640d590f6145043d0280c0c140c0e078614001d091418295660801460000d40150520b01c500526501300c2009225100354858100820340418040c0b00322406003001c0ca0031280c2c42140d5204049036100c0b0442c9108484202031100e9609060595050480e00d100c00c503403a804c40c1c414015032500e940b0b0704962084030301d002085d586142c0700c0000d84e600030011503a4000d0320f204a82003000310081d0030a80b8405070140c4144501080740c50030808907444903030300080a0050130380e8000010310400440780102c040160300030200101200f020001c0080c0300411007409003c000c06500d110910b118019103d010b1102e01c0010f40c90888451040e0b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 877243273 1250 877242023 877242029
    0x40302100216030c0515090c0a0b1c0b03120c010209010306090510051002120c0d0e09010f03020402130e0901060801110403022409150306040b0a08030d050a021b07050307 75
    0x140d40180282901840c40c20342c06140719030103240401d9209081e0410b80d0900c2d440d6014010846500d50410150071000180c0a401c18002e40300c00b00c0c5269180f10500344e0b4002c1515116105203601c2d002e213411100350300320714501c81009058502d40d0040d81c43c2c070300300c0781d0059158955503500454407000c80e6802d8414000200081e4209019a16003003d81806480b202d000d43ea120f41d00c000810310845100304035000c0080c101c000055969001d00310340300e43c2e551194001e074000035180c0c5d00001060529a071030504841c81c500600040505550802c0041c0d0040505504507400f44a0000b6031440d014210394043c40c0d40b00000605175050520190940c0d0b181d08404d42107030342c00c002c00c00041e03c4580c100d0020a0b40220247c01641d2042e520706a05c2c85152409680319012018150605031440004c5009620496041240e07800010030b000c00600d1611409403d0f41040c00004142442078000076030051410000610f84a8141b0303620f810408000c0c11003003554804441800b217401c0030413140e405 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 877244523 1250 877243273 877243303
    0xa051015021f0513060e01020c01060b030f0106090509010909211706101b06060506030f01081005062b021207030620160309030818030c0d03021b0d120305040302 71
    0x20314034111030818004002c40c0f100030001503441d20f42e002c01b48400e40c195680240ca16009001e050f96480c000080c41e04203940729000b072400100002035580c05810b114040302d1025114415903032800142c84007c0c1211403050b43c0007042085600b584405000c900081d24550751103450080a850320340b107035030201c02001ea40c02103d00103d044102600f1516080700a1054aa2209002075518007000030742541e600c120b40004000c01130003219501350032098181c50000046800c00e8112054010646209a6420341c1001e00f06292420304180400c40e4074a06a021451a00000c0180c2c007156a000d1805d03036a00d090703000b0010900c00c00485000f182c07801d10849490500841c210881020b19210b41c0403600081d8201c51114001c160085101034015504000c03896250f4184905507201111000304c045e11a0003420414201e40c5400024075000e5074241d4010001c4410794401400328072460440290b01c007000d01d50300d8002910100e042c008444283e50042114103207403602a19003801000e8200c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 877245773 1250 877244523 877244531
    0x130b0a27170c1002070b0f090706050906030703020c07080120030613050709080d080a0c02210d0603051c090b071502031b160203100e060a051015021f 66
    0x1c80c41c001024450035800c03031070311a955050385120600d0301103600d441c000b0041c0003040490900820034a054850404680b8132041e40e41c0b521080c917100c864502030f2101090081c0300d40e003540e0904001650307100e00b003403d00520780107022904c41d00d04200c0754803200301a9100e070310200c2e0011b0100e0040c0460481360440e5411400d00000003180180080c95600406998800082e00c1d1845010000300404800080d1808a80141c03801484064100c8424008a04110341d5000031032001030845c114840d0000303810300340c0c3c0f401ca070041c19a45c030540c00a1140303a00c549021010030340a210049a9035000800210414031074034001d40140095840890071550900150005c0354184440008050f2002170050b913070350b14000c5100b0b0403a00c01c118040844004908415052107103002100128002c42c03c481c884006140750a00fa511884c8e1780c2c843c10340010010a00815286d00801c1e085460000602c1c2d0703094440220342801d4a00d00ba8000040c1c0c4011002c0d07051910019040d070f450071003001c6c140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 877247023 1250 877245773 877245851
    0x7081b07030c1d0112020609060406030e061b0702010e0f06040902040905060d0f030c032d03050108060c122716060207030308040803061807120b090717130b0a 70
    0xc203c07201c0510541d184000c0f996039400465817a54100c07081001c000701410349035a22080018000c00040201d411144116804250700b100200f45e410003c2c00349090300c614100481d80111003840c00c041ca515082860000e00e44400d650341c034098001750100a2005840b5482c0892400585902500f07050086401d00c54650105611a140c0340303000b0b401d800e03c8402c2c0b200301c0c0b03022192500b64165541110341da000ca401409142096000040c41e1190380610240c2d0700c1d0b509441d210842a1609254100200400f030404508594a107500515100c1c101c03000480c07070450304050300340385a02107200e074009501c000c0d03200034907506403005858180b004184460540e80c02a10302200542302030b201c039102000050080e41d4111440403c4403054220403000c1c244804003800c200041107c61809d181844540c1202d4248071000a208194640d2440d0b18203520b15611949418091300184000d0201071212001c02c10106485000e07850f2401d00041181105802c0204c4050845203100d00c140707400580 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 877248273 1250 877247023 877247069
    0xd1e02130f0b040b0f0c071202042316030e030f190e131109100210061208070b06011202070f0b060d0b070e060c0a060b120d080103060207081b07030c 66
    0x503400b9190324402095407001c69807000d0001e030060600d24001480b0b8147e0115504802c0c545111840c3d1007541c0600c042148820800b03810b1800c1e8000c2031382c514524000517081000c182441c102c10803c0e0a0014002031104e1096055500031482554203050002c0e4140c8012454401360441a03004d02d0584801000d500015461044420002c4030311611810404180f0b040344080f1230441d4001030000c40120500007001e521005102107180c112031400c5c0000600742580c2271014201540048068607000243d660300306402c0c1c018100301d0400c084461076004000c1148014a24213000e541001000c44035482c080081d150020001800b800c6540c202d14001640d01c1692500b008071818080e070030116020114000340511805281244100043c42c0184500c03944000001c00084e10360040c0380c4136840845a440b6407045a07000002c0c5004010400700d41c4690283c03400610030142d09103405104d1f00807600c00c0d24211180741c030a421200c420020014280000c000807c1500b10346a0076003000020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 877249523 1250 877248273 877248277
    0x9010e091504030824090906010806010609182313150c0f0e150a090f09090b070c03051605030306030f06070e0d050109140d090e1003080d1e02130f0b 66
    0x5501c14031031681c0d0703403141000b04400505d401d15000e048120f0524201c008140e031a9002c0c0308010003406040004079007684680c00390b4003941e14144010701c400300b4a400110040c0907500300e18150311840d0b000c0721000280d91f288107014503603c84c0b400e400c012141c20942d48464009400010107480e09950b403240d141c01c0304040d02c0c04455803e180030142d210001282000350a001c0c01613940d80000f0b00305181c65013041400c400d0719003c62000f00e941c1c1e160201d46d42120000a4050b080c409280c00180400c3e10821201803c5840382c640030381041014103500d02c50304049401107403d40c001104002544c1401c00064203402c3c511401040c0b1424000c00140001c0b00b070f8500b00380115485c001e030b1010f0200942180c001c01d5405000459801d1040c03805c01c1e120400500f508000810490700001c0b400390a214040c011000424900a4145103548101c4140d11201070743d8005a220610403040e1003104e090340072051100c060260766001030403010048042150424000204003050510100100c541 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 877250773 1250 877249523 877249531
    0x3040306050709181d0f0709051e041b0302100503010302131b1d091e010e07080c070203100524031506060f04090c1e0518010302090f09010e0915040308 67
    0x500040030110141554840c2110320b4903821795114505038546840c60000f240c1d4102c035400342040019886054201c481480d642221000621410000c01d02003280f600c68440388511020612000310395035400b043d60440400c1410001c210301100410a6003009070540051308a03080c010020290782103400e070104ca510345280d004102125005011440318116803c4070302c4002451015645008861307e80c04540000d6506602c0f01c010f000041c0540401e94030600031501a210707004a995450b0402c400d54200e0481070360700d40705200d040702c1c1104041c4039842c080d100d00b0108041e01d007070084040303540140c1c103420b03180241e000ca0300208200244041c50360300520202c60055031404005003424450140c2c0d0000070240386000003100209801c1074007001401c450074594910101125400e4401c1e01440c07880308541090543c2d0b86d446584280e00a0a80680040125400801c2030000c110768030026080815440b81c642c003804032000c0b00300801c0e010844040d402108610705503030010102d02001e0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 877252023 1250 877250773 877250819
    0x7031a01140a05040b03010b0706180b0a05040c0312090e07090509040213022206120c0e0d081306030f0f0605010914060403120807080f0108030708070606050d0503040306050709 78
    0x3060620740b0500c0b4000715801021915113240d100c0d40c45a260b0882d0b5400007170308480361858421146092001e8007062007049401074210380c619520368003060054400108110380d1503014400102c00180c440c4010080e01c40c0b6a6034031311032241443c0481305000005850802400a6a9420402c0b07558030700d5115801641a60007000703042808408401a02480070101d00380c10600084061084e8010105012183c16550750034006020040d040106d43c0c0f0000d07031400051058510f100341342004040400520f106100e02c6103440c404542c803905420113a0031200010b611000c040003400818050400d0042818004001192400c030002c0c02d443d078079101c1e08011403c80c1154000035500c0c83d0a0341c00841e0403080404080603080401042070400326041c40c0454859804141c12860b10408241039600000c000d41c0b8000c4962250101c640020030100c5d110740c0c483d40040b5003511000b81c1c42080621802c0103580312825880c00006072040104940200150400c0410801d8640c010800c8460490 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 877253273 1250 877252023 877252027
    0xc0c100b06041502031801030b090a0e0a060c02010e06010902040609051c06090f0b0907030b06060d241d061c03020a02091f060318030806010917010507031a0114 71
    0x50008900300b4055907101d11410b000310740c803403180e164020000b0084081e903103180315000c0704100015021a241c420380903400540c00000a455a00c40754090500c000c010030071107604900b00c0e5038150988001a1054005035101c00000c50003080400240e40508400201542001d0411100038062842c5d4441c0501c01d03040989650f00880c5106c80112081d50004402d010011050820344c510b0080160119128100480051031155011684405176a485520f0b03c2141c1c40d04030410045811280d8034075009a0345800d092541a03841c900f1007001040300c0b04490b086880d0071300750b00510040c00c01001030204017008020265072107072000308102070068448030806015050403440c180d41da90000f5008240310051160340881011001c0c1107908020680840d292906422016900868400441180d0304a109030000c0e008030042540010103240045d00c0c56540d42d10301b0403160184600034540e9565401f40f00c2c20f15458000c881c50300d000e0b040c80d403100740c070020300080c02620001d001400580e00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 877254523 1250 877253273 877253291
    0xc1d01080709031719021903030507030b0603010e010509070f3c09050f0a0305070512010b0a030b040506010f120b150d050c09060f0a03060f181a0c0c10 67
    0x150080301c041d64004c110031301001d20360b114a106980c0651640b012509888554624007880000c100c82c004001c1a941c10b0007202c29a020386c00341070040c2000b0b0034141c0f0b80c036025043d5181c4002650081a000c0440d001d00c1d45040e06001030410064016000c000e01c0200a15001e5000400c2c0d00e03400391200e011190300b0038002e0349100c040010300946070b011000c011290301c080e5800400d2000b03480b803c81314030100e40c0e5007030f00b0881440100d00c402071441d04000d0042216207060750b142c00944070080004a403140000d0b00198114040f03070000c4440e00c04840a0105101082103a5030145c802c000d1090600c2d402d05000440000e455100102085c0304080040d00003980d40a843e003006102400701201c407a510b14017a521100e0340c41440e80242071500010700035181504070a0620140a030061603c18115200d810140c41080768041d4100d8039042c02c8109801200442540c8600500c0b1900c44140ca94145054080740503060004a80d4144a04a249003010880b040e0030102a900020031081c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 877255773 1250 877254523 877254527
    0x40e0112021518060a080403021c0e0d060603171c060f1701060906152c210304030807021305040b0c16080d150b04140103180f150c1d010807 62
    0x250510403070b83c10040110b14017180581040e04680108e129409690030411141608412105178003440400950403011164290801e682e01d901110b0050750049010354407612200c0786150322241006500c10009960388d00f01c148102c000c0c01d4100e0441041c0441c52503d900d01801d00c80a000c1c4003121780c20404001013a4030258071000007444416004e000b40350b0340308200c0c017080c0c00c03600360307500802d0110081000003400325200e83c8041002072194105031180c00144605c589400f04996004948401d00820040040010340000e520420344140d0f41c00700c910512800c81d25401218162600f8542071000240400443d6a0300c010149015910b0340512824a104600f0000c405401c034034000070380e00b8200760740f03070480300307280d4607840752070805030707900d400444442c1b04e60302c180031308180b2407440012558400d0300403118840714103251013074480725130700d4040c4800e5180340c0c211103801180c2c014a4040160b4010b4500791303841c07801c0079542034445500c120118001500720178100040140040c0d6558 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 877257023 1250 877255773 877255807
    0xb0105030a18150506150c0d0509012a06110c07052407080c0f07030f0204151e1509120b0721060305070b070f060b0a05040c05040e01120215 62
    0x3030381219066203c8480707410300c2c01c000c0c00e0541e400c1e401048017103c000312445031001194015020000146042c4050301030459480c2c01a04600e4100301522000704041901e8510429296064541b40d1254400c2441e00104440d1045083e460803c01401800c1004001040d200110740c802c0c1d075104003440b82c80c0d1082e8409040d0004101d0005000310f082d105102032000074040c0d011480e01198096841390059542d83c0d0324038800200640d100203080310040c02c064220740d4408801e0001c00c104261214140c0852121aa8800d07403040d503600000c02510070f0003218040d0809036402c203440480c1c10089030514550101c1c0300a071500304031401107150f2604c14140f91000200a5074070030005888000d01001600c00c0f444262200d108960000c1117040603541140d04a59000342070100c544503070f03503a1001910110403000c0d404440c46030001003544441c0241100e8003010381d5070950f41ca003440b00d402e04849040c0c0001426100303c00103000107840e019900702454504070032035500c3d401614892070340c00c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 877258273 1250 877257023 877257071
    0xb010504080d03060e01170d0309030516080c07060f020a0807050312011e0501020c01050d05070201060b032d010605070308041b0e090d1d0d020f1206190b0105030a 72
    0xd02c07480742c070085007035815809007003a0b62004d40310405a981e00d8854108103801c0302c0c0d40c03865a0700010304011899009901050b880381c440d09106050800c1098042c0c2002071003c410703540014005208191b5400920414000d004035041101c1d1008501030001e42d22800d80a0041001d2000112441804020015100c503001705881d103e003650707120307411440d00440c2030700004400410850085491740c00881c80c440c0104040c1d40e21070500266000c403101509010309110103555a4100c0416076550201c02548a101010000c024bda180c56101031220309031448098940e014000052040c664080100d40c00c141d014036019249440d281080d101c00b0b031480c502003002101503400020084006981d0b10312075005c0c0000d0344c01c0b12030340031801d8034944148a540400b404100c10b0244a41c506100c01000e090300103028142034036031540124061030003034041004a640248100300c00c2483c4041d0202140401010074880c903103981d80042c4c803d0101902002c08103440d1501c114005032105010b101e6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 877259523 1250 877258273 877258289
    0x807050705030c0708030903070f030b070c06092001023304031403010f061407030806060c0c0919061a19030209061303031805031f140a050f0a0608100b010504 70
    0xc0d030b6640c5507026030303a47c85000781d68020b010b105000550751900040000403650071085060495690b6081202c6601c9049001c0340c0c002c0c0d84900c1d0300e010404a002080c6c0c011a50003000f09041642c1c8006850071a040f00c01e1042c940c100240c0f1000c402400c40c0b000c0c103014116241c402c40b62140d03c0c0036183c80114000e01000e400b004000020403441244101040320200d80f182100001920070881c45441414000b802165900000ca5a582010402002d2809641003500d0310038071010300040b4084401d4510842c5196002000c2ca14401c180c414403008108078604420140000c04a4110341e0081503110340700f2600bc11160049640240c040b07440c0c070030303000348425510300300b5441283c2d6894140c0000d0300040c2e041c107001c01e009420500f2090903200300400608950322444a564031010010380d1440d04203845101d54160200780c00085401035141440c041400e10f03000c3e00080e04010010004e0881608081d0200400d4501013410420110440b10219160651000580702440303540e20440d8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 877260773 1250 877259523 877259533
    0x1b130311011e0905090f01121202030c1b04050c03190b0d1a040308070503194115060a0e18070f0207080c031218060409060905160807050705030c 64
    0x241142d00001403c00d8402c200c031090350607100c40b201216200310900444603c0380240080e000420141c103800001c2e40001d104682ca007402c0d01198604014410b152103043c950302100464052606000b000ea0080780600040c1c2540b50030a404110300004510f0341e2801940c441c001c1e4115156002440300f00364000f501f91030b10305100884003031102c800301c07010b81c00a90380c00042000b09100b2000c80307024030728030b414144654055113405002403000c00303054500d00c3c15400f09103001ea0000507201d10b41c00a64485c00040c0d0a403911300f0300340c12100512043e500e0401d4104461180e41d007009a404401081c0f0305450983d0f581000f01e28500d002400b40d91000580c1405c000b500c44d80f060030200c8444c1d043e8241c0340750581e00c1080039589c0c100c02c0f52050307040e0090001038904c4d00c060006030202102d40108820080036680100324150b203c0c0e000b0b0704d0307026182c0c501030101308014005c01e070300a80b40d0002d0807501211400d0042102710040c01204c100100001c000e81031007020800e0340c082288040a0301e03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 877262023 1250 877260773 877260827
    0x80d06050a060f03050a060e07140408010f02040305070f0f0e0604020c0a05070501140f040e2701150605090a1701150e06030c090705040902071e03081b13031101 71
    0x1d814500750842c03c00c0001d04101c0060700c0b005050064000301d5211078a44010361321028001c0d1a000804c10000d80118410300c000a00c2d1403090040403098040040010303030341c07400c2d410035074100100ca811203d1401400082048440e0404000004485c030b60041a4015155000090041d2188240340011343c441e8441580030700802003420700c111a03090b00c0d0001d1019000354004958000e4074860101c0d150140300030091103403922142c0b98000c0201c030115140c04d001918080600b4103810901116a41d1241e80014500c1c00740c005401400541c2081d07410711501743e0003d24213045502601c1e08100d01c0082c0e140a4282c03d400155411030540c1d14032550a071684d20010503506e044540c2807080c400c210400b08181041d0301c00e907000340b800b170341d45524060070b120448002c0d602882c400c41d81142480b0120610000019180c0da0180c0701e6651b108490901c00032050f2524985405002c011f4410401d52561002940c1c2480440341d0000030081069502401614030007102c0e540c103c5440035400f904 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 877263273 1250 877262023 877262027
    0x603101103070917190827190b0d05090c03070303051201320415090b03150c0304060c170403020303070f181a0712050406120501120b061504121a07020a080d06050a06 73
    0x104180b80001ea0301e0f04006507090000c500529180c4c4100540440d040102b0103803500240c00095101c102001102c5403003140300b001c2850303c01d5950047c0c00050001c074078039161940d05010701f0b004141405103000140426040290300144010280321720400c0340d64000c0840d16260130000340c141030860780c60211390395401d844010309554002c3d1486401502c494031108141d0128160140030074031102421503403581e5032000188401700c268024048103488510000c1598030100e8844c07403280d40555281d050007000500222240d05c2e051041c0010101c0305141410002114001c90317031120000380038594101c1d050701ca64030030740710040d020300854500048a150454010300840b00c0d55a02d0304142c6200c503403130400302e580a024600301403003400c00500c00b0038841d450590b003044000300030720510891022a8140ca5105030b02c9200e40c40030400d0741b803003480300050701c9032a07922140c24405520710344420029280d510090000b0032901300418075103ca4032a940c0083e010707242c060001802c081d107580300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 877264523 1250 877263273 877263337
    0x80d0509010201060b1201050d03030b0915030139090503010204091e050f040f140d02072c0606070c09050408121501020d0806031011030709171908 65
    0x140d0340c090760074240009015070f108012114140414003c101159007070204000c5014040f442c03d90406031602203040d01ca54525205c507014084021402000340840c005250a46545040ca26008024070241c01e50b22402030204c0180d80d100416400d1291300e508034140d40c0324215401032a015031001c40c001c24509130550210700584503d501600060354400005400c1d16002c80d4080c00300d00c03907000481c00081c140d1070b503c51414400c4000c0b40e03a002900190500d014040c03161500181d100a0081014a013858030002d0440e4004500307100443c0015110841d1940207030445014a500040304010701c110528400040c241815040c4110f0504d410003004070b4008054250704d650141c8080703a81c06e84400244c00e4414410380103000480f20b03101d030139601e29500800c078640600400054a681d18840d02c0b8070038480001c280d845440c1d00305404003e00ca8400e582048008603203140d02015201030000760800c1c61070425000000b001e01c1c5180400803130042c680020030740c401054001940c8501030b81 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 877265773 1250 877264523 877264537
    0xa090b040609060e120f0a050f13060e010e0102061b090d150b1f0305040c0b0a02011b020705091f0e070201050702210a08090102070804180c080106090b03040507080d05 74
    0x2d403e01145041c40c0840780c81d0317881006150507a8104010350f0b0740480f402c0c00038003034521041c1000c1d030410328190594010f40d03010480c522844d005441d403c0c0a02130304000016011482864001c0e170601c0c90000107562400081d003a001c0302d407015410700e5852180b810441e6403c807070181010340300400314907040e10b118980c0a4a143d050342820540c040078100b04070003c1c942402d10205642e0064041002d40007010068020707500781c454000081204624503009155221403640005107101e01c151203510480c3c1441031500845d003020170100500c7e924000480d070481111100310960b41503d0140803046c0c0d005510440010052008000701d5030780642c0450b128001c44d0302500e03900a031344880e1080b1000c2e800740d190402c1d202880b180d00030034880e003080c0d907002404100042c5040041d0319650070340d400c035511007542048c14852070201e004660003440d104c3d481c1e90515000f6941814005020b00b40c1d54041c00000c9003001c030001c2d050003000c10114008214400503100004001c07140109036034440c0b6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 877267023 1250 877265773 877265783
    0x20a0215011505040b03091006060903020406120f0b150a060e0907022d011d1f02040f0b091306080709150810090302031201180c050c0d080a090b040609 67
    0x4400029802c462400314011082c096480d580b03000e00780003103403540e034102800288051007408210102100d0301d2095130b0181011f42c8a025001d0700e58810071065600541005261030318140c444d10000e01c800000d0354a045c0c0c003138203a044e2641d804c86016200065404019031102110300001002c5402c200c050030599802d45903c0541e664aa800b0f990300c2900b014944140200c0648005c54180000b02620384848010008140e01d021400c2d8031510050003d9001c03010b0700b0807041070301d514034024481c1c485808000b80c2541824a0700b80c2900e0569132a1156019508e00060704085960b5a000c885803030782c04071041041095100c0e0103b0b96619010b014000c0200d28020042280c244801900c900f1603000c440188206031300000c021000e8000408100c1c1588010f214180d03400110318582c1e80130385480d1842c4182c0c0c085215803901998111008802882400c0014070b107803110101c1d800040444a0400400d04c1d140e45031707031720300500040340050018110f200034482009540d810400d00c0314098 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 877268273 1250 877267023 877267063
    0x41502030408030411030309011706011110020405012a030c020402161101110a1e0609080a0c1b0b12180f060603013209030415020a02040c0e0f130906020a02 69
    0x1070301810342c0c03072152140150100e110580142b582d14260200c946c0d0011042c5461040741c1c00d006c1c00f440c50264401c0c111303102c481e00440d040c485564000d0000b01d212030711020328090281d101000702006980003401030200060040c20b5400d6440715012643c01000c4003000b06800217440c01c0a52b40d0f0780720040500d00141030703080050590400080d040152503046600c82514800e503a0640040c1c48181c0821900140ca40c5000804100303d840a850003a4954940390288240c51030315410700510b0002021030250909800d004113460b80f01135a02c0051405810721712520b60354000c0c0e1207005074034a148001d1080c1c110b00c05980401150a03801080305a0090003080041e054080381040d0480b100e21882075a0a2691082d00d42c070340101307420241381720a8a10f0030fa100d88402e0006d4203403203510405070b4003c040e1402103051511801610300c2d4546443c48280002c00c0000b12500e0180e00351301e100728030380501804a410154414100e1541c442c02c1103548260040000c6d440e0241290700303407148030b94 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 877269523 1250 877268273 877268303
    0x100206091006080c0609190e0f090a08030112020f03060108030d0e07060f0c031b08030f0f090309101e110f2409251a0c0c090415020304080304 63
    0x1c24001c15098410f000080d1180361301c224140111904086404e80e40582004040085020300c007030444081c0510080074001c1c0c0c5008603551320b05140c0a000400c0729403142d201400402c141500707490640e00b030a5040c0d42c6e501032600004001d8031540c82100d40c0f5008860001508002c004020000c0c0301c0b520314148042016905900d842d55205e100d18808141c0c034070480d100407031103561000e1380544a820080d403000010085040c00c40003109003298201000014403140311040c103501d40d40b241c00d00180106519110901503100c4c014540403070b0181c46210300e13200c4114055992681c0c24a003001400e60802e81c0103e0080c04840d000190540c4c5010f6800e00c40441c540c08103035007c80180c0030007054100600340030300e202c0440004020800d01e000305c20104107440001650f02540400f2201c02e040d00e141400b8084102465490010b00c4140c01040105560b40380880c2c80c16000004076041070b16035855080003621300c0c0750b0441060781c1c075200000300010070804001550107280503051800700030701 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 877270773 1250 877269523 877269553
    0xb090f0a030c0510051b0c0906030c030703121422060903080f030c1c05160905030a0b040c0b0301030303090501270f03030b040c030204081b060a0311070210020609 72
    0x11031404080d0200900d02e00a01060034000103201d50342c4450f2410a2511011001c242400c070320340148000039400074a0040d6080c0342ca0400d540e0800e008a01a081403036402000996441691000519a2007070300c0c0701342c8071980100311706504140400302c513580d01d4100345502e0b40c27101c0c10b81c104043d22004412002c01c64620503212142a2944506c0b51481d050900c0a96505500020400c1c80c07134460070494883c01481100f0412140821144041502e040c80e05801c201d818070724041000704100f0030000c1005940000d0a400310f250001c03803404c4503481c0c0b41480549051183c110358503480c07000000004244c1d041d032109903428040c2d802000700080e61002801500300c3d51811883c143c500c0122013000c01d261301c0c06075503403610909001400e442544049002d46182001078808660b0126082140010078007000001c0c8400c24010080958000300080380e90088099900070107588104000240003404e084030015500207102480da01440d0f83d009550308070489050513103005003d92004046 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 877272023 1250 877270773 877270789
    0x601180c0206011a0f1206040506060a1b11030604030809060c030f180a060f09110d021807110a150b1504140a0f090902030d050903030702121005010b090f 68
    0x800365a010305000d07460102d42c0c00c1072484c4c0d42c807003201c1004100b0686035002800c2000704440c414044405511345001d100700411654000c1c074080c01900104040b40038250300148030241c0513180000d0044107240c03402d20b400c0c81180654100d4040c8200c0c02800f0078980c104000c1c9101e41c0340e0404540c1c1f01e07500e101d20040a800705881d440c0c41135880c07a002c241110507480400b040b04c06200300315100f891003912903d0035144136003681200a40d58450304e2b030a005014030156031720003003960140c2460b40311f6404100c25000d0945c0c0502c3c0070300d503174000c904407038480c852030341c0035000700000c03a01650a5400d04a072290800c0708a103d03a40d242902a0a40341004800440b440000c10000b41c02d003460044558540554014000e9008600340070214880302c080361420060100301400040c00c150384c0c03052614111204081d4014003000b400241084e80c1c0c0002120006035045e5038624034141010742e031500d03000b5540008001141001c1c0040b580304002009008411402c440004011f5003ca052126103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 877273273 1250 877272023 877272041
    0xe030d061a090a15120618113f040b0610081009020a14041d06010503100302040c030f0e0f06070c0507030b13080d0c14030f0a0c050c070602060118 65
    0x800c1c00d03140f0420040501c80c10000c0c419003542814192929400e00720022151039820403440e841d101e401c3c0101c00c074901c4c450030b0001c100c01c14402d864007000340074414641c090405e00070340c10039942508079444980c0d2565100c049403050300c00c1c411800e06250204911004440d15401100c2000311607014502c100d0900b070007030a030300241488260905076030744045c0d44104424010f02c0045443d80e110310f00d400d4010001004a4816075143e0510a0004084404050700c89030400c0014001d001003101c04801007003c4940c1110000b5540310402402d82c09031000e00020300741c403468115801041070380451104072207100d0001751007550b5125041130703a0b0f842c1509000360480e40400b0003840050000c040c9150890000f081d0308461880710364500026501074540c0c90101611a444664225000141d000d0a0103034480941d04526103891919480a4000c2c022000151510b8007d200a405882221f181d0b00da0368043d509000e444100c041e50301c4400b03104100a0356845a5a01000055480f6001032 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 877274523 1250 877273273 877273279
    0x6090d050d12091a0c04050a0b040e010602070e011e0312030e070501020609190204110307210920040902060c0705090a0b06091011100b01080a090206040b0d0e030d061a09 75
    0x41e1000c134642c10042801c010040c40402e0000c00020406030f54120720b140c000e2015000141c0c0e15070801261044074001a445103080d50f110030018020703070030000341c800e055850708080320701c50901c0c4a12054038041d180d440540111004041c004503603616800c2280305800b10750481e11101e543e0001241d076545c00321303420346554001c40c02c41400300d4a11009600d106000500108444010bc1c11040f8158001d4880001103a000c0c20340c84a003051941c10540c540314801001c000201664803550003102c0c1a5200c02910f8090f040010000c0e0384d2680034583c001d401622490b111031035807017000ea0302c1c2e00c58014188144c8201000543c0c109160060311482d0070080e020324148504401070000101c030b400410820301001540c0421000c4003004084141c0220a2001c07564421b1800050400c00707002d0205c48440c0c0c02c2c56409005a21860212006c071038440c0b01d0140d81c1c40c44400030100401004180d588240000101880c480c541600b019064500d903403482d000700078040100f407000e44101c00701c03950 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 877275773 1250 877274523 877274543
    0x109090233091f020a020306130209012c1f05061c0e0f010504062003040b01170309120102121e010501230c010608060c0408070e0606090d050d1209 65
    0x40e142040c103000c1c0081c0b28014180d045003818401104074120882104840141e11107400b4a0a501e001c101e0150040c00e03e00220303c3c00841034022070501d14050080411004a14865810081e0311440e1075031920450000484d00d81465082d01d14030b01c0c0102162042144000004a0945400c0e0201c0780c4420010510384459040400f840010703041c18120030079680100d20440002020a0244510807841041c00081140b2000c01c45449034aa02c400e000c14000700344104000614940500b074150b40460311103a10824045800d685584103ea2965402c619210602a940c5405401a0641d00c0152000e01e00301d95810106071803003440d1300303081c40340e01c40c1d0840100240e5004139441101214203441c0301c1404540941c0e04c4003181e0140003012900ea644882c200100501800000e07082020a1481e9280c03d20b4070400c255501d08134007890070038851020218070390341d558104440641802904240311003c05080954036121034080c620003242c01e0b00c00c3d600030700303400e480368a0510754483d513000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 877277023 1250 877275773 877275859
    0xc012007120309211a060612101203201f02030c040902040806060f3a0203010507050c0d090f120212030c0703060b120607121401090902 60
    0x1880045060780140c0501540c2d040100380c02080c90fa0210480c207002030790900004003450040680c000303008000c80911246010701c03d0307650311902101e000081002d42c44003103847d80c1c1d041030162507440d4020440c03000282c074040205a002800740c0000f0000700d0395400450310003c02180c80d065880d901e81409072418401402d0351039980d002c1c0d60010513001c0c00c90304040c0c554211008aa02035003085003a2346c000300810900e0314105181408038242038a1503103105403034103091400040d18541c1c10248900d092041f504046000024a032202d40060081c4800d080008014016510084031000795000305030400c0250343c051001034040300c9200ca101a00603149c0392030071000856403075040b6071284064000010b00001003006d0419462903001501610f8a1894000100e80d4040c050500071181190000200f07000803c40c1580410241001104010482c00f0140101040d1681d4030010b01540008030300d4004546c0041d807080e10a8601d0808c021820b1041ca466014016848000b408111400703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 877278273 1250 877277023 877277039
    0x50a1b1229060c070510030204052d150702100503040c0f30060f06050a1707030b06011e0201050411041a120109080d0507030513030503061e120c012007 67
    0x10305034011110f069402a580f140002100f03400b041c0b06000000350040381c20b200b5440c11382c2c607500d03040207000406101c5441d20740140314941c4481c1d0fa0b40d8820b0302c00507416452056204101c4140b80da00070702e041e419600e000c80c044e0007504103480940340c94000d11404120701021140d03040558201d00311a103480c080e10b028400d031003107907050214404503400c1803a02c001450b500441c962240403540116619041c8000c0c0022100715505c01c2c0d81c0c0304186011043c4030300001c0307400741c180c0e83c0017a03103074401c3d40d40c0b0340050b502c030808400b61316011518048090040c580c10743c4640e00551003021040c4910209001f0407041e01c611100a4900c40100810300c00c03286890300c0516048048480046001c0c00b0b613032602886600004400a001501d40040018103641480b40e80e502c4011840c403d00c6401c20354800405500001f068503004681900c125440fa4204101880074031030014204045c86404e421074513155909400070310301051003007040340e490403040080e0302c2807103030304070014016a03140c0012 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 877279523 1250 877278273 877278277
    0x60903030a0c030b130c300504020423060f041a1210020406230406020316260705060c0301120f0f120206101202090109050a1b122906 59
    0x5041030698420a1020580300c251101c5817075141008006001c95011001030800e19900310002c0d211002c294041aa04818419001710312481802c001750903a1039102180007020311080c0c107802540a0708030140d004200089040c4140c10a590710b05001c180c110500c8250754210201c3e0044510328082e0462600b050f0300c9148049548104454015a50200d44030803a03001b500305100244100150482c0d40b042016100c21b25000c0841c0103140c54030b0300130000e4890003420740207000c5407034650044050100d0049200410010b04070300c44404070641c541d14810390703c150b0381243e141c000c101c0000e00810848055a0484220ba003201c4040c040790364900701441e5540b2401c40c3d010184521880c04118040000042098190020700745404c0c240041c0c80001410f034002201c02034150310b82e600586542d541e4070304542581d0b8000c80d503070319100102c10103001d0080e040450040302d01109040c0700c2d4014100d0f000e5198030a400c0003035000040b944050080c2000001d83e410a80c0c40f10f20300d0604090700 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 877280773 1250 877279523 877279541
    0x21c02010c061d0105060904050a0b0c0c03040e01060e0a050a051215010303090e09070312110f121804110702010e0307090c050a08090102030f0a0b01030905030d09060608060903030a 80
    0x241070410360826545041c1180c2c41c06454101500d0304518280b8074030720911442c0e4114000b03d445040a01d031039540c460361880c000000a101c50515030101d0410b0303d850090381c0440d039021040d00d85440e02c8071750041d00d0240c00d21480f800036180210601c0e550400d61403c078260fa40240c0030110141c280070502c0540c8010145200041c800c10700000411000e4000301307406140b1a90b038000402c0d1030030000f0b001141000c3c141105d82c2d003049400f01b0000e4024032503161110f03c2750800c40c406642c42c40d02d19003001e281100000c0c03139015920b1900a000c07003003802840090880640f0000c21a032407400e0204030b980180f440c905074241001140003540c06030110940b110b100900320303001315071100061401d0304c0e22041b8840210303001040701d040b11742e0030140350341e40020303007038002c42c150718003801c1c8100c00c4640600561182640c4183c4030340030f40d00c2904120080b60304802181d070754040310505003004040c808001e4481501d4443d020031442c0010038000c0c083c455100046045495412070300d401000380d00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 877282023 1250 877280773 877280777
    0x90a03171308180d05010c020f030a0915120504060e010e070803040311040b06040303020601050907050c0c210f0a1a1009020d1401030f0203010b09070903150b150d060909021c0201 79
    0x20700c40025942ea22110444c0144500000f0805419024001c1d14114007001203411341d802c180000c5c0d03042640045600119020001d10b1a00c1c420b0044d015580040c011940c0003002c0d041400300400e1224a81208241004a00081200c041c0e00080951a00210301504030340e60002c200800100311400d8101441a030020000190203241000284503a1b04c2a0300440160b00104010082441e0058940e036110046003045442e0088505566444d21082040746106491040c45004d000381e02c0c80c490303401d261001049442d00c04c098a400307aa01d050610040301c2c2c5000359901080e2a084854020303010320024640c104016080c034050760701030341001d0790740c20080e940c40d010040c0c5000e10b903aa1034000d41c0201c200074950041401414203647d1a01c030103902449100d0148100154024100c008890b003150819502e905115900350260072241c0d1400d034408640180940c1d1070301148010021081c003154201301d82581d41903041c060300d0345003c010307602c0408120074072010f030b5070800d250700741d64814 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 877283273 1250 877282023 877282057
    0x50f1806032b02010c0801050612070c050f25060215040809130c08150307061b02031b01081f050126040308090c010e1323090a03171308 60
    0x119030080d10b1460035002c509044601108a0030000b038081c4502e0030f800140c0d18040b20b1b0307581440701240b41c41c4111008030440544402c0010342840c4900f0038100b1042d07000f819100a94108808960741c2c02c52840c008980c1845581d0305060b02100c0f00e115011241d1503009007084d51041c0b0000104554010070544a454081256004540d44c23102200804801d01c84000b402c0a842c44004020000041900c149150901001c0006690025a4108847e61480c0c0f1a030403006861004280d424002002501072081030000b00c5024010607100e040d1401c203076a014810398402a481c0f14003c00f452174002400f20303000d030074005948031302e520040d5090a81560f601489214075040891941183e00f44c0c00695a04244402c1d09410700140c1250082441d00c2120703015840c1c0007a95a00f220702d40c0600c410359071018411408041072184900042c3c40009900710b2a01a0a01d0744030301036182d04600041c10300c25020090032100c450345000f485500c20f01c0103203950b1b84e90b68110541c0000d0340c0d00c0d00210f007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 877284523 1250 877283273 877283293
    0xb0d0b0f1801020d0617160506030709080a140606030703030c111809070503010615020601120507150f080f041a040602270a080303130602090a03020622050f180603 72
    0x42400207180b40004d01c5000118035103041c1030000c000c01500141081c03070b040058250300c0704510030740f010161801102c0303883c0d50391200306094403900040d900c840e6035401000c010364248140142e01407001d503404004d540140da1007400f0180c07101d00a0100070086100c01c0101004160480c20601080c0c40103407490021030300304813903c001003a0448240c10799602c030080c1417110341003c1c014040201404004640d68001181000c0c0d02d9910502850040c20200d940d124107000c000c00442d03000f409052a4a82c01e4044990014162002400d00b0800301d1940008141d44403011000d6503c526004142002044240c00d040d01c5100c1010b04141c1e070380c03a001e0101c0609080700c00d03428284501c000c2d0800d160001e540707040c030100c0000c65024001d99003047c0204101c0041c440303440140b04d41e2049006a4440800c0001040517045810280d0091f80229030f200c94050108110b600c120b401d800284203595684c41006001c14039040c459800c14507150090403c1440040040d410a600409031f41e9002d403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 877285773 1250 877284523 877284571
    0x305011e0e190f0e061f060905040b0f04060602060109051b070818040e070305060f0106020304210b340f050c1207030c0b161407030c0605190b0d0b0f 66
    0xa0800800138180e0004801d111406070302c0c0800b450040d4003050720240300b51900384080c00380c00241c45528090354954501030f1440c4c2c0c42484003040707018010402c1003426200c950081d42c0300030902a0300e81081ca80300c0422068100494100720001040340c10f185031107001d80c0e6a04030f0b40c014061050412004442400503a920350050f0a410300b2458003c1c40381c286075082540c03400e440500b01380e00340e07101100144400ca5000c000c071015110b0803400583c904e000b10a00760445901c0000c051328682800b810701c588032a0707400441c2c1c4900581080401d00425000d50412280c0040000c0c40205002c4610742c501c040c0140d000c2d00d00004d0000a0340c02e4413502282034081d6500c4024110b00040214000108100340d122620341c211610f02d614607404c2c0040a8003030014002907104ca108040041014820188980c924810a5a102905102c5402c200b40d4040340010307038980303142165080220085640c10035200d0301c0112900010200c0b910b486a01e0400d110790700103804101107038060541041891 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 877287023 1250 877285773 877285781
    0xf06020c010501060f0e0f1c020604080d051305010527030309040906020d05090f0a1b05120a0302010f180831060f0c02060a0f0203190305011e0e190f 66
    0x105131600c4003407002074076090080006004100d060b20607903200203806425207600c02c90416100445030107040070100b9000240603409a644101900c1c0b10348100e05400580c00b10103802d00542c00c1c0001800d040e03d80005440900902200c980b284012165030b1402070201c010540481c080641070302d10700342c1030390040f07000d5070b440d035906649160b0005001d00c1e20078968031520382d1208110780078000c4d100b100200715483e5980c1400c0a046d00b0181807000c1e001120b51b041140041400426010556a8890b40c40f0b8448204034001e0b0095403a041c61041400014000c11075a14280000315030441400e9031051003d8224a641c895600c011b50390742c6180da6094441000745258030f6000c410842d1a0500c02031504454111450403c814074402000584030380d4141c40081c84503040000000c004804101c0c030b1801850302100d0410600348800305529050f40c040342c180c1d070290101000c003503004004191280307018481e0a030740201c2c010024400d58841751045000308070b090760100707070840c074110755609071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 877288273 1250 877287023 877287029
    0x2060c01060906031a0112030c05070e07020c0312030c0f071104110c19030e06090d081303031b0201020304050105030c04032103050a1a010c080c1005160c0b01030f06020c010501 78
    0x45503580f41c24414080210880e441150808000000a6040c84990f00d08404851030003000c1c800404603076410002e0511804025015944500c5081c0c80c060000a6407015028642c500074020300d84d158180690700b8044900ca000000d00d445e01e420300044908299500021064602540080e6840b50079642d0303000d5000840725202045480700301c0c604041c2c1c10006d8a0707000317400794900c0c1c1010b100002e0300458030031444c0e10215802d40e03d83c40c1000c0803902840d54648010005080010207241200c0a03649201c150b030300030b90f11200f0038668100701c00e041c114003402c0680580d006100c01c1040358428401590f10014508540d820155203541d11000e00003454810052034034084001d41c2403581c148601136000c1002c000c00e00546071034006c0c01120320180880c4604028007101c5050a002c5200c04a41c145040700c4200c03170409417480f0101e40184415200300d02200c1041e801d96191501c03a44940c01100e03080500c81e011039103541e0390402030a840040446031143c0a005001e20048c0a00c195030003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 877289523 1250 877288273 877288289
    0xe011206180b120c010f050c01150b22050a090207140115030312021305062d070516080d050d11070308040309060512060f01110307060b032a040902060c0106 69
    0x2802c540d6410018202a0b03420b68101903400802d0041060f030340001405003200305414a2079885240220382e03805030030750b00911008030320280800581540720200414810b0788403020034110544030440d641001c1c00ca032081d213500c0a568a818011401540c1c01405080d204800340e88a61102100c054251a4100b418a0700160812020420b1607003010000500140c1d614085180603c05c50f40c0ea0304100f418020780e405898080f418885010102e901010082075550503e658408091141c03e03056104010442709405840240c800d13014561640509a0f808080506585186440c040b285070700034421408809440300c0819055911000040500500036510810b03586418100070340a02c1d05940702404105041144076207110040c00c0d055080101111003848c440c06d140b00490301c010400d020817407140400102c80c002c010031a880f10b4918401034096404103682c40a502c4544441205003003507861b904081040d440c0b0f0194004104284003c1110f400c00c220b00030703202d0855040340c000801d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 877290773 1250 877289523 877289531
    0x20a140a0f08181509040c090e07030b04020904060f23030d08091c030507030b0f15030a02090402040b0c06011a0d180b0702010e07120804030f0807020402130311100e01120618 77
    0x1e170798100303405240b200c0c045505100c14800d207030000f00405110010705240400d0303030302d501c0c03880907560316011200d6080005009008058444048101c1c82c1d01511404441c07201005812041c140e11100c200c0b00858000c1c040c2130a080c8002d001d46a100c0010000c0310325015840085840c2e00d612094041c804582d1307030b00000c03145030030503000d000c40d168244258402c01d559090500c3c00da0300c129911242001d41e0744596103035282e0301c0c1000068010071350701a90150022a0100d510000307580a040c030404040102c42c12640d07140c500f03101c100b408007054042d4000811404a03842d00540248480100d408045400e5070500d0700d414500c40015540500107035140c0d08400440001005103401406000081801c0d02c0900c0c0d0b1031049038841c0d03110043c10181d00c0e210207424003486d541541d440e6500604250360310440c00300384940582d03450204a40c820040001c0000c11b05141d0351207428090203407034402880034180c00541c0d42d0900000414481074603400b000c6590314503a550310201c2c80039520041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 877292023 1250 877290773 877290787
    0xe100905011d0a0506130903110f03130b070803010306021b120415020303010f03140703170901080a02120f18010603261306030f140403020a140a0f081815 68
    0x31841c0080c00c0d2101c3c460401040c062603075221440070501489202e0001106943c614060301c0184540210700b07001e00840c141020040000300041015a012208541c09140c03204c04140d1030340220a00a00b0402c0140300600009000d90700500d40000b00e298200c50314180c6c01d40180c6001c0640c0d0b0140e06060011404001b0610301c519050010f0f205400614203660620315405025115448050300101030031095601c242002d0001e00d003d540c00c0b41c088403000048441121040d0303c8485400d0000d222880024400d88031442900c038211003502021307403140c40b010031b600e250900c090004030007460003141126035040248900401180b0034071281040c2c80483e54510904080c00d40281880c4008000240312800310b03035104416144a802c0c0083c01220b00e10444004100c0075180040003441d080c144014550005980104a071103000010b40c0058820105a141c02d4a180010104005400a000010440301c0078018516090140c3d078a080101e0002a0116110300c0c0c0208901e20009054 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 877293273 1250 877292023 877292069
    0x1709030405130b03160911070302100b01030e0708010920011709240103020a1406030f04051009080d050601050c10021b0a140105091507081018020d0b04150e10090501 73
    0x1200718242c1c90070250a048d805c0d02c0194442c820301c070380c0003805a503175400180c050303000394001130b00c19120404072001c468498004034000c20305024180d5080e60007030f81c440d41c3c82c00c1200d0700b0442d03c80180c1d41c0041d4071f29406000d001c0d00c1c8001d4101c12603401000071800d10600312401c04003002e25103c2c1e80c07148030b51560050040001d62600b00745176020401c6004101134403558101c94000c0c4042180382429611070515504209100c505a144c41b810103240d40f050011400244c00801d016140c2040b0715101e090040d00c480c0300360903a0141503040104503400741811603015190160503200358403140c01044000c076050641400044035032190702d04041384011800d05c5500c2e880b000e0340c0010504c118038081d0440819200a104e201042200c00029060000e00781c560b03c0140141e961200d1440f8130680702c0c1000c0d40110f506502058036254030308800380f41c2400340d6402607583e018011165070900000b018034000080900703c0c0440805030010702003a80d0300c1018001e00d110050850b144081c1040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 877294523 1250 877293273 877293281
    0x180d0c02180402010e1003021c0f0c02160b0d0209030708070e0a090f02151603021e12030c0306012106030204050a020a0f12090f0c061709030405130b031609 69
    0x801c1d61114010820440182d03003000404143c2c1e1411500030716045001c40c4210081e1082803c40f41480e9a16060304000e00c209400c40b0076200c0040c40d00340070011a0342000c9940b42002c224908070480c7d0184104500700000e0b0091051000300d00d005407524605902191134021a40d1060310ad44c1e200030381c10400302d11545c0c0307000d401c10310140040c010055952a54454251540700180c400c1544144212003c1c81c4c0c01e0880d454803000003002a1802e140382000f940b10362924418420710304106034003444201000c03a84041340b21103a5071107800c0d900c80c8142c03851990401024507040c0214010a0b44065841081f12202c1042e564004a1418210703c10705c0140c820141c44403040d640180308a00c0b14503080104d40e03040e4201c2c0d00d080b00640350040c0300040034201000c400380500120121030024085200301d450b0944089855090714a22400d20020041c8001c0381c944000c0d030400c0c0018030070380c68901c030170381e114843c00000401e0200e07014000a081919242c1c01c4000f001144808001014503801 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 877295773 1250 877294523 877294549
    0x1812011d03030a0e031315030603140115120309030f030e06030103050102031b0c030d0c122f0a1e090b0c011d030a09050d060e070315060f03030e09180d0c02 69
    0x101071800e1079014890b04c24000903600400b40f51000d82030070700747d240d8403d42c000001141c01100c490714600c20b2001c21402840c05c1c1d001c401400b032003000c0200e002e1108425809419a055030b035000e01c68070307684070059590002c1204900f000640810300366a96181c1000e14040c0d401040010795a06150010100d090014001400040c00a00518242c08004415100392462086011410301c0c241c4500725198410840441d134054a0110002036406402414008152506094150155426040700489c1c040c13041c0e01c50000e0500d10880c1101403005542000b48692402c1c40102903441d1000107006400052240b81c0350385d580d02400c90b10400051003415080034480248d4230f0042410001400c90312280255801a040241207004220495122070f51a502d41e00655103210749034a04548801441e50719810b5490a184000c14070f020520a4102120b51546651030724030840720902c1441319000b882c018000401804a8413441f000740040e400103a21075441c9960300000f48100090312074120 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 877297023 1250 877295773 877295801
    0x3110c010206101509050402180307090b060405010c0302010f05150f0a24020a060c020d1413050f0d0204110d06171902060409090303021e1812011d03030a 68
    0x2e040c4042100541c560800303441e2405600d1000a80f608810344a400d15948259001440001c0125043c14544118420104101e05480b4103940d2007440c1010390b40080b000503400306082204110035805001000e518610078000070810401d00c141400c00c80390119110104540c944c29464005e240a030090031003000300302d6604070311a080403a510803c00b04418160041080f001c41180740500810112000951221050104006096000b0744a52107501c42002090005101140580f244000e0ba1800740061120002591415041120380005842c1064000410300403980240c3c440c0e001c3c00000c0d890f642605982d8a0916100804480c21940b05048046480f0000c2c19504000f040000c103806a14002c2441c2000c01e0002550740c0c400c039401200350070318000580003015090340140c0b1080d401050112a5085184280d84280c481c0d80400c1e11601c0a10302000070900d0810380c0c107803504418100000e064880c910000d00e000c601c803003010b20a94008004c00c98204580d0140d084146260 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 877298273 1250 877297023 877297033
    0x907030c080f0601061b0b0c040501020c010903150504060b182203020c06090301020c031b070902030103032c3a0c0e072f06090d0507140102040e0403110c0102 70
    0x50301d1469200e007010702a85e81004007291041d0940c2000800d68958103401444124250030b1041252040368400d108582c05809041c04c03000c8250300642d1103208032600305420302d4500c510500c04200600d070060085991994139106045c0c035403284c03181610b4071521000c80700d60780c0c14440c072030f0803400c291040d0182c05007010548010010f5404034105800329420b407010740e10782c203480b800a40079004030003003615540710100706847c03a20301d0410000b402c00100c4003078800c019220030005040e032109020240114800040c52510301c43c4124866514101440786800d1421414000450525030100d08541d100c8540705020300035000c203900d4054001190b42c0800103104540d48040070901e25200712024520608001403000d0300907c000182c0300c4006200300d0f680c5808140140d040c002000b2400d00a00c0303903000258903801d000412034894011511464280081540d48071400e003554181002d5a54090000140c0041300203102c2c0d0045205c0e0b01e40c0c7c51504600c002091a00440c2d1071664119405 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 877299523 1250 877298273 877298293
    0x8030c060c04081b0622030b070c030914010c0b011203090e15120c0306011d070801081e0c04020703091d01140907030e0d0305100504050603031207090e0907030c08 72
    0x6a00d6004141c0481ca800021501000003090b82c000e1002d411b90382c4881c40100008040d07044401e40550b803180070602800d0b1030b66a0100c6030441c207144000c011411100d0f060150b1642240b01801103201450100e004048943c1d03540e10908083e400b02d1195070300b0034134020403d500105090040d1000d090b0188031031a22110742207142d0b0343c0050041c0203084030244880108420f008051320548041c084035403070f503901d01802c007044062401c02d6001429031004121560b10507407103141282e5041c4020f20300c1403584504400700c0120140941c0d2140f1850701040c44ca0b0b03d460014140c840d000c0d45070a0104c61070901c1003600c00f8401020b4600c90b20300100140504c14103d030000b8192102920001265580d659043e00200504070600c4054440c0a540820499264021906c80e2551401c444480c0b50741e1403d000a6800c2a910f00d68990801d010210480c541200042c0d4044c84034504000c1e19550381c11007440401080d00d40b2070baa5000f1400c1031003440300500d00d810042403804010212092 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 877300773 1250 877299523 877299539
    0x3060f0618090504032a0213180b0702071a040815071209320c0f030a062307020a0b10061b081b01050610050a0518061308030c060c04 59
    0x407203029101c10107580f9804070b002c3c54070403c9128a00310f07130050ba50004c0ea050203501082c00ba01c115040b4401d00702d0907004221942240151642044a6502c40b42440e000e50344070040c4200060515045220b03950002030b407050740c2008060070305e135007001e055035903030400041c81e06180800f900103140b107400505001003194484100d003601581e20300000742005691801d0039058044442c803481032024400b01c0030300d10810780b031901400d0610108451001e4999828031032402000c0090b10b9160300a090b031000030600b1504a000390700c0c11004038070300880885075603a1a04c0025117005006074410249031042001c51140c1710b80000140e0078620015141007801081110200c0d124003001203050381d50400c01c400e00003550591f01840c04020340040c24810203600070502200e24a2141250804220071315003d0300445081420b140d6400d40ba104980e0450047c000d4071880301da4001c2c81c1000250492801e10807180f003d0803004000d1a550242c00140310b203003030700c050000303a0488002c0004000d01d103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 877302023 1250 877300773 877300817
    0x160915080109170717070501051008010507020327030105010e0a06060519050a0c02090a1e053d0603050103060e060910230a0b0102070914070806130c03060f06 70
    0x1109410043d130b0390600d80c41c01c81019603100c134024400120204900d0100507040d002544200341d03010103d000143c1c1e4009150980e01300b0782e591000750704100841281020000c41503824590b0700d4003003441c12002103010908441d07090b07001d410000800828044501050700a80008058510740282054408805000c240d601c10300d081051050001322494601d01a0402400040e00100181150b2600b0500e40014006001c42d01183e43c4462081c01442c10f44c92003070f0350250b044d8000203c2180072002c84000d19944074101c038000c14020840c4450030303a905402c40d0000c0c2c031140d6400708503549503107080c1c07080e1103401e0a45810f5800100401000300c4001601e10203e03d14039a0106080280410782c8200040c20b4902054485e0341d4810030120001c00d402c441c4107120701382e080b20025690780c4540e000301c59880d28210542c18005021640b440d21401e105604408000c0a1001005d0302c6144041100c04200d40c443c08a5185d150410440040c0c01c845801419035007000c42414840c00b117204190 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 877303273 1250 877302023 877302053
    0x806010b0306121e10060312050c030f04090c0f020d0c020402030c0f070c0e01050306100510051b0c040c050a0519090b040b0c12161202160915080109 66
    0x560000c0005032440c0d81d021900f102c92a010341c20ba4400c455078003100320003030000104080c91440742800d9112040c503113206070790451b50000017108020581010841d05075008581703414152005122a0840c500c0340300c0108028200c0c01c000181c001035240003c0c0901900000d500191741000b031213003801680042074807080f00d0f0304035001aa030740d8070b491850307070326000b10b162017414118041200b00c10010350528840645102003c0312240342c2ea2a001c05036601c0e8111034980c42c80c184000100f281d400c2542c0b004400c13805074280581884070b51b00c0340a00c421000403201c0c0d119030000d02003c415007098814540303507800c503290040c0341c1049014003429510860348013102ea4031b0150710281145110748601c20203050480306440d41d8999491101025801612660748a4010071103203d51003810303841191901c2c01d2642d488454641c9948408802c0100d0841b0304c2d09501503030740312445481070040e51101410346442c0000307000e00011007030010b01c1d955410000103030b0314004194011544203404e100d01c0b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 877304523 1250 877303273 877303289
    0x405061302010908071806090209010c0311030918041401020306060a180803071203141603020c010b0613210203060402102708010e16090f09020307080303071107080601 74
    0x40c0d10324600c01240d1000c443d9000075054090b4503004118500f411880341314640401d0750500055031121400806c901c6203800d00c1e4086071140111400180c01002c0c1c0010300c514136801d4074104015a004259018100121075401d008130307030b080000300710300c40000410004c2003400860035482c01c080072900d548500c4041e0b0091004a94441c842d0b0543c219409020f40014800d603620740203580351001c0c042c101040404080390420b00d28250051241280300d02c100310b0750809611083c1100f20a8000b544440e6046196540314000078880d5240d0800420807035010300510383c2c0c4203192060040e03c0e0b540070210201840403179440240966400111150403540485044000e4001608182c410140142e010020065040003a201600f402030764581140e0052000340211407100000300c2d00c80414102009402c1c80f00030051008600b258059a408405a1400600c81046400103450545140d0010032254000010851002ea2044000c122601414000c02ca11410035001c42e072626014000c14030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 877305773 1250 877304523 877304551
    0x80a120c0c080f0705010b04060602060402103002090d12020111120606131208070314091f1b0b10051219230d090b18040b030a0803070206100509040506 67
    0x5e00ca029402480171100c010402c009403592400089d48410040301c050380300f0740c424581c580038640556040e0900c41000d5541b80b420640d804903881070400044140d0304444d90901c6030100d6a1105581c0b848458060034007050fa00080c144020b003520744108200c0c1c0d030000b05110181d01c2e58001224160030280440f811516913188510000c6503407001d90010380302c6009044a00203006103800207010050099840b1010060751942c41001c902c01d03642c803030b50084000c3c503400c21205460100740f000c4506514080a6000e015022402d400e640c5400c1555041e440b41d003401510b0004004080080c40182e072a10040e1242404e15910f07000940041021866402d02080800400e00c880b41c2d0b0302e814415445880d0303001a031002d517807071149080f000007082260b0340c08240305c00e6100c2961080001684007110b120242000c0c40003600c044800b058044c4210300400f00050b030800061449243c1c0c40c0e0007411545080047e04502455562195000d0815101804082100410401d5114000c412010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 877307023 1250 877305773 877305787
    0x1d060d060908070f15050f06091018140f092e14100b130501030e0f0f0f0610050f04090f02060a050d0f050112031803080a120c0c080f 59
    0x150240801d1100100b40d018006980c0302080b01c143c04074550f40c2c0c0120150500003030950701c1c00084410031b42e0304041600c01e10340080c400f80b0780160519407203600900304034043d903560045480c00d69110285100c41945071307060001c40e0007114085540c000001c3c2c0a0492a06100b48a16100c001c2d588150a001130407100141c01000e01c2d200101041a0128040280c00c045c1d6600004215041d90302c46007247d8603860000c1d100a10400340c84140d186000d20000c0a845d100040d00241807044464016025800107408621403d001c520311724250580a03011203000c4454846c20440014a14030214010b004240101e445a0f0059200080c0136034001800c552a800c1c200881116903000030342c0000c0000300c8045003035214000c2e1104505009082c411803825150800c02c0c0d820034060080518503a00c2d2000110788584807009225100342c507410080c0d07890b9110a01182d00050b02e1502145010380041c1801940c1c1c8920007440265280038200500b2641d240d012901c90b00a039404000008940d039 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 877308273 1250 877307023 877307033
    0x60103020913210f180b0f07020f04050412261b09030d020c040b010305090307020d0f0807030c15021e0d020c010513020418030806010c08090319020a1d060d 69
    0x280622421400d0340c007400000754080245404503c000d5080068172095a400740001d0b01201401650500104142801d080f070070354035616044190280da215000d00074a034141c0d00c07584a440c4c000e500070320180300801e0500a000d07044003a04250f50381c0500e44441080d0404130101c0056802042101291003151800b1200300300c05c1c09a0f85044c1e606001d004280d85a0503000034405004280c09d6a0138803a440d0341000644c2114401c03102c000480d00204000c00040c605a4035120390729124101e086035146c41505c88403400d4004241c2100424015007840c424088a4100ca2081452040040d0310308811104a48a124003050b56280c000001050743c62070f08102d501620707015201000200542c2c074040e215070824a24142082e03004a00d8035216441801290210714038644d0941c5510302607071500c1c00115829030a540e0305850b40c3c4000e0000c800035540502511141d0131a010050f50802c02e180100f102e602010b51000303248986410664240e440ba5880c4a41d1019048a941c05407a40714100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 877309523 1250 877308273 877308293
    0x1080108100b0a050907120c0509060f0c120c0105090105060d030c0f032c0a09020903031215042a0806010c1106070c0b070312090206030a0f060504020c031b060103020913 75
    0x146074802d4640042140321a4080041c1f070544261300c00030f01854180540a40c0e5074454540c0c02c03a0408000c1003003282d100155802031144401000440d029220b10203841c0303040c0d400520040c0710b10794544c4244001d9140c07d0103400c0e0030801c201c400e0340d11f04058bc1d90207844009001801001500310305640c809050094441c24030030058000d9001c00c90412000300044400504080d80c400e03001c0410100e0f1504442c82501d504140107801503240942c0c90030003010140d4000e10603144400901101f00154842d4095001035010900218081c07404145500c103200001d15212810019403204100c40e03aa400900e0503000760704000030a00410f0a03801240c5d092107039600107002d0040d02c000c006034086400c0010300f4214003c1d03070303244109100c2d25101c000361079440c038010794095018030100b8490740c0c9950003100030703031310107400040c51a6558000c2000c1e608848902e00143d0000300300341c00e0f09000a400c408500103054060940c0d5030455002031040100030745030904085042440c40200880010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 877310773 1250 877309523 877309529
    0x609130203010510060305010e0708190906060b040e1b04090c021c0c02121f0b04150b220b0f0c0312010308092d22060f031101080108100b0a 62
    0x244264a424804c1d4450100b42d4456100020b11741000028095059109a4060301c420b9440152036204c0381c003490f84030b0316221055658a03a403000500700007251849040010458801800c1d200c903c0d0004000ea507150051100980280301d040041c17800d00c208040f1004c0d60f124001c0080d502c1001310003280350403000300d12a082c10045203a9008100e80141c40c0c0354070b6500c00c4a81045034040000c855840c0c29800c981c080d10407154001504682c21150070607a5400d0000c1c00005007080600c0c0403c0c0c0340c0c00140c1c0039035035040000481e0740b12080c001c11a03d641e01c00c440c000f110505d1902002c6001d034481c05481c826110f6003c524520b1070002441143c80d804142c8a61021958413401d0201040e84000201407150032814024500c4201e0400f80351450360000e80306e100c3d0a851601406225505100210380600c00704d510f00c0f10303d20052080c8009804000f409802e030f81c1c1140b400c941c0d080085403210b41070103402c4004100741240042c012000e4010082c1c0403c0e201a80804120b456509030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 877312023 1250 877310773 877310779
    0x80f071a250b0f0a052a040f0e010e061905240a0306140f06180a05030a03030b01120c0c0f06110408010b1203090307090207050120090f0415030b190603120908030a0806091302 77
    0x14000127070300030b030303c4a0721350681d9a444030121064680700b0421400340000c003405060745000700010841c0e072910800b510070749079030b149508095158108941d8a160f011314103d2011a0741c40c0006d1056038044500c40e4981c030020b0300c0194540000200080f0035004180c42240d1080d184035402009440e030300c2000d4000c0c840070302203e03000f5010b80b4000d4064032200280f94005a40d0062104424240740100c2180341c070580c40c2c0c1c0301c41880070340341c0c01550122444c0c00e5900741d446800e600304a8104500500c003c0c55040000a4840d90500070400700303d144100e545055030045c040c1040603a0081031030400c5550340800180c5d03410036440c00501601c101003044d0820012008600c00300116040141025002200c84a031ba1a6100040008030f800300720042a001d07101100c1440000c000c80242e036080104501ca66401000c0b4401150036155a901f0464281c503921034003031b0f0500d8008404c900500102c50145090071407100c40140b040000a119500c2100711034042100050046d510a0701140c000d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 877313273 1250 877312023 877312049
    0x70b04080a0b071b080703110f0c1206090c0d0c050312070605180c13020c120405030706110325050a0c080f071a250b0f0a052a04 57
    0x40c0148a807500d0426500740c60038454000083c80180c85030140150003c848104080c0c01c503015142d044103030b0010a400c80c00d21001c00744403260200304008020f4042d100c0300050034252085c03814401c6000d81a803860180e40d01840920240b00004207641124541c15140381e204030100f0f0801c20032901d1241d006c2a014012410b0b20030000ea60b940081070380900614082c04240c403400102416550039680224044d00030189060643c0751080688000d410906000b40c11700d07000348600c5081c0000d9051194003440005000c00176400c0034004580140070343d00700160403000c03c480054491003083e200c0402c0394038942c51107800d000684080c400c4e55800c807080368200c5000d4a01484810301d00d000c0d0852521400400210074100011100142c91210f044400c00359803015590701d882d001018000c0550400040c460810304442403103844041c003440b01c010250134007180038010448058055140c1ea07041c03000700080000c66000903030228607038803140c1719000f445040420303036070046402c460310607004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 877314523 1250 877313273 877313279
    0x90e0c16081c0c0306290334020f160302091305010f0501090b042708040e04030c1e1112010204050402040b0702030c06090a2702070b040b090c060d020c070b04 70
    0x903070350041001000f940c07800c00c0303043d40b00c0d03483d1448850f802c804146a0380043e0a2000e02814040c00755400c826580220041c0d642000d03183d00da030041140d98000001e00c02d020310103240d54108000d40c03004041030064980080000307002c006042d50340c00042d0040041401148100f040da480740203000790008001c001e04218042048094602881041842402e1100c415400d2505206004911100d0000c6040c00701201c43c446005c2c105c1a00c06445100040c040090b0314824024002e00c1148a651071080c544803601d4414110400d64110708048400d4810050000e10b040300329060301c0800f03c8180e00c0140001c00c03011302a109a80190340c2050000c1000540c0c0c21320704000e0400c180c170881c1030360b640e51001d4042c003145020f20359220351f10207040c213400c00c5010104c08003030600ca04001011a44642c2d007080084c20780c0d000480454001020f0b00400081c89800580285c001c1e60380000340c68130b0140d120000e03d040c003c2c800f07061809a0700140701e2402c043c04001c040000e01000074501e413145d079 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 877315773 1250 877314523 877314577
    0x1120809131b0908010e03180d021525080304020103052a040302041d1905011b0518040b06030c0c1603030207030302190c060e0d02090c0a090e0c1608 66
    0x221030002d140c00300700844004240b0701018050fa02e07024211900441c188000a5410514002c1c507515054215100c0c1c0910b50158540290fa06509000c41003080d507100850740c111082441d42828401400e0f0707880c0d044100041e4104200c90300701c0d80901c0d0200b0316440307010390007841e400000c0200c01c1d000960b0602c2211000c140d0040c00490303000302c8042000200c4601690081c1d116110210a0342c0c110b1000b800c060702c0c10410061045000b8000011078003200340c0d0108184900c1d010590100d0030208510611504402d40c0d054070f898181c03410300c0a401400301041c1c0d2400098a0b00f0210140420341c80b41c0c58008000101c81c00c004070000341225580c90401075207540b01c5000030340050280001e0b0340440c11030640401c0c601640010310000c840d1034110100c1d080440e051480d5840b912071500403001d60749250031075000301007089000369a0201c850000d0000242584445001801c100411414091540654412021a10f0101c032400540e2405044a105440c0e0721555100319410b4500060 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 877317023 1250 877315773 877315811
    0xe19060609061107050d021c08030f04061107020f270114180903070b1005030109030f0e0f010903021905060d020903011805030a1d04061805010902030112080913 71
    0x800e0b030b40351280028041d42105454003418002e03141c20420941011005007004500380d50300c4200000d4050070880c10f603484072055481034407003511503191841440705005061181c1c61300d050503962983e00d010107a5020510122815016600c5091240d070800c400c141e201492520003081091101115030711110b007034403030f29104582140264070a90340340700e0040712000d01d203000e124590021400c2000564481e128007400030403a0461558448001171130707031030900520f82141d1080e128000e0f032107422400181401484d0052610072003101141d840180d1b00040804280da406580078850781440070041032006800740e0003180c000d100003030b204040308010340c00383c40580c6044000b8001d100001c006000781201442000e44250020403d01140398055200b8005030303407400c40d161400d844030f07200045c22541c40f07a01c0f801003c1d0010b00241b82481c023603c511030140c01407a80450541d41010402c82051429000c02089581c000075446882ea0300c4c1c442a0760407020682c8240b18032600110f00032400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 877318273 1250 877317023 877317029
    0x31204170703240b1509010314060d06090501020909042307031a060103150f0f15021c020304050a030f15091511070b1602190201020303010e19060609 66
    0xd0025020540340d200404a001001c0380e8112091043c1c030300300074000f00603489110072400010b80c1e4465441c40790703881d2460145618007158549a495803032041c000740580c1c180d010345003a0a03210408000e95951a09256008182c000000060310303c0c00b46001e41c0240318601d2896400b4080c403040000b00700c00740b03c0d030f2840340041c0c000d00745041026035111680c6002ea80402046049194210f00d44d0025540f07038903034040c00501d408941c0c1c4500c0000b010741125290400011940c1c0c0c0380080c441304201c3e0b40c03c407009221754003032005094540207000751201505021080721811000c02204283e100b0002d0303030040c1c10000d0222249558902d001080300c0389107081220b2580010702400c0c0101024491081c2c6140c110820360071022545060070028225261004080107043c804e080124203412003141c85102100a404501d43c00d0b000040c2c0340c001d007020108546181c0003091001070742d001c001d8a044071031105a080c01612440d5480d60b40291514081080c40d1400900146255101105800b2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 877319523 1250 877318273 877318289
    0x6010501090e0403081803090904081b0a39080d0e04050403090e090703080d0204030c0b0429041806180b1c02011b0303060302090601050307020c040903030b031204 72
    0x41507654040300b00141c2c000c40340500881c0300078000655a410301802c2c0754404400c14103491500100c040003441c6603000f500c0c180c0e01d40501203003810b000311001c01038000802c6034000030030300c80352642d0325178240d82a940180f15400c47c400000c0710510f210306c071400d409000d0440d400441c20741c8070704020795204080d05108c000205804000f41c40f1703003058404c450107650590746154280b803e01510740b1030a80d024000e08507902c14101c0004c04101b0000150100b900205000346e0355515606108008030100c0d0482d182e0844100f00801c094150f517501070500d200344400d47c04503e080100c2818090007035134829400402504030a0720030301d80c030f684400b05480040c49a81c00180040070a40226045080c1040e04009010003207943d0300703a80c00ca0b00c00350f5032051400403254120490306094000d40031000b1000b1a490700c3c400d0046240c10041241d01c08403c3c6400e904514010100a59410014062034003c0f680c520095080c14402c2e00644000070f40503080ba043c50207121940001a0f0140c440c0c10a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 877320773 1250 877319523 877319537
    0x402010909060837110f0a06020604200d05012301060f0309110d0c08010c0f1b15060810050105040b091f150e041a090720070806010501 60
    0x9001e10403031040c001512000c10090802007590b820014000c4000403280100031081c1c1008420510700b40e110724802c503c50300c40300aa030803048081c40448000030201e40d100720310012040c0492a40012500e82c840d411455042401407086640740000743d00407101a0000c104c03402e203400380901508292500d40b0b05003004000403014100a0301d12030000e01a2900041c55001405223252094000100181c09003d02142c00e241c0800054840701e9808000c4603480c0d400102040f0b417410a11401194588504118001c540c4141004104a150032903005c0540c10700100403050050080103c040b4a10311b207010000151580c130000c0d601c0c610700d003401082600301000800d80b07051038098105c0301000a000360340030b07032150005400c40000640041c1b41b000d000120004111807241550540000c040d01c0e0754045011010500c000d0302e0485c0030482d00780e4940e0408096940f03030044d0340e640c000348030303d0b1a8076603500c2c2c0820740303038080b880c200341703500f948110380002c00c2c54000400c01c0d504030384090725584 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 877322023 1250 877320773 877320779
    0x315030601270902130e030d0207060902150f09060c010f09050f0c03190b09030d060621050f1909052d0f1b06070b0412270506090414070804020109 65
    0x1c03d5444400000f904072081c034000301c10b080307020740081751500c01200c281c904044400b0f00200c202d811601c010380e0f046072075018003029401d04801e40c4070342c0f254000c00585001d022a10880c000c0c46081c1c000c50051200181034030a00a0030340c89025034445022090203108420708002e95a4003884c03290029601a030380c943c04480c0360009000f0000e500c59900d0798480300d055203442c3da00c0c020051141d076a81c08100719003214102144204006001d040d182c181140581d444000e0070134080601124800d4503140a00c07042c80f841e111280d60181c500e01c81000c013801240e0592016110101000701184500407a48000d200d80d8003250901445107614200301d504030380c2ca900d03a61248686101103641014042611079040503140c861800c1300038200501d070a402c2c0c0e441c5005d9507000c0303509031492844a000ca21000d03501c80640c0b20303408000c001e07640f0b112110b50328040b000310f12485880c4c456080083e103043c0703030344468100049a0a4100c07016440303107040b00c0c01908000c003c9408900040300ba01d804 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 877323273 1250 877322023 877322099
    0x804120b27060c0d180503030f0709030213050603100906090209070f0507030e03070302060a0201020c010605221e1415010c0c170a0b09070303031a10050315030601 72
    0x1c48188181d9000910107626600100000ea40c07108542c000782e140c5070004011a030755190500e94002d07116200440e900d2518a51101612401070681010809003c074100050f80e100c00140180244009001909172214000603141900140c10720301424113043e801c42c02d201080d404010041d00981d6002156600c070b501c2110300c204004682030102d4020712039103020074811140400e2010000e4100c91002c0c1c3c40340c000500c6138004005480060303400080c50448840280101002000141d502007014102180e121352a00b800c88003c402e0707142ea54452a0490b1101c9619545000380c89004021041920104040c020800c9810f2202e943c200c03100c1c010a54810180c04641c00c0d04145485000c0c0c0c105414490100c410490f01e562600c588050070b404505040c14840c002c64012004200303103895441c0184c150355140106802c03c200740304031081d003610350030b0000001101515010356203030381d0b503080300541c804c5410707051342c25100c0d00c400441d0900b013000418000e0900303c0c680381004a110158 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 877324523 1250 877323273 877323331
    0x1e030a080912040e1b18030d0908060a020c070b0d05100608060904060b030a02032a060f0d0c02070906030804090501080a200409052506180b070804120b 67
    0x1442e40c44103040004205600c498410117400c00e00e403410b185c0b0b0816680120503280e801800e9180c03c0c4520003180f125061404016a8001b5041350511781c0e051441d20350040d84481c80208109405900010901780d15102803000307101801c00140040d81301d60006041d0401040e0440d071480c049011003d001c2082802285554800d040043c13000308a681d0380d81d28080581001480c1c0c0c0c0e00340c45410694030043ea420b00c00805004070184502085031990701c11098008141d0340e020340036940800c0032040d29000c9004513144000e400001144101850792b04a1030a000703a4850100365142c508040b0400c004000104100d500109060000340d0320340201c0c1d600c3c0c04010070020190000a20509500d400e56070004038020b000034030010304900030b6110780e810040e50b1480c82255170720800640050000729184003020b4a0365203040c1495007202000050b444250380142d9101c03100208119040140502c200e4004c0c0079090800d204081c0c42e8a8803000c5d0060076210055050b0392405030306219840024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 877325773 1250 877324523 877324543
    0xa15121205040b0a0c06021b01090c0b0a0903110a08100f050709180906021306020703120c0f0b191e06050402180906030709020703020604032c01050c1e030a0809 71
    0x3c0c16a1500301e18200a03201e4007400101116205c0e02405180071559001d640c520140d010400042880c903a9468101c12051b52900000c010139401d002c0001320941c014600ca082da540710b141c48200e52a0100001e8100c2115404004c01e44914403002082440b66044945001180c0e4424451600c0d4000d00b0f680510480c0255100d1012442c0000c414641e25040900c3d19405500010700d44a040ea005c210301d1040c03038000c6005039100150800400c03c050514005800107480d140c0384821340d41da00d1101d003084440000c1c1c6400fa55401007250342c60001a4071403056070380107003044200b004152400016180c00341d40c424052410f44c00180b035040c14001c540c41c11114946030b8813500e411000f04000200060440c0d1303014402d0b0301002c1388178030603440240745044c02500104a1460249001007002e141040c0000c01002d410006210207405009550111102424081d13164090f4408151501005e901d1038100070150f040da50300403035030201c010198150b19940f03035403c03aa13942444540c0e8052181e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 877327023 1250 877325773 877325789
    0x1612020a0b06150f0a0c060608070501020c0f100c11041d0609010507020303070c03030209030609070e0108010c0203030103020d050f1509070e01080303010311010507061a090f040f0b0a1512120504 86
    0xf20060380e121303102c40101070074501030078014a90801e944a94007100c4c641e410480d5075520040c070900c020342e010090070480500803150b800c980d41200002c1500d000b0140940407e00428161800030400c00031000c1080d01d502400400c106140700b5007100b002c401442401c0d0b0355002d81d101080c505201030082038842c480c070350001d44c50750721091b800715481c03410304900342c0405509100b41021540c00388034150054070007200030f009160400c41c01403040c50f030680c00005d03030b80c0c0b501070200c000710b8010050380d0441e83c04490316402000d00341402420800110310071a240c1c00341e400300360041c1c0b08103010342c1e020360350040c21210170b03545409090080c46030031701556400368000c0c001000000c442a51307034a2682818500942000c0160351000240c2e129952020503c1c001c0903422480b07410504685540207400c840403051034101360700c403d106080010f43c042d014864103800282d1003c5550041e10441e40e400c5080d08019965443e014000c13960140c04681c00030b840d44035218003510a41c25030701070b01e03680c03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 877328273 1250 877327023 877327027
    0xe070e09030309060714131815030b041b320d020d23070905010302011d06090d06021e03040b0106140f1c02041e090c141612020a0b0615 60
    0x244800303032410681c010422100301420803035003079502d030510072610092200080a00700d14005060382340954415a00e811004100c40310300304089402c40e120303c1d80042d046010b0001200466590710304995180d00940c00d08003100000c000c07010742107401780e1055621000b0000d80f5402d103908100c05543d050134042e5001c00080481030103c1c1c22240390514403400012403580c2141d800304414208000c5520028801365944010419560400d01c7ca2059840d2040320101d00e20990340003034110302502c81885c4c011a00400d201042141e00ea0440c0d460520030100c54241c886070740c5071002190300c11a42140c1602052000003085401240c03910841c2003128242820314540101c602001c0d046103000c5c807404407254240300d140701c00c14401000680098248000e030007004030b03003140d00d003a40c9610071041c0314a860048202154000a0181240030b82c50040d617513150001c1180040790312011f03010304504416206c05070043d80001d040400184a240c0c0c41000d683e5403070400180c06c500a251700545030007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 877329523 1250 877328273 877328281
    0x90a0203090c12190f11090f071107050303030112170a14280818121b071a040f23040b1c0803100801061404020702130e070e0903030906 60
    0x302c5040c283c44070109404680302907608840000c10269a03450075940012940c040c90207002c4045101c0301e156805481110550401d86140001000001c00300d104018400400c130413080000c1c44044010100281200c0e22541c44140c850f21000a05e0812500c407101c030000d041c0b00f90400002d40b03044001c1501d0f501e2000c0b80011010446030302c000402302c0380600c0d890303070f21940c00c100d504400c600c2140f5660312402032600c00d0031241d490050007640302c5158004a00307405d01c0380040048510289000b60102e2a10030b10008151601c03511307412100d201102d41c046240302410007030162085072101c1c0300004015590301c0ac202124080940340c1e094500e1050144801410150800510003e003d40110302040407440b6120201201c048102c1e58000008140220500580384100151540100070480c09103040c242c0c411401c0032091150140d9008142401559100c01c000d00c500c0079802400d11450114001c600e484284600514104581f154040b400c510000810340303115103010f100900d0141c135 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 877330773 1250 877329523 877329529
    0xc0603061903051009060c0503091c050705190c050d0309050618060304030e1002011a12030f0309010c093203100c03090606170303010314071205030702090a0203090c 73
    0xc0440c1103602071880c60300c0000041c0302082240c01c0c4000b10000024440098070f861410307500420825401c010080c0103100300000e000c074400d45904400d1025280007880104191118080c110016142d4018203a070394a0000c0d01c0c0280304403543c03203802e028040e1900c8000700590110440c401400040310340c1000e01450074620002d26008400d03031110340001040400094666000701ca003240001d8004104a81c2818054a10440c1100c1e500080c44038152020600003000c52500c80580315644241090003409414021203000000d0000380646ea4a8010045c50180800040c1d0320000342d400340001885105004030030603080d0302121032034043c524004010111021b4000003650500503c21004401d07249441405540340a07500c0120302c0000c40e08001c02120410340c414038042e2070110b01e036904000c0120482e419294403142407800c00311406013651909070349400c01540110582042010b2110001c017031b05c0c9040c802c640c0e94420f907070717038210300c0c3e00382e00095550030039550080d100e6204610b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 877332023 1250 877330773 877330789
    0x60105150421200405240d0c05030105090618010212040809040621020310020909070f09120807050c0a0b0d020903102d0c05030a05090316060c020f0c060306 69
    0x1a08040d03000c035114101e0300d4000700507800b0056600e83c42000039031441c59081500489070700c903140307480300511203003940b401d002800c4400c43c04500c200081c1c0008000c0000a8000c080030b4038018000b00001c0c81e0410302d0942c0c64070260390b01da400001e0100c01d552074140500850301050550064070b81c0750346440c1d0b190b2603260080304070503500649505000c9542c000160041380c0700c004400340040c01d8030140c01814108011030846506140c010082032480e900c68481494018800d442c010041c080540c00c2281c0b0416144c200341740702d1500489400c00c7c051080d02600b51280158266040070366500204182400d40c0c0c131450359011004c0c015504d9010702c903405411341c07034800380036100320003034440740f00080759050844011262070b0680c0c0d00150452225140b020001189401c0040ea800d1090150543c00010138046500e0b449000041c04030780280161610828040003a40a1b81c82d2450440083d00350030340040b0040c40b60743c0e0780456a1a0000b0205032824000e04218a1a211501403103210 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 877333273 1250 877332023 877332059
    0x120f05190c02190201021c12060e04080405150c070602010c0f020606010807050a030e0303101409040327080105040b0612030406050d0507031b08071421060325080601051504 76
    0x1b50007150000c81c10004100f054031404061582c600f6000c3d07150401501c22110590082d91509003050100000a1450000c95055071011660440f6a0304d00305081c07511840b40d0512140f50f0b0040010000e941c507015089903000d07204a888a1018503174030b4000b241d580d43d0860780c1c640014080400324031114005c40084c4900d00c058540441d29140700381e05e45145a000740e8420550b403243c44410028503100401100c2d40680c112840c2107182419280145081c056200c4003c3c4201c020ec07000d4a001070000e01d6800810000c0300900080c42c2506001584107400c588203070161003080c0c2900c41c200000b004035420340e001605d4550900b1500040c030340040400900c80c01c1416605d8120074032005410031080d25000990380c425500346481000100700d4040c1c10200c07900990180140c1845880035003000582c403200c05042e0909946400010b8903010340740c1c44814102d519505403000c0440d0331048131003516082421070703260380d07a43c030284071800313000e0a28492030318001c1c082800720a1881e5030050318 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 877334523 1250 877333273 877333277
    0x1c0b010302090a0308040e0109020405060307050c1606031b080603100f0b1807020d1d01030f1d0706080c07030e2101062d081c120f05190c02190201 65
    0x1c0088510103d80c0e8450b2a400950702040c0100782080124280e4458031301402d855a01982840e01c0e0a010400d140030240c8844140a000b03e20082031804c1041522058007022503803480f07903a51076031701a0081032038600141c52000c908590b2000103000789621402044091b0040c182f030710150b80e60200410781100d000d006c550321000303002060f98403d09601a41080d1400840703103400e0a44c0e019140020f04441402440f200c03560901c1c2442c611441005100741c213080c0821a50030600b4098002d2040680c60406800003051015403444000742c00020b40705a9240c00c0c442e511100204000e80c001c03031303030010001401680b40044504003407001d800491040c00007240144401c1d20018250b0326160000450014001d01100000d880b010f103c83c500c8000511100a086c20140400e40319600300d0708122410254040440085c0c0c412150360364400509074041000b41041e2800c50082d1105503510241d07c494091007180034005c80c40340c081d06040c1d80c5c000302a42483c0310040d07070495401c0e40d01641 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 877335773 1250 877334523 877334527
    0x60c171222020f1519050903240106050d020904060b090103270602070302150c1213030f0305090c0a14040b011b02040b130e0c01021606090e0406060b041211061c0b010302 75
    0x603140c8100f5105e011800703116200c55480302040d50500d0301d0920341144054000100d5100e4642d007142e02d1102e54117596161902c0380d5182e20701c41d142c0c2c003e0720440440c103800c6494200005100403a180c040e00003040309990500010301c2c01b2910a403402c213075209128669080071403803000590340f0381c01056014400d0043d980b845040f4580b040f04218211885403d0300c0002410b4900004444852540160086505020300350141c40051101d84640b00c00c60900d0359403404500010001c00c8000c01500004100c3d4038620340b84d0310410740d54806008090301076410844206007640c000d02c00000114008498901880d1094003000302400c401c440315030700640c0d0140c001c2d078010040e01038079507095250320043ca040a4800d000900e0001c8013100035044554051040c0079450f848041c04007114810000700c407c036201c0e03041680040c400c40c0c0c0300c1c020346040090005420900140c10441c050301a5051050420014081c00b0240c401c81107400c40386402c800c18031503214020340c00903070003404c103150040c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 877337023 1250 877335773 877335787
    0x13050109080a050301091515080a1b0302040e0c0903150a060e040f030e04050907120203030c0d1205060102030a090603050a1b0c1502040f060c171222020f15 69
    0x2070040c0e44003088810029500100501c40350303085c0c4c016280120300804281c64001c0c50001c40e44034011640d109407040003445030104117101426009000741c00c1d09040500040060303031740d02030b000f0b50091180504001d403000008400200140a6440d1140c1c0500940495115080410100e020007842c500d1520741c2e640340030a44511500742944607921440081a45035410306020301a80d80004940d0300c22030402040060860010540008451303402051102d8403401c1d20010f0b0a50144c03110700b254510580000307001d0903a000c1403c80500c2c502410030440c903182c1000498507031050203880c0f13001c5150194100180c0b4443e40c0050ba01180d10000069030b030300807504020303003491401c044800250101c01c0b10018231040008003050345404900461a1620301201c4900c188a684a00020b0180003480b960a202222061241c4015034100070baa03112001c010041c1c2303007007042d00d0b120a81015111b68114841411000001c83e580080521892100950422001e80001c0701d4100742e19006000b4a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 877338129 1106 877337023 877337033
    0x4060306051801140d031214220203151302222f07020111010203240423130203030309060106080610050d0c2a061a030613050109 57
    0x1285c0180802c5c01c0940d5890304405032040c00c130b4108410a82c2e441c00c2d20503490b216440e140307070540440f180000340c80d9041c00c8800000b5015403044500c80e503c81c00c20505c16034000c3c008940b1600300c0260342e0100384060204030fa01c6400b421b1800c0c4008010049000f02207581030703c002544a00d0546c14040d0380c22421500c104100302c1c0e8002101415644030b20303601180e032840340000750340e607081c01071600640c003000ca0900c0c1001c0140307400101c0e15140c2390250144191000c0c0204149250000c59603582c030001401e03c0c0203403604402001c0040c0c405001a6214801d980003511140d0b16100e4080c10351100203014510070b0188807284442e0541250a0340c1d40c9041400d0001180e82c0001030554925483c0c1c200c0000d101a4001d402d2007017034506546801c140d02ca240b0a11a0380030500d04010308185070000b090b03040d0420000114040e03007102191102e14040c0001040109090301c0e4 = true := by decide +kernel

theorem cover : BRFrame.Cov 877158273 877338129 := by
  have h0 := BRFrame.cov_init 877158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 877158273 ≤ n) (h2 : n < 877338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
