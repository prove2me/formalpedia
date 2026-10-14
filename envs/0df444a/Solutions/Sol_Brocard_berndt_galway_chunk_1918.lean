-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1918
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:08:58.221976+00:00
-- url     : https://prove2.me/submissions/5f221e59-97a9-4e6d-bc96-36e06c5616aa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 344784172 ≤ n < 344964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 344785422 1250 344784172 344784179
    0x218090c0c060a1a030d1e0e03300a0c200a090905010f23060102120c0312010f1503020a0507081b012a1d030a0302030d0b010f0507020402090109 64
    0x600c0c0500403110280103545a0444c0960320b19404c0310780741c13411000d0b130180c140c4110030700c2c01608007011800d01e03114a640c40350710284507a10405100c004140300400799041d00401d100103102004558402c4160798501c031038212501480e420468034480c5494890302228115034030b4281c80248110140d540740c2e500e18840b50303020f940e00d2141394050481201d00007010f1a45040650031248180c0b040b0111519110784028058070b440c20146410b4402e000c1d0f244c656880b07100403800e00c0e05192100b40707080b90101d202800e031840400a407480071031814607580759a9030b8810780032498500c3d01c00d520b9100e0300070044216140c0b2075001030a10840303e0030803601d048625514111158001d030255001c101e103882c0044030307000b030070f01480800450a00342034401c0e6180b2414280d1110605243c48203011071080118403401082c0103000583c84010b041d40c0c015201c604010707484c0c0c0d101006c1052024074200300052258094113004422912039528107080c50b09a41c284402548140c4803141032101021001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 344786672 1250 344785422 344785447
    0x7081008251a0307030e0c090103061a03010615020c1e01120e0604031110060e0a090c08030d140705130b09030a060f020a030b091603230403080105010908010218090c 73
    0x202d1205207440756542c0c0b5018000904840c41c4d150341c070340250080c540c003c00035942d15070304030305490300044001a42c241ca142846d0146900e0442607400d5408c06500083c010440405e041144106800b0b4911758903031141040180944890b800500c040d40404184881d4840e21456504d11120000094010601082c3c240780900c100c400300d0000c0d08002491203c801c040c00101c01001841302c0a00659052050300694054010303c00c150072a541c1559409001040c1c1c4000000c000c0c0400703903569040035806003000317098500714104080c0500800b00b207100c2e01c5041250f500c600c0754600310301c116084c40100c00d419400244120750502c1003e600402113180391041d41071441000c0e00069403940b0101000c1c1c00d581c802031038644078a500008000030210f2003904481c49080500d000100e60014000000c0400300c0c26410002000101d810442051303000034030b09040c3e5100b601c8025807140e856130000c3c240d102c0c601d0451000070410301c036400c1d03d05000311410303005000b40c40c0c01814507039403000c0c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 344787922 1250 344786672 344786699
    0x60409180f050709110c06010b09010c0213020403060e030a0e010302090a0506120108010501051002101503080c060f0f090307020922031d010309020109030f0c0f030b0708100825 78
    0x341c82d00d4000220801c00b039001880350400e042c4221180d1814800c07424501500d41e4814401c00302240c1c1e00040392598ada06c07030701c01d000c00c15a00521007880c0200740b099100094102d40411901d10b031a00e075240702c64404c008207640d1246010784c4c404000221120045010350400107103203030402c2c11014040303520303601d08002d030003544440400d01c407456240c684410700313407071042c0d00050042603098106004144c1c080f030f9a0700c0c54141002c0119042c00059060040288990b1000c0c12540c808240b0201c003404c003144c0272b03000751035142d4070307109a071160001d40840c884251200b0807180e004201e110300500b00002400da021210b40d0010802c04400e40f4554401c480c07001c81200007505285080002d07500d031002c8040e00f440c00380303010091104243c0c00038000c1d1140d07000c06081e00c180c0c040104200a00c5101e0400135010103241e204400d80d503031420000a100695400300800c296800161280350000e240070b00316110140100800e4091100400006129040c002e2650040300808104104003420 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 344789172 1250 344787922 344787953
    0x60309050118081c15061409120708010c1b0f051509010623061e042105060609101401120203090a0203070e0103030e0103020a030b0a09050a0e030906040918 69
    0xa42e56a10300760b100540e8030715100413890f800c00a103401e80c1c41d00c0390581080f207201a21a2400d1294444c0e035800100c4890b030144034501e070780c0b0081d04500383d006250b0203d40b02c41200d10000003405810070044060b503040100c002d00789041141140300070003048440640d98001c1c2d000b002598a002c1390512007841c4290125807172540d13030791102c0d010440c0c00c041c540004103500101100c440081c0c1450000b4000b4400c400000c5800601d012010030400f1420088500034003088010030381000014540d1a5002c945140545440c003031903000800038101a51000d115032002c9444156060420780c0a40c0c200340c003209554100b0400700c40c1002c40c4180c510085008400d5040281150006032040500e8001107070040e007030420b022001000066000220320018a6003401d01584600c4030390011002041c01d441c00700d900c40215080002e00200355409140110300c903840a103c081074881d9000c2e582c1c0b00d8000c0395a00403104010030810395030181e004112200d0104416401c0b6042ea440d4900c03c1c162108 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 344790422 1250 344789172 344789183
    0x17070905030d020a0b07050304020109080f010f0501080a11040f091e06060b12010501082211040b010c1106071703091c080f060d020a0906120515060a060309050118 72
    0x80248400d2400300042846690248002e101d9410a170740c500c811404054014424002c0c040007060441e0300501000010b4840c050886041c41040315429020b400c80504050b0117519210010810440104050300b010341c0044200300c21030030307100c2448001e007000102c4d6001c0b40d40e6038000c0300004123501c1c0d02034415a0254004a0341c80141d0030044100c0d802c41d40042142031003008591620721048240e01c1c1100c009007001d103803e41c0c4401448107162040134901c0040003280505100700320314401d241d080030405a4007044150488070040d2089014040c01401040b14615207200c1031406c0001403403418403400a1003984000c4240380840c542054416040302e400411201e0407040c80b9451030350415400c2c1c9052000c0c0c0c24803490108400d0409800f05002d01e140d440a60259240c02182d8001481c0b00142009210780c4c1d4603480e81c84603485642146d5900458210310103283c081c840160248800070540c01c8d03854603142080e4000d0200981c116225501d4078088203100b03680200400105000e403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 344791672 1250 344790422 344790437
    0x50a0f0503130612060503010204051305100506160b16140f040f0308030106030f090209040f170d0e0c030d080c03090f030d021803010c050a0c02011e090305120414101707 75
    0x10f1813400c159034050b040b250003684107100c104400eaa41503081000d20041742c80c005042c0d1036032201d114000c1e140b5084650410b5001030103d050340d418401400c0d01e2402082e61040503154100072221649203151800000387d514074084514440b83c0f4010701c85600a80c064a02e00703955100c1104c1e04020300d600950751100c0c0400100121a09400b07220720f540444601046500501d03400600386602c041c001030702d200c0402c030744442005401520281c005804041e0541c61341e080340401070162a02c80c040280c0c6001d003a40e44441818006a128143c60031a22010700c20790343d0740c1c0c100740190401404030b14030b407140306e80d1200040710500c01841c0c4060b0905000d039a810b00c5044409140b14282a0307180030340c0c908111240b800394004103460a8080500e00f245044800d800100c5e080340e04481d0303000441c8035603c00740c07004641004040045a100780241c42b800344d01903c5280882c05140328038180400c0c0035013104030030300d0042c100b440c0d145001d040410722040c4008050404600413140b03e004500d11303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 344792922 1250 344791672 344791697
    0xc0506090105040b010605040f0603180605100602010e15180304030b0106050d0b060c0601150908031305040b0d0309061b1a010501030f0e070506030408190305041a04050a0f05031306 80
    0x3011511070143ca031504147c1d01c1d10f85001f00d02103001e0003030310500342051f50359074515500450142c20840d4064001200381f001c0e091000410400c3c2151b8801c9901540c6400040c2180c800d0119002034045120110389443d80d880380030403840310300014602c40306800108808000105880c59140c041d0403103035203403902e40c454954000308403041282118800d14051081d40c0d2001000140941550300e8000001c00a0b01046400e46030900150000101c60001144050b50800a100c8010031254121420301080441c00700303000c1c2440001c074019001805108060280380d00901c460350101c1c44524448404d0241382d141c180c0303100d80041556035103188010041201f50380c18080c0d1060721400c3e00040213200c11607001c0c3c960701c100c24850b980c0500d102000050502c07140d40280c8060b41089a0202e411000f1650014010f1004640c100c03060310211000804030361802c02c0301845954400700514540708180c07551003502c6c04413141100c0307a200400106507401158101c800003000c107a00c8a44c186100c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 344794172 1250 344792922 344792933
    0x42004050411040503030d0f0f09060f0c0504050315070e180601080f01210206040503010207031809051501080a060801060f0302010816020303130807020603043002100c0c050609010504 81
    0x26030b41d1142141038414441400156400301c11204000300800000402c000c1c500c0b410009044628515206c20b441c09000c0300c00d1105a400c520580e00220f0010000c03801c4815040d5081e0050340104c50305030740a6101480c9400500d0400380d0410294106107424800b09c50005410b450705248002344c3d404800c1c140400d82d60042c101030b070041491081c3e0340c010340c10540180491800d80c24815035690851916100399254002220701030107000e002550f031042d46003030140c080884000c00f0903003500c4038a070011740a03841d84595400381c02d40400f280c54110b1307071000440310a00003400700c00e0825518500050522024843d8800401503020b00c0d1602ea0300c0c40c000500068401840b503500210039140b0760b8404c03640482100d900100308440641100c05030300701260ba500904200a4200c080007040c48244030401c6800110001d12040e914600100d010051008032105100c000150784861903680f18801c60342c104c006540e442e450000b40070b1303185c0c0c0c9443e40360250a8a80c6421070355110140024000c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 344795422 1250 344794172 344794181
    0x915180c010e0f0f1302070b010f09090c0e0a020c010903020c040b031903110f0d0905100302132304020315090907060c17040e09010605090a090c030b04020420040504 73
    0xc42400c010544003149008035031404031840e240c5201d0303030440182c1d9542e40e60b401002c401d0211416001c544804003880c1004404600380240001802c0a035030000d0101c4803409144103a030760000411030150b00c0c261100c600101c000c1d0403024840d40038022407403225024414490750314001c1d8012f16030500100e060100b250b81c41400c041c040d4000c0407a0485003400d00201d241e13400c0d80340c0750194204400c5510780e400d015052602c842d070781c001d282c29039221503440101e03442620342c2215070401c00c0360709550603000ca2003800558000c4232000041080b20302c0b6030116560001c1020355490000702100b40006040360b00490750013000c1840c50450541c142002401741b40d0001c0030f00d004090320313800e058028081090000e0000c01c16155a518000b00f28040381c150380c01003802412100440c14000807043c081e04640c05078034080e09a11000468a0015005519946030030940811a0324115201d40a40d510028401d0b42c09c20703215500228040b0426001640040c2c080c8032441c0c68600701410001503d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 344796672 1250 344795422 344795443
    0x60f011a0901030f0e0a020f0a080c061e03090a030806100e0915031914070812030c040302100e010210021905180d030804170f0d090609170408070905091203091518 72
    0x601980005002c0712000017801c3c80070704000c441c816102c0c155061b010b01d503d100203884140481e00801484082d3f200000c29210440c0b0907203404016a99a006003c011080303c1c1c1e400c800070b808554242d226041c000c12444d044400b1407204101c0b5202c030320202c1d107000c1d4001900d00d6094000e01c08130040c0013003100300382103444030940500081403600f203e2668544503aa40042e4801000000c41d00804490085034010756020380300c071896840303001c1c01403d6807019440b464058061200102080c04092003240d0200008083e21100404003000840d450742050149140e9982d428640d0b5245944502d00451074510940e28540c1c41c2c6404d107030449a40000c0c10440a0724403041c4041c1303181c00444410354036003000f034a00c0003e01042c54242180645902070018000c60041404000d00e10801401442503e85030b60854a8299844041300c1c00c50303000310360040940e0020030b041308880d600d640c002e6400c0b0300c902044460200c0081e8451045503415542005d00e106590b420450b180411b0103200c814 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 344797922 1250 344796672 344796679
    0xf120204151d0a06051b0d050d0c0e01090b0a03060b0409020c0d030e0a02010c11040504050f0705180112140d0509010e030c0109151b0f0302060f011a0901030f0e0a020f 74
    0x700302c807840118014140501a03001070020208840d442200ba007210400201113450882e00c1c0300010b01d00290a42e07110340005070829003800c04240701c4501682100e00c0810040c0e5508210a2038040210140d0f0040c420401c101a01d418000801150b081c0c0a0006880e404400603501c4103103410b054984070401c000e01c01410300b80144146400c0c004222a14441d4080c00c18440d0b800e014a0320014030540701d4261940b1a203014280801d200303000442c089411800d400f1968a141c4900400c40007050322418071044120710001400b241c0395121428001c0d51248104844040741c2041c00b5040c52032030304003800060301c0031442208969000907000f003812015809015850b01c200002440c4c400d585c020403c04200c400b00c410001e0f4410b100440c2c0f058082256480c0020039854481400360000009a0043c0b19030000724017180e11070740105040701c1304040c946a0503900c03943c03161800d0b002030b44110b0600d6a58a0001c403c00d225000e001001210f11003d0562044244104101c400f00946150302 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 344799172 1250 344797922 344797967
    0x1080a05030405040903030e011509060b091e060903060c0c011b051e0d0908090f1c0f051f021e03060105040501050706060512100501090b010f0f12020415 68
    0xc100080115001d0720402e80d030111398120581004d6014001009180000d03601e043c0c21141140719014581080d910108002d11010740d4a10540380f0b14011500d1042d0311851000524401c1300c54540c902500c10030148c80c040c180058100000c0c1800802c442100240d400010079151100c000c0c0b080400a0400d081e0000030b010507814001e203507006244210b00143c2c102e0344200f4803200743c10144c074141c0d0b0800100b4403181c40d440c50851f405400080001e03000c0c0000e80d0701101246454040072000300703d40007420700c2c000c405480301300d94040b0a803020345043c02106202c00c01030041048180000c043c424000d0307030701d0521401508443c9200400c17510102d4041c000d100882c4c1c1c1c010300304c0e02118400d10780b2036200c1d182c5041c034000034030b03440d03102c10780c0100c00d200d030903903414008501c080c5403143c3c0340401c0180b682c0e500304903400d5a4900c51610b0000d242c100840003210300071a01100d5091040c90881400c4180080541c100d80c42a040403a0301740b5050204140c07660f01922180c0b1a0180d03040100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 344800422 1250 344799172 344799193
    0x1030b0f010303080f0612030f1e0306032a03100c0806040b060a030c030b030102030a0608070b09060702100201020c0d120605120604060203090f1005220b0f06030102070602130501080108 82
    0x180180c030040c140c03105025040f00882d51b280c2c0e88440c00100702442d641070301d0361a60b001851070307441da0041203c040c0007144a20340c030072104601c1080c1ca20988004c1c000c0c080103002e5080310ba401080074030144a100c102040c2400194a0800c0102c0c400210705030f00140a4030801e1002d00b0103100200490711071400c0c0514030450380c442e0070a68004050b207007000300c0e0545004005030050401084050381540c404410050064150307081304e021560100705603028262584400501071007003040307041d0091010800840141070801a49681c040e2a10005040c28141803029082c80f4601c102140011800a40c0c07a104d10410f118074002000102c400841d20510f0300213181d00e42c480108080c150590200000f1407009007406101090310028094851003114402003c00510090300c00012441d0340c0d11600c00d5542c40c9000c1011302e0398000b248d91a85640d0b0303516040c1d005c00020001e0350555000d11210000030001d001515141c42d0341d41c03003c11a5411700300014420801640030020300d500511644 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 344801672 1250 344800422 344800427
    0xf0a0b0a0306020d061e05010f080c091e03030318060601050c0a02090601020109080309010f1b0e100201110705100e01140412140301060201020306101e122301030b0f010303 76
    0x29011070340c0c40040940c84940031040d11000300315680c81101c000c042031100481e485614180d400640740240c8500305d560307101c2541240c10503401c0b00c407607070403141c1004425854580840d1030318980310810f010392511040d110100e4210340041da2000081040310061101d4007205009180d4000f100f17180c002d003020500380700380340e030381942100c064060a132041c007244007a4400e411483c000e03900507170f1071503590504074074260081c0102c0e00f8000300c40e464101c151304111044440242c50034035907622000300c00040f03810007803500c0514201400399981c40300c20f4030030b40f00c4500c0580f50080c006c0c2c0c041c02e820408a0001c00641d424511159096490843e840040c20640310245411941020b4008021190442c0603140b0b4810100d2103044c03c20044000130740c40d40c0c150011841031078207a65a04421010080581c1c90070b01d0114414102450424240346040c4a400110809140d001d0301007244501d68840c91003102d04a981c00032684001c50050040c0600300344040d0b0803403918050b0840561540c2c500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 344802922 1250 344801672 344801689
    0x30a140f1506030a02040e030405041103090c040606050a0305090705040e0c03060f0402010c0f0501021e030612160b0f0904020706020c19080301140607020307080f2b0302070206070605010303080f0a0b 88
    0xc0c8687e555080c9280c0381d413420801d89000c1c08016000304800301101c4503c24041d082225459050b200d42c1044290b182814000d140868030b954480a0505800da4820b4001d4a0001c1003601140f2401800042d15583c41c002d043c420b4052102030040c80244006040c10110300038130140305821000d040c0700050340d104e0080040c881d00040701c5540c100552900902a120b140004021103c0a0714408003ea080800071801071074200c60307038100300d4a81540c40d0707205d42c000c4000440e04081c0180c00c10800780080001c08001d0038000401e468217610720f0014080b40c01600040c0e860300d6001c110081d064408001c510b001d880c2c1d00e0030301c00c25041e81c1d5444040600c81401074000440602006a09039140c10054500240d401415a9402500d680706196030310142c0b04d03021345d58454217035190281c04542d0f0b05c8020f1000c1e0780c100e00b400c4a440080507400303980010412a0032200030080b68011070301074400c40340a1807290740c03a0100740c20204141a045040506080ba629140c01c0f0024115a500803d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 344804172 1250 344802922 344802943
    0xa0906060c0b041e0b18011104051c0b0103240905281b030b0903031501180b0d0525020618070e040b06030618030702010c03090801090305070b0702010b090c09030a140f150603 77
    0x41d0300302d451080c41901940e100d03031601e0041002c03180cd40084100442000d8131130300025201c41c1c85246d0f100c19038460044c0c80901074082c0c10b5420028000915588210300c03078014503040d02c41c11440c09620354904c81c4006001e45040d404046220044c400c10100c1d504e016005036502c4025815800c1540761903141420700403186060101e204121800c1c407140c070b00140001c2110501154032005411502000f0b402c00b280d04003440c100380f810400c003460f80000ca10071560340300d070b0003010f40e940d5610700c1d001040c41e01c075400c10107071082c0d000004103000004000ca220300e2040c0f000607840c6c00d140050500d00756018003803550009018405902c8401e00006581c00c3da5024600243d04841c281000d4903400c1894001014550802007103c044c1070b046002031000328443c401102056075000001c03400c03551801d58503030f03100000d90702040804803500050264600300505561090480795611200c8400320300021f40d082d004150302c24060705040c04055050004224030b41d000345409030010303480784c03a02e52 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 344805422 1250 344804172 344804179
    0x1b030d050304050c040f0f151d0603010f0c020d0e030c0d260a030e12040b0a0c050c091501021504080a0f14030c0304020a0906060c0b041e0b1801110405 67
    0xc1c051100400c400b801185005d4030800805000c000c1d081d0140c000c9900441032581850b03029a80090750a81b21005c0b078841c0401c2c298007405001021898010190000b903040d901ca410030b11940c0c59600c40c107442d8150f0b80d0001c2c4607104103440090303c5100039203002842a0489a100481a2102d04100e00307110380c030040d1000c403c24540002c0381c40140902240031381c020701180c1520455010703840015500c0c2100119514032482d40d13030254042c401d5000d080c1d824001803007546400c0f030140849562461044055600070a1802c0220724500011280c014240030040700050080d41c040c403141ea0f518005180080d42443c250b102e9030902e03c0b42c4204d400c104a20403030740122503440740300c2b19030b006042404200c0d5681417059401c1c0098101755010fa204420010000881c20150300c01c203001c907803070364840064000d1591511025490010003d5910300c1d1203d068074500c2600200b0049403520841480c400ca041018032001c00542452801442d44e2600d581003510000400580e421030300f00303d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 344806672 1250 344805422 344805427
    0x180e011202030309210d020606450a0e0606060901050a091a0d0b0103020702030d0806011b080405040501080f060a020306040b030105040b0702190c0e06120d030b1c0b07030b0a0f06050c1b030d05 85
    0xc51b5034500502c0142b002518003079000e0750301c2007a20100c140e15005184114082c480d0394020b910340b5442d05d03000e8410aa0000c07040100388100d50045000e420110040d090488800e42c5e1003150308891040c2003030100b607100c0d002800d070201c01e03024030500f80f5103a005c1ca011800c00360642e0120740d58148146100d801d000c40600041d0041c0c3c8652a4400354206510b0b4650031050300b031034a903040740c00c14080c7c241304904043c004a81600c002901d0082c0c9500a0000c150603224811100c00950000e0302c03c40d000340d200c180700841920240100d6002e144540000107a41c41c00345002800c000443c107812003502c0319100386030003042c400e8400405a81c0075010800c0161282c100141d01d008000c038019a181c090306d84080360094060380121082882660064482c090120041d005110725040040c0114101008038501901c240d004400c0320001424814030035440b56800e030132036041648000000380000818140c0c4900a00035200c9881210f082000c1c40000c04001a03100e1000c104080101700c800f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 344807922 1250 344806672 344806729
    0x5070f021e04090c03060e030304030906110307061802040b011d040f0b030105130b0c12010902090301111303031412061309061b180e011202030309210d020606 70
    0xc0d01c0318080c104020030070400c0d11070f5850b01c020290081e00c000c0e1003892400000100000010080b03e102d1640340d0b680c07414260500074141d41400040c20860780d036120601c180390003c0e089105019443c41d413600162405000c1d841004107444a4140d030702d04000344007a0703010f80c08820f0152852868030880d40401d220819520940040600039001d0f5070541c01c203401d2084036030a509080d08254003c88a551142d55100a1004a449140c40605021002d440100112030681d40981202400100041502500340ea0700424541101030b004800902000b010410150040000880384038115025402d14002c14a25092810020301140c081d09a01003081408503055102d085519032040d001c0141840550740d14942c23261698a1401095010007a03452038904444041c04581031658661120381c20450003040d03070114010120780521052010301c3e030540c4d50121059102480000150880ba05442c0c1c2600e0040c4032143c0f441550450002c0c0310468031405c5c0140030058031410b905111522 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 344809172 1250 344807922 344807959
    0x1d0a060221160803010e1620150103030e190302060910050708032404051b0904090b25080c03040f0c030f05010e0d02010b0a290318060705070f02 64
    0x242c0d204442c2c0c400ca14402e0504211070740c40034606032203d008a465669880360740154070701d100100300a000c25130029000481e07450030300c940e103164a20841134500094401c10f10825410081e007046000c281003035116100d41c141284d03030142d0310180e01019011145182c0100d1003c2c400da2090034001c2200003030360b064040c011412140c0b402e51001c1080c0d56481d0050302d80c002001980710301c402500a000b0020703202d24060085e6806161408040440da280c088140240d5900c40c80320142c001ea140c01c3d8000224051002c441d1103050242403030402d295080303024058103014002c40c6400d00c08200103002d0511841d0054a501035800000c400500c1018184613000b059940e100070001c06052000c002004010b4000080180d420300072507190540c0c5102c00c0e030985a410040c40e80159800004000d85a8444003020440b44554952094400482020140e41e44121903110101c20910f420010a1008000c5550302c41e4852401e28100400e5503103a4210001040010380305110a0401a60403030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 344810422 1250 344809172 344809177
    0xf110109080708010b0102070501030b09070c1e030207030203071e06030917030103120e030106082a0a06020607020f030a0903080702040b040218090a091101051e04061d0a060221 78
    0x2510608464180da80c41903c107010b0309030150b0190040c011540d0000c0c081d4003902850f40110f000a2241d01c1aa40b00f1030111b0710b404c0082c6045e1060600301000c000107260426841e211503019030b020300440d90440c010706140c10003d0b4071824082c0c108444016040c10610b4800781910454070b400700e840301c0903003401c04a05c0d684468041030341000000000800980c05594105a0400d451380000c1012820816080b10940d1007140c0d003940112000c82900751001c0d03c080c0309039003401110b003088040c10000c60140c0c070480c2c00c1000980e0010050040141e010407a90040c410741c40c0040d4a400700382c55004101200030b101c000c00d6006e002c1061400c65540d500b10b000011000f4004640740d4552034084070038480c16120940c09035105101003055940706000309004260021403822041808800450750382c2c0c004040b004520450b002100024415000103100a00390b82d51403982003e098040c000c00004920840351141c01c440100f0010b507900811200c40c111075456400f05d42d0700701c0e8500c180c00c41c0f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 344811672 1250 344810422 344810429
    0x51c02100e030115050306060f130504031110060807050607051c05030703060605030606070f0c080f03030a0b0d0213020a110303011805010f03080304060c0504080d030605040b0d0f110109 82
    0x110603016490301a5840030000081c001c088009002824180f44000c0c0c3c40031103805500c1e01500440c00084250800c03000d02101c1c00320240c195a086100c0720101d10468000307039421030000c0c030340e1107a1442c921001c100545844081e04001c0001c149050007031030392504240725040c014000030910750107120040c80543d00100400e0100c0808000104000b400c991007180c00a010030701c0c06401248040c8200b00f989d10861002e0182e03807414860ba1140790080c07040c220300b240d20301140440803030000c9003400b220301010123880085441e810201d050006030762038102401d003d940c1c080b80c1b41001d6601d0300d88030084900e60a800503030b1514280011030300a6103410306d00d900c07440000000180c4010010800245802c00101088540d888200c80a402d188611000d000101c080c804680860840e5028594420850070003d04d0959510103250070701d14400010300100790b17100801c010504240c080c98032140011100080002c5c4c8035903540365001c007010000b9000401c0c800f14490280d01400c078100c081c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 344812922 1250 344811672 344811679
    0x2903040f0f08210a09080f0328050a0f0b03060f06030c1002070504060605040b0a0509190b030907090c050f0c0a020607210c0c03080309011e0204090608120301051c02 73
    0x2219002041d41a4100c007035001045003c003000c1c001010b0022502c90381c03c070f442e489480c0501e00038003c1c2610089070405071854550400600403101070a891400c42a61000c07074480110340d42c5441520030084400d030540d1202107501705482120303c0e90b008154298000221103032007070b141d264840440d02d000075000c150b81c0c22110000030001d02540009a9004491088070103010035903d40c00e0488580c001c501c1152041c070014001a901103009030060f01c14440054080b56106035001b032041e044207030176440344401d07070400000c1c05045001030004d0000741481803818003c20794a442c004001b4450348140c101c1c0001c020818050011081c06800c40181e0000c1ca40ba0301c07405603003447c0030400c01450070914945285000302000c20700450b0548541608044441e22141c035645561485520041600b02c065580b680b0811500c22034030391092095402d50380058640f41022440c004031026904012010742c01044403400301c00d69030342120b06582055900e69040d40b40c2118040d00f80c1440d5000950 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 344814172 1250 344812922 344812927
    0xf250605090f190b0402060c15100611011401170102190e0109140105090402030712050106030e0f030306060438092e08060d0c0f2903040f0f08 63
    0x25503600000e40c181101e5031003410f8030041041c51580c0180401d0068000740960800d000007400340ca445c1010302a001c08500a0b9205494100304640130348004603160b42d03070f4604c106002d215645e40031114021220340711000300540010b95a001d200310740c0510a02808a05401c0d0f2111008000c0d01910310715814a2940d16404201450180020500490b500c0c00552240c00014000d28510742c00c0c1529001078507030518160096003131002a600003000c103001e00180c0603012441441a108090003400d0300e560000d801481410980d0404c101141c02c4540c5500603c01d0001660b20342044130708460f001c0250f0088029040f00000d580c801048070850002001e1a0101e01056004000d090616088a08110011591192520203108008105c0b00040700b032070001c0c5058011603006421150042403030444400342d54569003126a290000481780d180c0403001c00000040c103003081c10030041403003004c04501810018103200c3c0002017015150001d0306012409100d248032035a85200d03086020300740d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 344815422 1250 344814172 344814181
    0x6100e0f060909121804110301030818041d0a0210021609150f0611150103120305100819110d12030207082106010806040b010203042327010603020f250605 68
    0xe1044a417046a0f40a0342c00d05092070101000a41186d040e01d500003100381c2407004401c5501c9649061582050b002603590304100070051108241c20340c25004d100c02801c250303c0a10522540b402e0000d20b010656000031000000800d03442204010344000060000300351801300901c03850b040095100d0b010000515070040740e183e074054103e6020111340301c02c403500c994403000103d80d50f0783c0274403000e8030b449e0285da254040b151081d00040d82114000850114007034542410340d08042c2568013010011210003450b8040003c59168909500b01c2140d0b10a2540c0540d121400e5048480d1401c1080550028202c02080829001e540c04c0e030100c0c0359002d5071b0303075156452506d04031b84c00d90b0054086070328203002420507c1e180c081d4100001c010f0b40039500707240c5040c0344601e924000709a0303071903a0340881c1c58401e1030741c840d69400b05012201c4042040360724003002d02c11400b014103030002000c25004000c9401c1c2916000d08a03210241549000501c140d004008a0314200240100414407403e10044c017 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 344816672 1250 344815422 344815447
    0x706050f0403110703150f09021f020715020c09042109030b10141903140a02240f03060103020c0a06020a020d1d0d050f03040806100e0f06090912 64
    0xc0384514443d0321a16030b54519800c500d075840031540703c024180304048514021130440c2d9000180b60300d102e080d0106031080b00750b00158013440c4d03940080e006940069045409181d041200000605410007440441c901c0b402009403034518010b0124011103841007c02e08102a28040789081c406c2c0d06009440c2c00702c0070310010101c0300c2a20081c0c800e01c8213203000c10000d00070001a801281d9000c040c0cac40204410300d0500074060400400801841540500000456003841c480081d189528001e80680c210520411910603d050921600c1c201030070341071102066000c0c200e0382c80c1c24400e84030686a9035100012006445403072203184c0c10340160010041003203c0c030340241c421101c054003035940564100e07000f02d0b4020b50005545100e64040e002d007445d9800d00020000513980140242c0b02c0c0002200c00c0c2c54510361060f0b02032491031703020350100002d03d40c4003241000602090700c00100345c4d042540c4601e148620103854580b0540c8a10041900da0100304034014800300c0d4a1882da44455030403506 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 344817922 1250 344816672 344816701
    0x4060e12120310060302270a1a032d040f02120d0908060108240c04051f030501050f030607031d0a0620040506120406060b07050606010e0a08070b030408070605 70
    0x5900c40b12190f03181c04074120340a402038a5001c07100003c1b41840128503e00c54200190b140d0300365401400001000c56514801910030050b070740c0040540b6920f003858040c01e21903621440300d8074100b0410003039580d00d2410b003a00e000c5c2c11a17005041d890b079400044c0000360380309240c00c04014240c400c41860204040d08001d04070115451002074400583c0e94081e031549419050030358043c0d1000280030044556048125503401a0721b000e038003420140c0714804605027035040c0703540000741c1c0c40d615911500309038140141800740009561003850030100b200401e540b00b001900c10818951102000e80c0002c00005140442c02d864908580f181909403c00b0030003003121180255020249a8017401100e100208450071594003410721883c04440c00019014200301800446419494a1002a4130404134001d070203000d010300d02811181c201480050075100081042c28011412220200f01c2c0d2030001c2084021250340e14200d95683c1d440345454855881840001050700d0b141c1030500100103800d011 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 344819172 1250 344817922 344817931
    0x15020609010b091302040e1603081b0312040b070c080d02092701152105330618030a0b010e09060c090d03030b0405042a030804060e121203 61
    0xc000c40a0b1450034040703188811201e803506080d0b0b07000c40e0740050510381d000d4040541000300f0f40d40303001d40340326200304020300743c2e44181c880000119040088441100d000391080000e4001503207007a8600c074042028010061000d0b0442e00980000b0341f9450180c010b0110040d0320542a079918454808820001e422003040302d4000d01c802c1d00322910411000c00440c044038030040f40184240c0c40e00324203042000c800424a42006030450201114501d0300081c19141c8a1116000c07525207840d85041155410a039000c0740c400401400402d0746000c0042240000001075400a030303a015000d05c1c8001868108010750303010701c141c4100314184061610020305072105c17010725120640714602c6c070550741c22060f038000048603000c01000b2894034120811000039440b03400d010605c4422000098211481101c040d14070160407003803449109851031020610305015020940c180c6c3c11602d8950b0640210b0241e141880a02c000080c41c13681c0d40070300f28519070b1151080b20541c4c1c0715600c0b03400e45508180c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 344820422 1250 344819172 344819191
    0x303030203011e140913050303100e0c0a1d01030b130507031b0f03270c090b0604060c06020310120309060e0105041202190812040311090403020a080310150206 70
    0x3188105100c1041c0003c8044402c104030982400300a0000c001882001500300f02446014501180c0028420300245110b01145541c91940c3ca14210040314140f10052072500c200004121014150b03402010ba2492000700782c0254840236040707401038000349120141280e100c801c1d860805625480c3c0d4104a100300040ea50900c0190b0301c19078032020110181c041500418211112201c030540300780d0122010b03000500403504a11118500c04d140b41d030303130003a0544030300c20f000c00203001e0003905020704030380580180c680516080c9800c00c01862001c0450008107921380000c08525404201c10007013003d40b01c1c026040c02800350514010f80607800070301c50f107030220380328580c118200c2d80200700340da00700d8480c42d0b19a4100c110b243e080244d0300303110030003c1420519003000824800c43c00c002c8125548203122016581c0d41c2542800b1485100000050f0b1050401508000010b03334081240000e182c3d00500d143d80342d44032041250748281d00e50b0000021440d94201e1564029030015005009000c1d20 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 344821672 1250 344820422 344820449
    0x103231819110405060a030f02010c02090f0412020d21200408010b0a0b031302010309120905150a05040e0c04030b040309030605130804051c0b161805010e040f0b0a030303020301 78
    0x480610040d1007003202d00c0c5e54003c1c0c20f10402c00210320f004040c401c12520501d0001180401a8000b42404409a82e99002100e2800c100300400c801e0304020039211646000600b05d090035007500600840d10102020b000f0031808403c03cac080006904402010040d400005454009407035001c0c2c2d080d0068410491650300b0541000014100382a4000a5030f0085107081e1940d6038a0008021219480c10101d04069554600c4400315819903054000c0e17621070342d0380b48291032401c410006940c0c58880c0314903102c08100a80e200d0160407800705c0d002ca5401000c10b00c000c1e5a0b4a48807980c5004d281d0029082c1c0305d02d002003004141e0b00801100a0301e100d20810841500c0e60102044c000b4070f4000c0040150f20300f0801441580345c40d100500400c103451841d000c00c1074455030303814890941a100105106800204075000c0340d008004600713003121034292086503a14200000304060301c60100075005945c0c07840c000c501f10003550010030171034601900e0402855030b245002030095009105038410000710 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 344822922 1250 344821672 344821703
    0x7180e1501061202030723040503071a07031b14070504050a1802130f02040b07020301051e01051909020a08090d0c0528020a080307110103231819 64
    0x904800c40c16101c40780e540460038410450040001d601c05081039040c48001c400c405000c2440e1611200050441302465803550b142c00103261801c03500340c000740002c009100301603956110791426286c0703654040c501500c5401440c104d01c50860310082c07024000340e4454440812004000034401c0484034241ea08100b2079944404000450b0020003502c4600004442c501016241480c0c2d21000c0d200d00e141c0000c0c07080035940002080f40d11691210411400115100d020b40c60280b040543c00301012370480c00400d8032150454007188140a810300c151807402c2040c0c11021401c2a003005005120030071035459846080140541d03504550f0301c1020b2040c0d40c4096080791295050504880e0b100f00180030310b51303458086524811610304116800d04022010b000907a0762558248000e21001015590742c40b500d04010701000c101800c000c2c18541008007031807803120743d0283c5c0c014120080c04000c400f81c0f13902da9548081171030b8800180083c881d112614149420000d50400c0c201d1040700e011000415 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 344824172 1250 344822922 344822953
    0x3705120c0c092701020405040906050406050708100608040f02060a02010e0705030d090608061504030321021c020c10110c0105150f011b080a170615180307180e 70
    0x1c030381c2c1c0400b109141800c0701203d8003070b80c45041c2240010700051b00785034076200401d086a05495040d100b4544440c241320500045204294201c0765900d400740d01494000c4a48890607928402c640c10080b03800001014012400d07030076951254020181e5a40e2008850000d0182c406420180c16a0041404c00181880c0009030440c0992240d1a4420390314900901903c03815030050296030448282c004040144034040c0007807001d54420b0b16280b9401da40b0080c0e01d62460140010084a64410002151070228040c041d40d192038070f1441c050381e58225030031110f0824042c2e0600c00d074580d08120308000d500d0b070400081d11010f41400020411551084050708685451142154202142c820394003050f501c0b50154400c494005086954184204d41c0c0345d01c0c642e4801c19400000400e0340c40d440d04082c03402d05400350003580c210b0344210305484c080b036850540c0c032079100001442c00c1104100c400b2030320180030142c0101144007000e4501c810300c000c0700300500030718031900c030303140c052110520314041 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 344825422 1250 344824172 344824189
    0x40b0f0603151305030403021f1e050412060b0901260a0c031202030c030d0c030c0e131508011d010b0307080d0c03030605121e3705120c0c 61
    0x40401186a249440c0c8a07907001d030315000f001054485020070031000c030260b110914a140c0800f1014015603035480340900040142d20071803121019200c0040c450180740303900605980903180913000f5820a100a840c00c6001401009503c0e90805c4c1200000908000794840944094802000d000d5210180f0f8403956210b03e003010000341051105074041c00400c1104100a0080d40e40b401103070b1400500c0a21070b85982c006002902c20759894041048401c1d5050180c40b040321918208600041910000940342881c08069908400d40e16282401c034541403008490003011900002c000c1d2120001d5245800b4400d0302c611001036003000b034034000c281400958041141c0070070001d4901d4000c0c0c0101294110503140040c0d08064440f040826141d440b8510082c0e0690510002c1614a4200564402c21015142c0d501c0e1540c04c44850740308091010b107901c0000b0321212800e10341e00e1500103210740101d04054005010303031058800f010034010440c8010000c0a072410202c804520148040101c0e40c07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 344826672 1250 344825422 344825443
    0x40209060301090225050c0a09110d090302100905010b040b0f0105030408070c2d06030b0109060c0510020f030901050105060906090415210c05040603030906080a090b040b0f0603 78
    0x40d400c00042007001195070103058415040d0b02d01c42603400d00c030421610a15500300c429a5640c00005078070040e85884862400140814a03042c046829852402d13071450141403006c010898580e16001c0c10103100340410380e90810031081c108090714542c00c2c503078003d14011282c02e00480c90400d8104d52442d00881030703044014169034591456983d9982d001203500403601c1142c42c00481c0102080d076451405090100198a51454600b08000c10490034445859440902410b1a150000c0c185903071141402c001c1da1000d061071500344103d4274000741390042d5030b401c2c04003052000c40c1c207800040c02c0300010b60141f040d4400a005507603e8008000891161120b000d51041d0208000708490402c0d4000040d20391000c0c542491969440c006075031944103050040d542a51540c0c1c0c000c041040341e05151000d040165010099181955400b400482442c0113801c14404032034001900c044981c0c03c010300d640d078404501030b000d081c145071812202d030050711381c1e08205c020315000075042c6c200010a911003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 344827922 1250 344826672 344826679
    0xe0c030606060d09050109141b0a0b09270405070807181d2509150504020c03160807030f0c0c2312030a0305070908060114061908010e06040209 63
    0x40d01c0d01010001c40d684072989520040c0c0c0c0714503030040800d00a1080c500c1c52030050008148600200a415050541e628404d0342c1a15104d0803000c583d0310b4100c01801511a01c03020301e036a0344d40300c5001800701c03400456840c051140d51603040c9101d0a00c0c945440c0114031602c1112142030f202c001c0703661100c00c28040c003500316410b41c0c00403d0644068011800a2010450540c1c00c10280344071103080c51004201d10301e280201c512845000c920901d120030080008610030400c051090991030507050107441090710507034010a59401c1000c060080b0b40c40d51010600c1160721100500d400f9001b600000c0c021f50100c1c0701c0c00101c101c028000c44130344500d41c6d44481c061810364149a91048142c0709828035002c0040301c8441c407034542d00da501e1182000c101900c0210744139000d14500405680008218034208448040c0401c02c4040c0002d0f91030640394600e80d00c0d818200d052021440303030300800100440c1640305d441881121900144d5043c140c94000140220f29612141444103074420040a10340 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 344829172 1250 344827922 344827933
    0x6050315010312030906240f050d080f03040302070e040b0a0c14030a09150f0603060b041103040f05121605010b0301020f040e0a0f0504140607031e0b01020703050d020d030e0c03 78
    0xc0d02e11942c000c84109100d944d0000303400301ca00d0080400d00610643d03207d41c04201c01014030800e80b465030707003500600c4211a03464640d40c0350703039585010b40030f042c124018014020009c00d040500038030410b00503201090883c115850181403a040703810055800035403451424141144241c4988000c0842060b40001c030742c42d54640741c41000c02040c0d608400d56240c411070849603c0d00c81c0d94001d1440f0300d00310b980041100740c00c0d800c095045a0f078209807584031780d00e4480c00c2090b181d032042c10759030301a400c20b0720586000a036042160400d12003110110030403400062144040305010105a107881c002e074003c002c0c100c8102d0030b040c02c0703115443c104200d806092108010300701859950a9004000b140040741c06001c0701780f010103036001030743c3c00c4441c00405e084480c0b8130041044407603030000c2c03a8901032010580c601d41c000741c0350840884001c1629121040024203034000c000d0300000f594400e00300c07a017182011400035103c220902d4540d000908150300d040220b503001813040801c180c0240900b5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 344830422 1250 344829172 344829203
    0x7120204210515090c03071d0c0f04090204121203050702060c2d1e0a08010e060303071502090a080601030b1f031203020306010f210203130510060503150103 69
    0x282010039201c03007294144107224010000601a8a40c00e0044080030020400064400304040c00d20407103800082490102070182c8400b000c9180ba1186c10490b03c0e050b159131104030b46a01c0d1400e00c100d401001c0b455000040010f1600c4245c01c540c00168014462851144040d603001c0703042d01c0055032003000681c81400803d00d5003190b50001c0124030b98000708200d60343c000c0181d0801b00d044800c20080c2ca20350208003220400f80411880e614a640d81d0001440d0091200010b0850041801098030305068400060070350389040046488054001480180d0245861100c102a6200854180c021300c004c1100059200d1700040d030780c2c140c0e0b60010029181d035803030502c1001c03425080f0804207403665203000c0c000003060404440c41503042160764003590701d180c460001751080388201003600400c03001d05000320041007114211a900b0040c0b01c8056542d407244649104440741c200005801c6000d0300c1060780413019141d0000007250400c1d000e807050840541307030011141c0824400504096040030500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 344831672 1250 344830422 344830469
    0xc0c170d0503090c031c030e0616030209180a0506100f0c29130b1003030e040506040213090f24060c0c1a121b07032a050607120204 58
    0x82d50b10000b000200d40e4010310810000345040706102d400403903031090706081500300e54540188400c03114080300a21560030415031500310002041d80c2102015400304410603540e80b02c1c1c032003010b9401a03146518160808109901c001c10042d0354442c0b00341011a40c8a0000b4010054078120201e680c42d0b100380c0414941318150300c40c00c002009900c0c40d0445141ca02c00d101fa07001c445000d020111280b04184456140000081c04007404803815a200d0701d004000103035100300140200181590040307465100c40700400d001e8080c842d0103400039200240c01251250a542c000d030300c50b010024040c030801000c00e40740c1c103080c80001001c0318103c5c1c0d100c1080c404c943c0030340e05040006115102d1001540c0e40d44102c9130b00c005140030300e16a600300026803c00c2081c11013076107030b40004810614825509000b0b02d401c0c07461280720001030500c0811405621404071400c2000300c51043c0b0304651003408000d20708161520822141c080200b850074410300c55070b106910945080c0d421009502e8185d10142108 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 344832922 1250 344831672 344831677
    0xd0c0e1e0c041e0b07080315043305060301080c0102010605091b030403020a0f0c05010e010f021c050c030409051b0702030a06270c050f010314150102030403060c0c0c170d05 76
    0x1000304400c08800003c4c26035000300241070240c018900540c5070f00303240001801480c0340d560590312442c2040300040100600c05c07034a01600841032460042d6040800a05022072003075803040303a004c030001c000010052000300d41111a150700760b008010041d141c1c0100702c41c103c020356040c403006900ca01055000030094000715005400303801111400f0115659001004000000844640000802c208510350f04140c12540f400401d0800d488103c801d010000c0d6952407403d24000031207001c20070114164014001c46032542591720a50b640c0d42c1c0c45400c840d0140c2004d030380c0b0301483d1090b8050386281e010300d03109503010aa802406042a5400741d12070b000648110000000f200002641c1d4041059081046690740c07482460002c00300b600c1c0c1410010102007903042c0034189402c210b440701250b0815082c459100c0789100e481c080746111100100e2a40c040c0da04014503161801210154958103c916004198030800ca0300c003610380c0320003c0c5203440c48031100440c100e9002402002005015a01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 344834172 1250 344832922 344832959
    0x30906090118030f02040c0507020d030305100e0103060501080609031309020322060e070501030b092a0d0506030610080a060b130c030b04050c090a0e060d0c0e1e0c04 73
    0x100b440318410007101c01c107001c080a42c011200300e800b000d81d040460400c0d014640741040389052890901d406500450074030036032080d008041503507902c0010310450340d181c015005844c1d9546091107541c2c4904e02070006150038000c2340da00f1320070900010001d0200108681210095078171b080d07081c3c1e2a000c10b5902a4102411004600713003c84c0c01c1c49040000c1c140849191402404086800321031189002c0c1003280c1d07034019a0405081540c00c49058a58091a42e000a0b0030302c00b05400175248894000405e05d030a4565250b144001030044c0b488030b90341c10150143c00e04509442c1c00761250f10810740d039403d080c4504202d0b42c00100030b41001ca409035204038601000945046200704030300c3c00c08002c564145e5076403004a699195a804642030502c0740c039502034500544546007101c180d0018240031040c0c0300e000c042100050000b40f15450302401c0159440e4040c961005c01a103654040583e0302c0708441480014102040382c0da06855050080c40c050f4018220325841d003824002c0030900343e905060b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 344835422 1250 344834172 344834177
    0x304180b060a0e01090b0f04030807021c05070e130c0e0a09020303190e0f0a030b0c0c010903030e19031b021c0308010e1b0301050d03030e01090b0105030f06090309060901 75
    0x400d040c1d88421004222990b01650f9984459540703c001410300c5801c2c0d0040080c1110034824204070000c80c101301c800343c0360010f6109446002074400601c045455414000d0451071401c201020400001480c0c0140e41c0b840385581c45943d1542111180c508040e0000b500c40910000308100d4803000c0740c0969080080110041006109c0fa00481e1443d0f00126500043ca004c0c001c2090100c2c0e8404682c00c00b13240100c1d141d00120a41000103042d003d0741e0300018000c940d004002c00d0081810302e044950f00812480240400f11483c1005001014030880303200d00c03030046c15000030551340390b4040e01c220303a03030305480740d05034051510135100c404ca035800e100303d8000859507000000f045099032203603000f61095642c4001c543c100f100007403548001415208940036030382c4503504400c0c142c00c20703681074900a032000c1c01e908105007000c6015100140a6503400e5103800051024440c0c030100960503144190103c035011011300ca007103540c5040445800c41e203034201348202ca11030701e0008014200900140b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 344836672 1250 344835422 344835431
    0xa120c02030c030d0513052e230703170915150303120a0e0d0c03140d0f050402090705070506151f110c01090503061f090e03072003030418 61
    0x2c2020900c1e00703070002c0041000c1031010810395011110f00c0480006000180e441514818a084140913140c414020000d550001c100565132000c0c410034003035256100350041450030581a00c003041456014900c140c0016060311b210700b03094000c00054030b000c4d8090702c008042046c402c0d091080100e1001e05186160b03501148a4207950760108003805440b280040340151a040c41984001190841c040082c1290407140c10200d14580250004200b136401d810300c000440c0101c072108142e0b10440b5011445913240030002580d60361309038400c5115a10a6517150340341e4990310803d481b5400b410350001c1259001e000003988100142c04150540c42002d0510010a00040c0d540ca4084103d4851400003c6030103c81d002d20400c10008405010402c1c200303610f16904003004643c907158000c0a010a9580003a004401041440c200c5002000882401c20600c4515030103241c4a130b00c050403d403a00c41c0c0e042036113210100469841c10301c15034014021031505140031039900031b00e43c0031411110529600c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 344837922 1250 344836672 344836693
    0xc04051c0503040518010806090d0807032a080702120f09041a09040b0f0a02070305030a0e0f190b0a050f012c01030b04150b06041a0f1b0601080a120c0203 68
    0x707014009045c1240101c010086605000e54249000ca000f008a4015070146e0309030342100740c2249805420040134503020401c0240e10510b81200c000b204242c2c544c01465907964103400d13500041842c0031b1b2416a00359101c46805040c2101640900c210404d0400b2080180556503c0c00e50301c400100f042c907868180c8402000030009442c10400c443c1591480704160400c9084440c1c210304aa102464040450400e10076450042c00703070100a04800010b661000c6c5050030076010440313680da01e414041250551210400c006210f40741c80d590450711101900701140f03948015008642c895620300031480c2c0d440c2c0c03a18501021100303c5032004400500c00c002c151a4041d490003074039002e1401040c80c5040b44c20545450044100c0001000e210180b4107100b0703a03042e58580d01124100c4807080d40707481c1006441c0007a503410748203c41b40c0440f120030008926a407030754940b01161b5a02c0255080c1e442c04da0303a8882c001d485103160707480103140150300548100c40501500d00701c3c1d01540098110b4200008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 344839172 1250 344837922 344837929
    0x10f021b01030f150f060305090a0f030c0219050a05040216060203130f03090e1501021c0924110a030912080c0f0a060506030d08131a011206050c04051c05030405 71
    0xc42944800c1e042840e110248002d017030840911000b061139103002c100c1c40c80c0c1404925242c7c45030344c0e00100700692030107108062520a810340311240381c00411000000c8131032000031390030b84521300c034807802001e584000091a00d4a0320a0721030401d82403002d10203806656440d00001d62009000340240c000c03044d60403000c58100b418035040d1038070036110b042c145410220a698000c40c02030103082070f8512601103440301d0364003141c1c48201c0c2c02c4039107001140900c42e0405540003842078014610402c1e0000700b4402030940c1c45160780c480c008a4581d480c2c0900d10410480c0c54004840004d0081740701264200b048810120030100320318015500c0c541000c00d4541c4c0e50703092002c920407048441d40300128400074031243d80304036030704250200c00510302510002030142c080f80008001407074900c0004204014042040c0c0c403459440c4803803915400319a101c44402d02041d0b074040003035403160325020005910241ca84101c600f0358000405106209500700c25107504542c3d28039003125180018440000c0325107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 344840422 1250 344839172 344839181
    0x60a03081b071d09070e090a030804030e0607051b0d1a0a021303050109151e09150c09031406070806060912030301180f1404020d030e03030a0f030b010f021b01030f 72
    0xf0f40014401168100011410b1070700300940c10012100d0959810712459000000d03c18074a00d50500f416010317a0749905090b141c03c00140300035600f014001905100b0844089080c40842500c415002c1336a000c0e0350034000b1610059000801d00380c200443c034100d070f0121819072036002007141e101510341018100d19a510000b903070300441d180da440b6050b440400c40e00b01c1c50404610f4900b8400c02c030303080b01500400601000c000180035110b64450388078060203840401c045910001000900c02c0c1c8008400040902d14140f000380c60000100c0e03401c40d402e101c0410802d008008543d24403c40e6243d5804024a551100c01c103258041e03104100400c100e2000d101860080081d0000e80300c007403c209608209840b01405e403410b40c03503d0411081c4818181c0c2041075001a010384031031101c0e0304c007490151440d504580303006901d84000305107140c4480d8030000040300507030a40d038244a9240040015182803514051a5015811038015048810302c01080142100c0051502250805c013030010320049a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 344841672 1250 344840422 344840459
    0x51f051c060f020c190209061c0812070206090a0b040809130f020c0d080f010603051902030a1a011815182c0f0609060609121005060a03081b07 63
    0x1181c020440302d4644074280210320039100d400030721840304100b943c0017031f044007401003c4903c01c200c5100024080011118000c00c1158014030196442d5540c180c4010b00e030b50102e4903840184203160005011500214031f502c4100ea00070b120f00c4042d2900d41d2034070303015000301c2d201a401c103941c001511320a05460141c0036000e40c500700d0060b515000049440d00f444030801070324090100040034004000e541c0382c40c4c40d046501e545400109601e40114000c1009960a1100b0f5a14008420b014010055604c00c8041ca901e00408216001542005660400508500281d640480300c8200078400d003004608108449038500782188904840000e40c0441d12500706401c89109003295100c0c0c41c210342035035004a814880241860300d030951082c50b882d00000c000350302501000c400701d26551160340582c0d00d01c0e54001c1540065011012035580c0e101c02c47d5507148541418100422081e0a141f0030b03203800d59400c580068500340d000e000f0030035042c3c810300010f2843d200c0e150f80002d601c00701d6520031014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 344842922 1250 344841672 344841701
    0x706110a030c0e18060d020d080f120f0105031506030c0a260f0703060207021c060f0615050f34030206070203040b04051023040504051f051c06 63
    0x411a100000508201d82600720b40e004003080c40c2d41e241500e003480084d44e1704c90320440d0003d02c40c0b06903101195840100880003050491b012803010345418048002d4207a40c9028080803906030f49288509a80003800e100c5c054264000309801c000595041c1c18032640039002404840d4048a807a0110380e520301d195100301403410f088200c400800b41c2007166102c004000000514a030081d41c6070940c2c0380e645500c03008001c260b0018103403046454410f01008004050346503004102e000707040034406800060205140307035140c2140400d5000c0c0f0019101d2000c0400c1d5602410034660004178182d5521400100d00d4802d07c00c0c10705048a10a01c00c021501c944105140700c1c481d900c1e14000e0303c1c0031000741c940c8055401c02d10003403180c03090480546045a804031448056040b80940594103180210510f10a0882d281d98034034503015030000400407500e043d2001c0149544100d03410070085411b00108001c009140400c001c5031804540c40000d00e80c103c6403400010103a5920a0110351100c0d43c41c100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 344844172 1250 344842922 344842931
    0x1306050a0f031b031101051c06180e01050405030405010e030109060c0c2112020d1b0302041503050c03161b0507060806010e010c060c020102250c290706110a03 70
    0xc10850908008101075603200341d54100382545d403552440c00c0c00280c0b150400c04045035007080500000041c54034041020000c000c6070740c0343c6400201c2c202c0d4240034004420309180c4c04d211004014410300c0d205503004000307182424140401120003442c0d80700d007154035648592601c00031400d284120a40d030071091b1100c4680c880c1500d410b81c8811864142c0e5072041c10564654440340703030050351101d034900c070061006903201d50a001c01e100411a6412160350110705010101d88c41c0e401d580200103130b4083c01c1c403109007411859070031000e4540498039502801003e0000c226102d040801c605103100302c2c0d0824100e1071840c487c00502458001da025243c66000d0401048034540209a150300400280303003118468034800000381103d108410014205a564914410a01e01c00e40c191900e641005406e50301482c0c010400001179140c50805891107400c81d9400200300f883c005003600300312046001e1550405807903250f80070b0b982000324151110398071031011211080213400206402481600d0004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 344845422 1250 344844172 344844179
    0x601081b1305030f0a141f020708070f0f0b37090f0303020403020f060406020307201507060b01020705030709020903010207080c030d0501270b0a0e010308190c111306050a0f 76
    0x2420312158401c1c100e072641100550300700c101554002103005c47d10320400540e4030211840d103103000d4842e280b030103016240300c1c43e0340004000002c03203c55140c1d8052840300c0c04686400a14245020000c20900c51070701d03a030304400c0c0d0746e001149480b0b8101c21503040300040c0804542c4821102c0c00001602f20300280e80020180708520b021510b20741005000d40d440c40c1010304121b00a03660f0312030b0301c41c0580140042015000c0c400700201c0c10b040180c2c1c0c05029421140d040c048541820f401c160b808a40880c1000070700141544006201411540020000e0524030b01e001c034034800039401404201d130195000c000c2c18020590f010000c1606800d008000d66131240718aa13035004403203044e00000300c000d071001e03070040312038a0122195114211500c00001c0c101c000c440013810341941a0300940756220310304000000c0c440e101c0062324403210400c4c1440040c030782c0c040d402c9400304081d00d4020900034140c04018003904110749002a24045280d0000d40d5540350380c00035440040d141d2240308010800303080ad1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 344846672 1250 344845422 344845433
    0xb090a06110310120803070518030304090c09080a020319030509030105040f02010e0d0c0b0d0204080a05010b0907081611030c070f05010f030e060105060304030c0c06170601081b1305030f0a 83
    0x80004103541101c040300c0c500c4c03a9583caa4a0b03c03000c0c0c156803c102001c40d0b40403042c046000510a2008014100c903134a40d0b40d203820034040c00e010300001c0701060550304005001c190210300e803a807540e1700034068850106400305504c0a514440000d6040003424010003240e80c409120340da00480c094170b04d01d400c4140c43c0c0300060040320303e0344a850280503941840700015113480c80c51070a5030407400341c05440b4640c42051100a002c5c907400003941d44244140c42c000e01006501c41542c0040554840032156202001aa4988410358420708400c0c0405414814540300c0c130058081003a860040c3e0340f034500700c0d503603113840d01030181c00c5005000b844005c00c001a607000416804079015a081c180322001c02c0454450f00d40d80c0500ca0940500340010000702018800d03a580307001c4903480081a44800e03140c1c1401401008001c0c204962034a1400c0490a2503000b520a24400c0424460030315200c510140c20107210b0f008040f050b00520040c03070001c64a55820300420708000c030003e000700688101810607 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 344847922 1250 344846672 344846701
    0x20622030c03021e0108070f0c060908210408030f060a0503030a02071806050d0b0726160c08031512010c050d0c090303090905220312050603010c020a0b090a061103 72
    0x6440001e0340719144003c4c0e40c0d07000754009600403500d003804900801f61a90a4400c0100503c2c01000703c2d02d4589243c0400405402500e41c0000c1802c8440000ba10038060580000054030050035692041c03001844140030112091341c804000b0f000448030540d20310119140d034004441e5480543c00408050020000e00902d4a416404081041c4132a62500340030521041c0c00360400342401e01400002003695001e840e4554994034061410304035040c2910f07030062a49802d80d03841d6003400510720300d009518440e40e020042c094006941d20302e140c51b140c5c0800c075040c0d08050748507044140010010740e02102841102d010710644e483e030543d10b141412154045502400402080c403600c520180042903000c40b0980c244c3d983c2440c009a81e8440c200750b0441c280d18258582e11954100940c9c004260348241c545c901452503010501040e00c0f948101806e81d80b01c0460040103078402c000d03001c046003030500101c2d0400c0c80c05081c1c0d042601103442c0d100c04e448515542003d102000411700c0143c0307a00341e46 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 344849172 1250 344847922 344847949
    0x2030a020c060f0c0a2f070609060206190218060c150f010e28020a0c03020c0a0e06270f0108100626010b0907020c0a090209030703020622030c0302 65
    0x100504d071500561001d401451040d07001c022202071010550300a40c540c41c08141c0c50800014140222103650945d01d05080c0503804c002070010000081d218000600c0c54001d40b01d90340d2079162055aaa145002500301034400b021142c4a110140c1c4c250310b41c08010b200c2080d180025221420716240284407681000d450030b88240645e0004019440c5101b44158201501040101481a0109074241211421504100140e100045602005401c0300038204010310a4090354110481401084040b1800d4451603581003012030003d2920300c1c02301e400c610120003c0785d02c10080b902c2403982c04000392049520807050200000180f2403070380d0030400202840d0301ca650600200b42403448045001d81c5c0704445003001441c5042010b0412800e400522020340050a001c400c1d19003168000d50b244403042d904c5020300b8100c84003042405a41c000c45540301006001401602d14550a0000b90341c00303540d038110141200b1142190007820020340c0d90095020303c2403035120360300754010801c0480c02401c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 344850422 1250 344849172 344849191
    0x140c030708060606130b0301150807050304030909150e09060106110313030314040b07060605010906020703081c09151a01050306010c03080702010e0f01150503010b06030f13020402030a020c06 84
    0x300704418a80041d409600580603100561205120107101c5003c07002608000300f055004400400c050b00e1440e08011120391680da80c030402d8a030440151041c1c40152009400214000014800d40719a83c0000002000b000002c44180d40c0d41d00050b000508141c510281035013102004002d0756038403900c03201c48025040069403524698001042100d505840002c080c07000c40c40c00b0700700085010064a0041c41120b176459034400d01890100000c02060040f24041008500c020440da840090600262a80070060b1464101c11403220800e03600101d004030b10b59510360405400050131484c400c4103071020303a6800300d010703410301c240e490019244070030150420034140308001c81603074446142c5607519010b040864140d1110354049000d002d28000010842c40380000010516030305606c81403804d03805e8080825000c3e240d0342058242e440b6103c070a03074010400c1c0041520807c00210903500070a04410520488206034081b500341e0f0011507485000550225014a55900901a1652158424 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 344851672 1250 344850422 344850433
    0x81b06040e1602010603060504051c0f051804061a04090507080610050307030908191b2d061b0e030a15110d110403050d1403010603020f090d140c03 65
    0x1044180711610003444500480c050604005405000b948000051908080d003481146000d041c60f55841074000c50203650501c0c402c0034100b00c20b1040ca491880f00c10540e071210303d014000960502145000b2021950180ea81d190015541611000181804203001038a41d11146008000401c860000b407a550602520f0320400c219903940e0f046288240c200380c24160340b82d0f280c5c0300302140103009140340100203890008410404c2c00b0300620030004840c041d5211015241403030703c0e4411510348200014000d2400384150111001180040c140041411020b601000c8560711090250344004079910a80203020400c1c3c280c8903440115868002410380041c0000c2c0905d03641d00c0b80d0020554070005400c7d1351556519002c0383d43d5400c8407041f142c0c40a00b0f111440036045504400e5106200807203080c8103802151003281d00071210007080480c00c040e2582560301e000c00a801170351240428840201c1d0401464100383d459a0704030750214041d01403e8a25540b0603074031480c1860480290f0f1080d40003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 344852922 1250 344851672 344851679
    0x30b03030403020d0503070f06060f06050903030703080415051005010e010c02130c0c060603121107060e06090d05011e0f1503021203090a170d080112170f04081b0604 73
    0x4100c0c0e00716a0b068844101201c11818940d082d401131707e10082c8040e66411f080d2007405950703004038082e40c401001c9040120303130b14481a00c4511580045c0c40d0150014030440d00072034003554a1940c0300f40146600320800a0418251084842c1291140100038103001e05100c1d9582c0705104c3c810142c02820503011130b0510360005013105070108004002c0d20740359103410b80d10714440c5200e01c0140b07902c40020710186849207010985109241a2040003030003911060400383c000080500495420380c0301c0e034990f0304070107003405025404840c5142c1c11110ba07181402c0024001d01c1100c0c40700781a9001c011060160002c1107098810f4007040485c65810503441d880b003240f074809205c00710b9034119031044586100b071080c1829800f41d110300c65401041d601c0e0004450301c0c5180107940030b075541002d072040c95150a009442d414002c1c01842c82800f10351029038001050311026040c44000002000d0400b40302d44516855684240c00c21800b64100184050121540615648000710200c68440c00c107400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 344854172 1250 344852922 344852929
    0x40201020312150a0602071509051e010c0f0506040b100602101d01060b030f0109140f06030c1e130203060d030507080c030708210c0307110f071d07030b 67
    0x41e0b6440c0702400300007000820300c0548428050000c414000e40104c4070329540c0c1e40041d440e01c12510500d000c041402055842e000d21809048098403c020a6840230440320801550000007002e0428140112503544001065640d480390031554800c80007071540b40341c580b600b245038810103000349518045110701840b82d203802284c203a00c4108040800226100c000c1d860620001c0d11654007e400c1d4600b900c045146a00e5000070740c4904d400701a5000e107030b682c480d095005c403000d9050846c2c4496121780803450710710031003681e60303002203004007110100000c880006480d0710904004403048005450144070b03070304200b84102905501010114294500744004c43c0c060b06a4550050411600107a0a400c000803d000d44080400c0c03c000c07261208a645410304050b0b014019070103a561445000c605200309410503984603094003401541152155001500c3c2c0c2150104409560b005814800b005581c080000070004c2003460341e00c003140f094011103c0307060240079160000f00b500b84088000144c6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 344855422 1250 344854172 344854177
    0x4110424120b0307030f0803060a1401080103020630090d0903020d0b042102030310090513020418051b040c2a110d060f0e01140a02070204140a020a02010c080402010203 74
    0x9440c0500030541004002c00a07003008565000200003100d03c01001091003501c6026520800c07042e02d601d40740944800c001d00e0820075035074a441c00190000014401814504041d1841e607c0500ca0040d10090700e1203154100c18001a62220316800401085840d800801400503200d07081d05100321001d045030007003406521941005040561900042410807100d03900040100c00d010b600c2c0906011080704c000d41307950096032200d00001e007607107000c5a1b0b4003081c070030207025603641c000c40044000540c1c203100181480c0249000410300012101c800301d5002e0100c2500028000141c03120b400d001410001100c032000712113410442441c0801d41810844080b400c0c6074800302c410b602d00070b11240340000c5c90031012000303140c0019042c000c0070104007898001440c500c40f1100c00380026058040e00500b00d0784480e20039150011003101151a501c0264028100c3c0750002d4008180c20b01e501c826503c0c0c00034142c40244c01d61303500090b60400c166080c829544504028540f50600c0c2c101600001c0d41c90 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 344856672 1250 344855422 344855447
    0xb01080717040821070e010206240f0303040b120f0a1118061b0303090114090d031107060204030308090c1e0f041b0f0320190e04110424 60
    0x11140060050502080084030b44200920404c840c80b4900c0c203448001c20303d0030401001405886117070081a241c0f00d56910350944800084603c0260034040020021425100061281c06010412002c0b40000c41c00004018940071501e10702d08500b4184002c101c40741009003030b403410701c0c0361000c680050b002d043d0440f03189640c52001030807041c0036000018010b10454080360f40d02443d03401c496031034800c0803010b14403c6282e80c1c02000840f2400a038010100c2080b91441100d4101c00303801210140203900c05007004907020061802c00f4060b0782ca01080307034807581059010540d54410054045420407689416402c00d490071101c2040d074038503680380034041d072040d1445004001c0d000030341c50700e1300d5010320f40652b00b2a901042e020507036100035040f0041100180d00082c1440c0100000c40710300380000300701811031035000e4178202c0c0c003071503080301c10102c0c4600d4010040f0001606c8456510303402030882000125942d542d445140003e103402c000c00340c02d01074401c4443d4101f0362164a802c11596920b130b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 344857922 1250 344856672 344856683
    0xe060408030a060803030103060b01030f060f060c05030c012a090312030b030102120c09100216031b08060a020d06050d0f11030c040e03030609010f0806011505071202010b0108071704 80
    0x9a88070703402c920020703140c25080140540310110000080c02015004000061001e80702007200c03690903a4402c00f0b640c00d40c0181e4281e180030a40800045219000d0341c1212401442900d00f0302c801c90784403600b035540700e10781380880c0302241c2c1449550205419a01104120604202d10780526603559213000d440b88407544c805143d552070805d0f03940d45080d01210b110840d1b200b03180c1050300d0a803074026540d402c11144e040c06001040c810405d00341c00041d003148109801c88801d007050745150303500c10740454a8105808407028408d40000c80d99020404240601140000580c5566054006200b02c076032940c1300c9071240c82142907242c08075648a11490416400c0219080c0a80d0210003003850b242c082c0710741c1034103c0e00d000e004203130120001c00618002c4908580d84101e07640d07107008240c000010742c05803201607045400104032005008dd1503800d54000e0b400c0c241e0501d11144c640000d400b44040c840400341c2d44510059466681c41711031a5400a400d01f042c10942e2040302c4440782c42c00006000804 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 344859172 1250 344857922 344857927
    0xf0d1e08040801090506011703120c030408090a060905101e0f03150b09030f0a050d0809190b150a1a1e041e060201050f0f040c0503010c050912010e060408 68
    0xa10140e80c04a801401a0000034000611145861566880240304501590304521030f0402010408400c941c200044414622043e44444000320783d15032000d8001c840310b000400101d1384c1501c8036500d0754000c0c02c058881004403840d01c800c1c4450701e04420200c2041003401c0d0f40c44403085448950081c2820304a160012039501000d01c150018030400302c05401030039032100b00050590301c0500a0245d458180c003075a407840080c200f540d55518400c80000c100d60041420380d024180f142c3d14561f440711b6107104481641009984406140c0751403c01170300c500058000704400c82220401601c0b400e0b006440c4003885501d81300301b07a0880010310000450301c1034000360458860710103c00c022200120001380c0390380e440d41d90800e1001580580440c2211040c05040056500e0061050b80e100d6a80411180c4141d6640302c8a6101f4070b20042080f41c40c1c2032032440101d0f803500c00340704a01c03061a140e107915030781e200002c0400c04420445208454035030706122180c038034444081101c54100390f20015494 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 344860422 1250 344859172 344859233
    0x60a081e060f450a0606080f06010317070c24022b050d1a01120908040302131410140604080a030305090307170a12142205030d06050f0d 60
    0x401e00701e581040850000e41500200061840200320074130042d1050000300200c3c0c0d50b078403c2c5074030341803a5045101d01d900300000403c0401c030080c00700a2241e019900a500d000600d40d51004410169048042c41540750607500c006411041070001103113149000600c071090095041a8000394603210418185100c0c1d11103002480c001c0040d071302000403020040c05000d0150310604038403c2c501c00c289000404007014980152028410854101d0b0090091494a811a024403501c8111501140d00c1540e9828601900209811841d03000352074111441010034a4505080c407860103200c0030510581d02040b081000390070002e42003041076403600303001c41c0030b5072480951420b6019509015000440c020500c07414171034104c004000d840c0480d2922014050040d00004c1100c040316550002c1a0544c4085000f404602080900c0140903174032441c1c100c1c042d647c031241150003114030904c1d4680c54284c20f000728034001080031502d0b001500d180c480c2c2425a03d03042d10381508038007001401661002d150 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 344861672 1250 344860422 344860501
    0x1e01240e04200316050f0301050f060904020d0516020304081504051912020106120515060415030b040209070e0901090905070e0705120601110a0605060a081e060f 71
    0x35031407003000324003400184011181e0b549590340101c480b10350881143c0c0502e9115030040042c1c1300c0e2540001d1050741580c0c244405c0c02490031a0f00c41c1c40307501c03d40500100e001031381d07580006c00300030910078808509418110501035102030321085120035034105100901c0541c400159200d066807688420a200da00d40d810014241121079105110454040941710284040c40140f15031741d090b10781c000c00ca0710341e5a01030090080910b80e00205960000c43d4400f074500800782035a40c018400400c00210105a803c4030707007907064036500859410440c04204400d600d040f044481d03101c1000e040880a440d121000680442814065a00d481c0d5507070902030140007040122001400003640c01910a080c40c05d4003409603000302c0340e071692580c244000035207294030a075408018080414020000320301b041e600d04c0050030703004010b0754110401c100c00250b210010400001036801302c4001c0880c501009015600704140101036040600d41035003446803102d0750740200c10b84c01035413144820008a146804 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 344862922 1250 344861672 344861681
    0x10e0405060a05031c02190b0402060a020f010606440c0904090c03051e030f0901180906030302060109090f03030519060303030b03150126151e01240e04 67
    0x5a0144104c00c29070140380d90601c49000017000c0ca400701c0e054a5403400300189810324150000302241c1050700403400504180015100545250051701c0791414020300303090841e02c25a1000001548a80d028003084c1d1007803276007403014148078118400030140e0017481c1e489500d00c10318140142002c24009400341c803c4406076008010300800601c404400345c00e2400011a030f46c0002e072541e00490030039407015403180301c0742242d60320000d01a500380110320305110859080340318141c2c10301c80003440e0900c4040d040080c3c00040d1600c1c40c03000950608600b0001c1c234002050b00900d070b50324505003520020a991285048080307505240c0424103039540a8123851540c600c03900034540c2c074100a40801010341642041500b0442034046807403000c51180368a41f508020301c41d64041c0300035200203280142e0040f020380c00d101070b882e0403207030301090704800c1c1584960116001000320507041e0b50040501221b840082c010017400c5030001404101c0004c492040c140200901d00b4404045800009038990390032 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 344864172 1250 344862922 344862929
    0xf150207031203090b010b03060d021306030c0312020607020609030403110409020d05010f0507020c061608040b0d1a040b011b0311031201140a03051b03030d060602160f05010e0405060a 81
    0x1050300b14400300c101074058001a881107410b110080700200301644c4e00e0043d80c0c07098800a113080d0030645540c00f400410080c2c0365801c0005503d070400800440c441071034a01c0118400c0302c402d1980701030890000c0c140f04005d402c91045420000c140120208004203403000daa41203810151030328a80000a0010b0210400c025003018010203043e00740801980840905030140000b40003507030b5030311422a1200502c44410b41d20a50902c81c001c4d280c4090040d40c0a440e1066840500d860384807a02e484403504414000c00c04207866032004200d900603200440ba0841c4107030380522490b90321400280410440b0140e21a408081004000605206d0455080360b901000c007034a03655424443c070100d030342c1000d00032a210035015040d01091400d04003026030481c0d811030068071f4014081c004100112601055407903041c40148881b07010100a8800c10000f04043c0d0018001145a1076441822002d1948a0100342c03107000c80800c0705980142c070703490518074100e5000549584c0c00c0000b801d03802d195003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 344865422 1250 344864172 344864183
    0x303050a021903021c0f2007030605090f01060503030702010816030b0604180b1203090111121306021e061303020a0b0c0304141c0f0c120206071403010f15020703 71
    0x204071018560040765010985500b01c0c81c00c07401d025411416070f07990180c5008580024025040e01080c80f000300ea00e0101f65645c581502d201ea40d894076400b003510020303900d00e4543d030400092007128110912a1800401c1c0030380186083c4140c0c0e400203003400000804501c1c1c1c880e2580c2c0d00200d283d01c2a80003014102c0f006001d20b80380d40c0c84001c07031005900b10203210701e0314600c4c040900c0828680740641545080e0482d00940c5014040001180d8041246a41d640c5600c124500241002d403141c010300304403003010007820300682c6081c0e8000d00d0070261402040c4402140707031354525036107404108680d22080d400f43c0c003034100b00549422441e104c54440301078644020f072402d000d0250050001103004034041c00c503c60b280e0301818100d9403183c0e80849005203084501c14840d0b8258043d10200c8040381a50034605198001601e600f400503123070000c0354005030007490400c21a242c00803041c0d00c1c0e0300800003c60342150304000c2000d5511405009804500300c044409c40e400910803c2420091580701 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 344866672 1250 344865422 344865463
    0x6011d03060c03090124090e07180207020a09090c03030e030c0306010308040e070f0203030f15041a01080903070309031b0b1303021f050d050a0213170601050f09010303050a02 77
    0x654904007030340040d540d140c80c9500b4141c5445140c6d00d0103d40b41030000c0601c0f0074815144c0b8101d8030b40001e142c00981d0100c0381c005c10100203503240030155040f800404400c8050781d207529610422280780016040710200d03a00e031544d524041040d0808200a0b641c0c1740c1001d80d086e40d44580040e281904503a505507140c03080784004800c01500e800980200d5900c115138000d151a10541900c00c4c0c840011042c4c0182d1040c40011086035101c41c00540056110b80040c0052082401081c00e982d1081e00030207111003490181c0d030203560b008403040d5021070141c002d1420130506650050442a41344070107003020710004040016400011840002000a11aa03981d94007941650356600040b9200a074403d141400000e001c4200941c0010b1200f0b20a42d216890311651a00e504020f210141205441c15424000c00ea0461141208040a0f06099003003040c60f001000d8081e00d0000c2c140c000e2405120403c107501c03100d44403044000c0c1542d40c54280303d500d500480d030049280c181e21000ca02c8580001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 344867922 1250 344866672 344866681
    0x80d0b03010b060c0a0501110a08041b0315050907050f06090906120105040c0609060203030f01061d03030a09180e03040303050307020307170c06070807050d02070512120f01150806011d0306 83
    0x300700c00352a2043c00280500000c5103408ca1903802600d50040104a00c100000d000074650120a02c1c800075003051950003948a848681e00e01d003002440d103072050342d21024410f00f0380c010855000200790403201101103004080c0401c0c1c05001c0c46200501510108001c16050b03030700d01d6441c01e0505003143c020841c40c40c1c1400e280031072807550302c9038101081901c0e4020884600c00310480307200c0c010310600504607901e4880c0c102c13008003075040301c80340f810151054000c40355004c0c80108000f0190380d95100000e4100b10890341c40b00da00300f0720301c05c900e46802040f4107400f1010041d40d04598040c180207407250b07541c80c02070741107100394200242100c001d40c1c8121200000c203000b40c8441001941240c0c0140d445070713820b441b044800d94400003c44e6051000321f0340d001181d0020120107108d5002e403070380020300c03400e01e801642041442120040000c820410403540620700f6900415202000c003089003410b55000d01900d901400650400c0308045602c80c420881c01c0300b141c50300c036018048a082d4640b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 344869172 1250 344867922 344867947
    0x50310110d2409112505010c020606120f121303050a051b0405060306040809060409020c0f0c0d0b0a091a070c060b0109062f1009020f0d080d0b03010b06 67
    0x5640414400c04038050b03000300b42c01d1040d01c0b0315482180340c0c46032903240c04000d00d0019082118030340d9944000990b14182c0c0000395081c061201c1d8a4002e1300140520f04098007002a40b2f850403e19402c1030707102c0495944510320000b64444555107080d80d140c3d0700c01009219220400c65a00054418130400201800f040000a02803180340142c00013801daa180300010001558004d640a50b49039000380085008914a07400900e840703500103005034a0b2564512090069800181c11408160049191580003100c02c3c0800b443c0e031242220243c0c20740400d65134907004050081c2c1500c50300c80c0d4400911040117021414a442d5180d0307500c4c001030620b0040310007082c204441104071000c07814084007100e40d500403049a400e4841e980c07a2402c00c0d8410398801140c0848071900c1091030102040542e404030700034011034091240002010511144900502008118100c1e0359401142040102c00100b118070701a2140038018000c04a44845448002405400f01e43c0109500c00d0000910022040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 344870422 1250 344869172 344869211
    0x3030a0903050105061c02040e031606050603391c0f061515080c130e0f161407050c0406060314060f10050a0903050604030804110a050310110d 63
    0x81c800ca009100a594050038043c0400b400406e140c40340e0126110f200041ca03058002040701010b0104507410b001400010001c15040100c042e81c0c41c654481c01e11000b03080920211845400e14051080c0d0b400900e0007200d04c03002c001d100351807103a0070a48000c0c0d140e51400d06100a4074110103601c43d41000a0400345601408988200c40b900d02c1c008810300e50340545001403044070146030f0410315408220300705481c00c6200030907101044108004120300040c4080c0b21038060502100f1212444c98008903c10014601410001c107001201c020301801550021300c0158511881c5001da86a00c10381c50407914003020740c00700992180c106103000c070703031154158000454507481408181c059114a4144103900344964002030700242c43c0c6020008041c0074400500c0088450b15010300d030f40d5907e8403050709114059400318009015041844241310f0340541341c4021600448000910724906400699501a280340e9102400d45515100e103840440b18151541c0e8407003444203208501d56100003c5284 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 344871672 1250 344870422 344870429
    0x501050f0708070215010501120204080f070312020129040912030b0118081504020a03080304120801062609032a01181e020409051014011707030b09030903030a09 71
    0x15200340001d0040f510009005800b074240004a40c038a90800c001180d56103400c42c0342100d2645c08103c00031748400c040003000c840b429007a01500900d81146850300402078410351004c03c583c10308242d4440380e001100003903603890190320440782481100d40421302404440001405c054040c4800003c40c6400da00603901990003681c4014180141109940340a07805c0c3c0607c500030b070b00030800440680c140022264120340014101b10819990355910107050f40215401c60743c1c481c20740c5005d0071039a04415140c5c00f40c1254182208411000c00020703001190b000e02c40c4c1901d100540124800e50414812580c0502000381684c00c4030301c00200e101840e6849282e081101d6103090940075800c010941e00e50f030a99400030346222201c1001d010814104440d00050703912a5941c0c0303207800001d00400194480c3c0c0d10360f0780007085107119200390108203075050b4080e460111141c070a01040e12404910813059940c82110074006440d04181180b450143c440140d82510000620b10341071600003c490084 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 344872922 1250 344871672 344871677
    0x150c050f0c09070207080c0d0302030f0406020102091c111e19050901060807050715180609020a0b040b16060b0901030308010305010b01030605010504090515041b080612030a08070c0501050f07 84
    0x21500d0b0b401c8102c0c0c0c5c6050b24403a44225401158130130400b49802040700c5142e900a104407402c00000240c2800543e026601c0031002d43e6001907204c1c4542404004101060485a039141d100c00b40da444507906440c0c0c90f81550b12813040f114600030042c1598541c0404000c018180c505104584240010500d030280140d5203e0001c40b400010042e10401c07c40344100c20503501c0500b007407007030f689182c10101c00d00900b4000c035481c1d41130080740310400268841d041e8001c040100d4601c04a005100d440303c69500514009001000709108040301c8804560407162140d616100034805410928001c1c0542d0075080d0380505480c0001061691058076141600d000310000c01c14070000e42e0065089828030321455002c90018041000304407519841070740c5c410740300e43c026948480982c0000e411111a0440c2d007049140705240b10341e555601291b000e80c482000e4940d40d4840303104210082e40c0740070f4414035004201320b000c0080c1a161181054203210f50344580244840e040103602c0b44084c04044802600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 344874172 1250 344872922 344872939
    0x109020d0522080d020d021801110d08060f03010b0307030813080c0a15050c0a052103041110110d0903020f0102061306020f0403170403030f0c0b01150c050f0c 70
    0x100803050188520342c55100c0190742e0311020039a0b61103103541003410004102ea80c04e000c8082c281c921800184888a1041d0104c00b60100741d40016088000c160110f5295034892010403400c96000250325820500490b460a5282100750019001d05401000980c150052020010410107043e02074007019400d00d075242004e50302e558029550b45501c10005a01401540d020802d010501c26a0000620f041c178045140503128000d140c50304141b80c2c0e04480076800803814102504400c1e909026007550030780010301e0b600b0291145085100c010720914400c0c02c480c0e0340b103014171740501d104011002501094518610a601003d070122101e407000740d0180301d8001100c2c0043d840421402d215540381007400040c141503449000003504203200c1042c0103901008040082044407001b1802001d0342c441d5075a403141580340081000c5a080c864005001030400e03010000381c0b460b854241990f401080c405c990840380e840c1142c1c00c00d05068081d05602800711282c10044000c1502d094270302d019640b262 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 344875422 1250 344874172 344874181
    0x8070f090e030a0507112e180b030c0a02010204030c0e090606090f1f120602030108070506030105150906040308190201050f06031504140d020f070b0712031508060109020d05 76
    0x342c49105029030100029420442d40c0d00103034003488600300c01000501120700c8840f8091000d202101c4000c68858020700d100060a05158048560142c64100800b084c5d8054505103010400c0e0102030a800c20500006c07481c50041403003581510019a0040d010f40a06070359080d030340120078429640c1590502502002400d1801c04200c1e05020f498101da072040c00c0d45c1d5010812450080c1a00a0f9403030710125500014940c0b400b181c42016280034010059a030752400803d64a8482d156015600481c0709100410443d91101011161013840b2040d00f035a0302a0800001d9041c071407904010b00c10180403808010030f04101c6446020780c02550000c00c416150115a16880401160140c0d816400259200c513108144c8001e42c0e0414868003085819650710450300d824280201c030105c0041e4007600702030758141e800b0006480104404000285042c19075282c001c17450291846100902d900c50000001e075154485024000b8402e0f071058440c01e5031221480c5001e58401c1c1c1c00c0f0402d0794103050204 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 344876672 1250 344875422 344875451
    0x4050d05090f0402090a03080f09030601120f08030403050d050a0906050f040803130204020c060408211b0309100c2105090703020f13090309060f230309030408070f09 73
    0x45140040040144000c14400c2c0100710181d88001c40e41c03900b000807803500000280310348014040c80d52110005507200c1d030201c001e15152040590202c60158505001440031819a18102000540103104140d6940c1c650a00307aa061080015081c007003441d200401448286d140d01c010181031040c030080c01141c4491110300d003004400d0340c0107001b83d0010004515116030305601c2e10017091001d4005410300280710b101c642045802c5905566000c00003980491040c203c0310605410705040b00c00c0380c424141005000d00b400700c2a40707449040317800040440c0b901c2e981001000508030849106010b208081070000385003c03010342c0241c907296100c03440e88034007000c58012a48039035507403001003000c145142c0800c1003540000100e02e8100308000c141e800402d01c540520b0700700a0294607083d0415152034001000c00b09002c40c4107041284001002c640080908000c64080300806403503920398035001a0b4a0039446960300c83e880b148908480004c40c0202d420006049a0b902e032820002c7c040075a012 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 344877922 1250 344876672 344876677
    0x5032d190b03100b0a0506030406020301151e0f030e0a1209080d12020703170907140d0305030711190302160b0f070b1e010b070615120206030c2104050d05 68
    0x46541034015003540d800503d02ca03408008420b5004151485503661303900802c000741c1c0169400c5d20035a070004010b11404006035021480c038034240ca0100c1440041e0090850b11603012700e1403d00300f150880d12602094802e40280b113510000100b5584118082e1a00b82512040783c5682008034105034000184020701007902c00040320152501040300d050140c14030000d512108049042c48107180d030788141701001c1c142d45441800080010314145080c00072030841710342e91440051148010b40394000009622100340e07030b00082d0908000748040030440d0041d0901045507101a1058850050320003819030001c0c00c0305d0a4201e21500d001c030142c80e106050001d102d514010b41001804008003000103403030603400c0d0340c441c4621070105440c0203101d4038403481110a0b80500e0807040701040390f0052107018480d0100881e078007042e000b2580e02d004078139018000b0040019200711170100002e15030321800001ca07140c05003404d900008010308c8490b010000102070321700365128421601c0c8804828051001c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 344879172 1250 344877922 344877941
    0x207050406180e0709020f040806090c010509040207030c1407051809120c0708010f091527020105070213060602061803090d0302010e0d091706100605032d19 69
    0x40b640c0e159104800c800a0309564108404510074924005011401c1d031020f0303c0d80c0d070716980d44140d90301d1500588500c0c24402510311074080e0050581140700d40c0e0004201c41d12920256030150f107d51042c1401d81d1800f0754030300080c00400100342e444a450a001ca084070641e0300c111200340e040d4a04030000e0220b01011035030038042c1d600c50620018089100e82c040d1030007040315400c444007161113844d031a0940d910b4140d0300406c1920b8044842c204850a0f01c40f00c4249500a42000348080c0041040c501d101d042c54035100100e101c0aa8506691042048030700a640190101040105038a046002804a481031000500400740416000814084000486190324005500748100042004040841020118295960b880100036000740c2440b10010a1006d40c071174480c0e040c64240d90ba26040250003907511280c1007807081010501d0f0340c0000000f80c0d0854500540c9a554a000e81c014284030780c20550700004041c1e039072108000c0030000c4188100c540320008445000020400000d0341d00500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 344880422 1250 344879172 344879189
    0x34e0605030a1e08040315060b0c0c01051309050108032a033708061306120605071103040b0a02120405030604021909020408010509010c0801061b15020c0109030207050406 75
    0x1e5203040842e00c12a680032045000811490303c0140941e2100c0301c9520560084a42c50707414910f00c80c000b0040e101c1d040051030100c40c002d1406181a1202e42c4800205052506001000c41d0180d11a0403800300d001c0980314440c01001a03513154113950744d0384d40220b042d401c03040341140743c16031068003800c01c8003140d041400c00079403c1660482050f10304202600c010031600c5038807420f4401021080c11818903000740e81d284d80019043c00c0341403201d0340d5207141800b0711650400d081040b034240065042e00a0b950030180000d40c9448003001100c107c480645070340b54610000c00d0121302d900d01c6200500c9900031580880781d10000c61000d5100c44c2c02a4400c0703030750541040b00001e0160a2404a0201c00c03181004500c8050b83c880c00404201c0c0c0142d084080c26030354030010400c440b50b0910446142c148c1034203096050b03615181e402404d4440d1510580c0c4210300d0149881704229034054000700008943c0015502c403040d001c081030081c4280341040d401841900000203041c189071040c18242c0d107040f03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 344881672 1250 344880422 344880433
    0x1701050604110409090201170a1505300f011506020c15090105180603090a0b0c1201120501110304030503072d030e0a0c03050601080d1407034e060503 66
    0x140180003000600821b81c184103c28442010035810781c0c0210f171240b825a03500056141628290040d54482074001034020340d00c070301c19400905010b003501100b07903d104d13102c00c000b10301e4080020304261a000742c2903070540c20702c580d4110510b80700d900c10090b14425402c40c3d030001840001c000400d00c168a903c0c541b03a90400260b10154820300042500c2c41804c02c60000d400250804210150700840e045a0960044540b401c00c01102054841d00302c28580f110600307006441d9580c01540d0818030071101030030618020001003140a41000c91000c206440c0d25032289003500b4050f0965004035a6000094880c9800d0110807900707415031140b980300391003c0c80d071401080000740c0050110408421040c40381101d1000000c5039010024080c5208201030162940351a12152a004000c0c1c02d55040c08400910302e40303140100825240866054644228503000e40b00050b140d0002c40d02d400141800f50100041e9007209121000321790707000a2902ca110782512070424022200c490003400e40c10f410a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 344882922 1250 344881672 344881679
    0xd030203040f02090703200a02010e0a0c09150801090c090f022811030d02041d0f041101030e0d0207060906050a02060f04060b03100506040f0612020111070503010617010506041104 79
    0x1903625070041c524100003491031210a0002020200d807c000c41d4140400100c40b09000e034207008244030318000174000c0c28511101d40d40d504428bc00b074001c0c061241e40c2c0320442c000c080c0900c4000401007108800070040c01d0040c0c100f001040360b103401000402c60804e000000c90000302e208481e05154040d00c0b000b0303128200c1c0c14894098550700112002c120140b10503e003a020f040c80140900c088200005035160305d403034094000711551074010300400c185841008002c91213884025400703580600903a1402a801e00140d000f44800110b80400313106214030072961980010319101900c003592140c202c596a00d00080310b00b403098503200d400682005001c600b08040c02003242e60040d100d01c50104a42c080c200111f8a07125030908013a1119868000703000ca04c2c1000d10520003030380c008803010701c142401c0081031621003162000090401010800c400d25051050005102428005000348a801e5842510603400c440c900c610003425460f00d004207017546841c0c030500103028143c0028a080170329 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 344884172 1250 344882922 344882929
    0x51e07022e08150a0e010504110705100209031e06070210060803120a0204120506041b030f0b070c02040513170a0f1b0b0705031614030c0a0318140d030203040f02 71
    0xc090a10803205100d29003d0b00a07035100000034000d04900c10010005614000400c404d4440e84601e124107101d0410462001c5080441d0452144008440159139038240c0c802191804880d050b080048002101e942c28005902141c03590055055600701d41840480314103e2086403001d12405105500c2085101c4a46110110460f805210558010704007035440200d140a4009124102d0301c68002c00304000030498605004602070300390080c03881d0124110b9441c034022030454800901440d0b02c00000941440c480c4401c100c10316405003090080d0705004896844855900c6001c44121040b5808541c105513920255484880d075659500100881c14070142c0d084840412068044800902d10310045100310200030b00a00e8140d545540e0380ca00300b9000150040c148000c44204544100604080300ca403609803074100c6100030703003199035010f4502c0582c02000c90466650340c0c80710344c042c0c01d000d009881c0031403d00c0c00305d20001c0d00c03243c0300300140417030403484111001000d008120100401508 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 344885422 1250 344884172 344884187
    0x61a0609040c1404091d070f0620070f06110a02090708060d05010614040c03180201120e0601080d02070806040f03030237020106140f04020901051e07022e 68
    0x40325400d02c600103d01070b00c60300c0000d41c044e07080055a00c1e11418469410289500340c020220203200c050103441303003006020310b40c01429214140c01c000301d55281c03011084038003141040500e148000c944034a580e40c0b0200a2500142c17240002248484000070342200001c03850f00c0c0c0d060340c024003450340c9580780c1c0016a44079401810158010340181920800900300b446000f0141c1103071427014210050321010001541c11851205082600340000c0d08503012501c100700ca04940e09082c01c0310000d541d41424002070480001d01c82c124414800000344481000c80e10642500c4980c0c01e0b01c04103a00d411504c1e6840343c090783d00814001d0021614004a4401d60160581c810b03040d1160808100044d082c3d8500c100c01203039102c00703c041080540d030850702481001c004111130034458980201c0720001802c110600103803a800746030002500f44180c0c4c400e400f101c5081501c2d64415800000c1d0114100c031a410018040740100d10b646420350b00c4030400c1601d02070090203015100e40d00307400c40c5801c85800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 344886672 1250 344885422 344885441
    0xa02070c0b031803070b0411010f081b0d0207080306040b15190306091a03011b0e010e150f03100e01030f02041d0f0102070303150311011425061a060904 67
    0x68081901c030480c10084c001004428083d0700d40c00703450308041c180f00110000441d1101d05004002e019101da1980042909500520b47c0c07991104800c0b04100c1506548a1441d40b4048544001903042c10406024051400341106072020840e00c0d9010051103146042001c03144000001800a0403a00072403001d02d80100b02e00d8078021602541d1044944140c404010582c00b0b0b01c42c0034103503070781e00c1c0c102440780c1c44030346000c43d2000300c81c01c40040c40030b89200103003440c050400c50303045442c1d0103e465118800d80c407140542411940c4d0080448881030a81056980441c000302d14000020030a25480c1681d050702c0c1c0000030840001410b5082000400c0000720f28040c401040f00d895030046014080c01c07581c41034031f02c00581c1c0c81c541450001c0494208284001903200300d8041070001c180d164145402600080c24901d01000e00071500b000c1a000d8a0030000d00300d8900c0140700ca883c484101d0041480d0302c2510188900800b10441c0100500c60b503e0075600250b06102085ca1440d203908505a04c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 344887922 1250 344886672 344886691
    0x6130b0a140a03050402010e03070e010501050c1c081b0304030206010b07150905010f060807142b05161221050f0c07140111060406020307030b1002150a02070c0b03 72
    0x800c05410350400d40d4101003102e20100c0c1e5100c041009558206410f440f11007011009000b40504109038594240303418054503041000c00b060032211700b402008040c1e00e1142c1441104150150084000c05801c011a04000760107a06170301c0d900b01007501070559000ba641900501040c1c1e00300407140710290480182030b241c0648900c0d440a26144a01c0340c640010700900000c9500c00b02241d42a00b981d02c42da0259641d5032000c002040413920800c4400c080307034021142881c80f1444900d00303080e1000506c0e866034a51018429440c100000011800d000d02200d54007000416502c421a4514109425000e0a05680041910400326490142d0071884083d801e140741000321200050010307800920000050341c1c00319000f8072800c2d03100040500e25140900e0071071070384042c0c50001034644601a000418958000c00803034401c6001e03401110b810781d005440181c0902d41d10900964cd2008041d54420001c00714000c10f0040c5801e0007202c190a800c80c191414207440d01c800311070680d0004001400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 344889172 1250 344887922 344887937
    0x40c0b03010e010608040602280e0d020616140f030901080114060d151203080108070503030903120c070e0a14150105090603101a040614120103020904030c151a06130b0a 74
    0x7281d03824031441d01642c00c0741150303290205810000d4a642c480d00c8529100c0d59090f1542f00040c1c0d5900c0c11165850900c4007042081036061500154030138001860b10b5190160a0319200c00c0742e0004040c00808409070b031002e50590340c41e50090808007090451a821607001c000703d070100800b0390000d00c41c0c44c01480300480c585549407401940c16404010460019420314010082607600700690006450304401079481c0005540001c0e68444a0103550130540c030021580404407503042c41200b00410001c0d40745403039454824a07080080183c40c50014030100e5410104030700c0500021601140134041e140e182c03424581404000319600700a10b14080300e18156008201c9150502d0306002100104008070b07100c1e424440c000c0c2c024460300b070401e0b0310000e0601ca4511b80030300d81e180c0e007411207805885c00c4010307484a0408681400d540c0c20064441a00180d50048152155000c400d02c41103103044481d421540b9010041d06119020340700007a00c0d0049030500804801d140140b1040602c0c0c04c1004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 344890422 1250 344889172 344889187
    0x30c091223010b040608010b0303043b09190203061f050301060b0406091a030f0a1805030406030c020304030b0711030c190b0a1404080c12030a05040c0b03010e010608040602 76
    0x1c010390403074000090703515040b9486082c04c06010b0000078200300c0c070090113103082400220340c2d24001c500c01d13500c5540c420825440141005c404a40c80031040150401c001c0208040091040105aa9640c05449002480c10800201c1820348840c0c95009000d4059a11154150a8690716400c40414070340c405410020304d6503000d00c070320030042001c03144003500c540c07030164007a00c18a007a5200c6088090b03540c1c1e54204090192044940c0303c0d603200b501009945401b4000d000034546052429001d40c018544a4148180007001c0d0045400030b650a01c0440e204c00310881e00c9005521000b0b00c0701c00c01c5408200518018801080e0324035502c4112030500055180452600b80f80040c00b100c40b00e042c24202c02401044000e1030360102906030140030b00ca0320540400076800340100098100c00f40480e000e801c1d09000d0040601d00c0300300c0302e9540d0302d0341844000c6200500c000e4604035010408014002203401c41c0700300340d030b0484407147c03810743c1241c0c030340241540c40354001002260000c1d42001000e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 344891672 1250 344890422 344890463
    0x1a09030a02060d1416022a0409060204080a03030518011404060c230406020d080402010e13061211040f14010e0606040f14030d09120f02060c030f19030c0912 69
    0x345c0b10f0451075034002e052814010300039003041c060380010303003110f40c194040a060350301c1c0e040c0c6405a020203490010f402c40c0541000f10090181c0d80113240a809860500400d2682c150400d038051106507400306c0000071142c503c1422190202c20040b408128040060040342c1c441e40240301e880d802d07081c88071006a45558511031fa01c4140e19111803040c01180600889904001d00c400c04940b6040c604101d00381600040c2003a000117403903c0c401e08241640140007103990300080700805040000d85420701d41494441c80e1445c2014044d80150b00e401088103036540e030b600440401605100c0c101405908045503140c2d40e500c0201040c0d0020010080065080c4030494000c00400c80c412581070501044d2041601b4020416805010041d02c59400d001030488080b00c03110b6a50b111802d416100503d101180060003902503075000c50201081d4600030804840050900e030002050101c000c40056600742c3c03c481a1701c100b180094001c0b04280b10024203140c00c3d41580d0701400c0e80c03001004811000c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 344892922 1250 344891672 344891711
    0x171c060501020c2224090605060d0507031b090305100513021002030903030f041d06061b1e070501090b0c06040246090524060f03040b011a09030a02060d 67
    0x31500c19004c040040c0301405d02c2211144c00b40182d1032084c440304d464040021514010078182038403495a610106403028001e0f8042c8003a00c24a071040a803603506100d010740407075030300c1c0300a441c1c40c0100c0c0e511490b840d039248160351092900d410390390311041d010380a101c1080d05000b03c02c3c0651200300205c0f012a0307420000b17440c3d0300382041e440994681c10f0109900c40c40200481054110781071100303015595940b9002d40b101d21500494010300c1c2804029024500501c4550341c0130038841c8002d52119419002c90040e0079503400781c885c480d9403075885021072032500c101c429a02c1150000d201140c014600b01888401c2c417aa00c1181c55849a204886040d0040b00340781d805540c5449030b4000007451402c900c001c802080310807001c0095280c41c85c0b56449c400711041c0a0746034600e91904240840d0703191419944c2016002c0641d41c0c42e89003600d08104009001c0c081c8540000d081e65050010800708012a5040c000283c06010b41c0c19a82d07080c4015030700100b003900f40031519511124114000c0018 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 344894172 1250 344892922 344892941
    0x6090c091503061a0102120d110309010c08160f080a1d010f0f090305090f0616060f110f0a0c08090d110f010806010f0c05010207171c060501020c22 65
    0x6480034000c0c0340d460705034100c4042ea040316803400001401084917a0300812020210480c44001540e1910100031444c02820b0110040720001408401d00109100560101b00c80304515201e04030716854505840210340f580c100140002981c6c0c00c032039550700b0b01c03810344903401c035614000205440030300301c4448108000d001581c000c0d84c0c1d0344106807040402c0c98082e1002640350900104401086500c0c020400c1c0700d03182c0c0442c02a1007012400080b51100d00c21550f500014815915140455151240203420600c1c2c200c80710600341280381c21003074250000c45030000300c61101d00703240c0406048250f80301010070384140c804000c14081119191540310f4001c141a1141e00d113400a01c4034036040190b4804000a024100a045400c2000d603036085002c001020f580c900340601c6146207803030038a0191141e0103005201c035804100d000d140704000350240050b08200102d515600ba401036546044404521540b8016445001d80f0341c007034204814000204c406241d03201c10400040360b80312040d510204c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 344895422 1250 344894172 344894201
    0x405090c07030e0f0a090e0a050a0b070e0f0105030a0b01121109040609060b040e13060603230105150103090218011d15030a08160c030b011806080a06090c09 69
    0x1001001c241d40b181d1a15a43d41e030459012641c0720400e03010458980c2140200542d160782e459078000c07140400c002c0415910340c0708040710000c3d030143c900004950003d0359444081100c02c4d140065034076107a41e611400f540c042e50b170141581e5920061002030305591013603905020b884845c0406101a41c000d503949009122400c6941d500040c0601c8202c0d5601e5110300c2c8a14507019062080b030300c41c0e208650864041041c03442d210303101e50500002c891000c10000b800c883c0b034000700004200c05c074480c0f0491000d0580008001144100c00603090b64070842c0d40d40190740888200042543c060f80c40707951600c2c000b07801007110034281000c15003648400e82143d81d840b0181c0b0410809075000e5841a40d00522b0860404d0f0f280c480c04002c242e4032207900308021700e07080740401e501e0341c858041710710080300c2c50308440f400d844550369080c0021042c0080c06a00c404a608082e064829001350103101c085640d0a4010188a140d41c0c86032001440d8001d400c0b81e200d0702003d800a803020b440d0141c12070241406 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 344896672 1250 344895422 344895427
    0x216020a0b180d020f102a0c0834170f0705120d050a030b04091109090f0a0803090703080c07090c080c120a0b040906090b010e16050703050405090c 65
    0x809994140c02c842250241c810080ca10610005840310121000ea20100b6500c807010016440016908a40401415000c0784000318440c01d19601d0485100c14190203100e00307a403281d4450030348503142c0040c00e40840755800f40c00205030102255142120100500e038000010315600d40d5000c00c0d442c8042555814154841e601340000c12600f401940000c0004440c880e4600002e04419901c900154005200380300740401e591020b0381c069004100c0c1250010010030140d030743e030728108800d4030450940500a8000000085c25034a001401c22003e0203030a0050050f44019601c00d05036501c000c058031a00e00030f1030000000070707940d0405441e4945011024000c40c2c0d081060950840d0389000b80d18040200070300c180800c680841c0e040303481c0411036507010300c0183d90f540000c4000c2c2c01a64803954001e403a00c0c802c00180145c2e0790006900728401c4c0109821660f840781145220340741510355620040030040103200d0580110014050644241407480c2083e40d150002030006100311010048039400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 344897922 1250 344896672 344896687
    0xf060a1d01031a010608010b0c01060b27010306081009050a060e0607140f030105010809010b150a090b040608060d0609050d0504080f010c0807030e0c031204170f060a0216020a0b 78
    0x241580c3c83c1c9030307a6820a107903a40c03418000400c041410703c5002c6000f02c0008204a00f60000e4001034050a900400d1079600e4210321031800f0b4a0300302554a501c60740000341e1a00c05903111317004040448450500811851500d484400020040618211650b102d0348100100165083c0541820101c1c110050320840c54811405400f1800009c0f0b2000e50070800c00202928604040a581c15103a00303107405825681c445040c18010030000d88020f41c003030010301010518015081c010319581741b880c1d03251241030341d4030301910915005500950700451b901c0d10020b41031341050100c0f2242103005202c00300301e608282d103030706040400440c00c080c0001c0c40014140108002000602d400598000c02003080f20108000200303a20005020a010991207040d1400a0101001100c122000003010760304214007540720800298014032407018501d2081c072008006802c00300e0812202c48924000d080d01d9074546095070020340c4a84040e240000c5000002005a20b5445150300900000395a40f44d540e004d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 344899172 1250 344897922 344897933
    0x50a0c0f034b1e0312020304030906141e130b091503040201120207080a080c180108100306020d0f140906040b060d050d1d040b0105270907030618020a080f060a1d0103 73
    0x18009117010459004005000000742d001c80034104179180c606d041c409006800c08250840d01c40e9084d4030361b51400c001c914070003022000b401404c1841c20590329500300d80d501c680000c51401495100c0b680f01241030880c50960360b84c6030082d5806841450084c0e062802510b00c4001ca8100b04815181254081141c0311480d801448640c1c0019442d0708890801011502031800342200c140854108131100300440c5c0c6e030007108400e49000d964442c40c295241c07042085001d0041040d20b42007160507007002d00c8101d80403180c1007554040c2031100090035083d079450b14ac0d801c00741c41c06021a9004880c2c1c0740e080011032070a014548102d01c02c0d6032020840a2803005858252101d444200d1050345007180c4034107580e030007004842c091001c207082101764405841224070b52a000103840b0350060581d0f0200840c10394540e00c440169407840c5c0c03181d452103441c0c160450490182902440c042a1420089190308480c810315640c41207000380407000050b180d62203400c050748a02d000260400d04540103104028 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 344900422 1250 344899172 344899187
    0xd020a120305090c010e150408150601050406140a0c0629090108070504050a060321030507020c0604050409051204180e210304050a0c0f034b1e03 64
    0x250a180c1840b003401d10041898503101051403603414404542003400c1942c99a43d40c480854040c1c00c0d034541c8850b920711005403500d9100e402c20000d000500c000600030740c01103042c0c80c20790322550340b40b81d83d8030580161a01c0a034020403221081c815903a00c1c03140010040c1c002c268101107941041c1880b1603050360500c12228100142d248200800d00051140c05030001d4030008403281118041010703100d981400c00240616003011b019141200a828415130b0002c400b892505803030340c2d00300f0440d40c64030000c03a00c81d9008110203070b200108200800603850280c100103100e50080040c0d89164003841c64403481c5034015031000703180055009462900300e410384036520000c100100a484040d0b1443c1110416011844483c001e0500220115081c0502080424509075204400c41c000b90303160040032000480328030088840402544503103078104c040403989401c900402241c4050f03403425858009605881040348049030041c00300401c04601c1120400c5064017070f4030511014540c09050003003140 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 344901672 1250 344900422 344900453
    0x504210306030b15010c0c060e09071e0807021005010806061504080703081c022802010b10080a0b03010204090b090c030c09060f0705030a08060a050a0b040e180d020a 73
    0x51034a1802c101244915122035031255502c07002104500159005a0b8400c42d0f080b0301400e8645030703a90120308150405989203600c0e0084440c21b80d070b5034612400b02c41c04006480a20303c40c02c04002441036990260414075000720590041d103103410100c0d1010012114260f1101c0d0b40b5511202c184081410544200803e6203851030f0300520701400c1c814603ea940d502c51100911030304002800384c0342d0309111145c40c400201c1e201030966a031200802c1f00806094510142d0003546423280055240314014840c81d40c180310302611a0310707400d0404e1130648031140005d1004d5030080d181c0c0d0b20314980d40e40c2031000307001811000c100000c100707900400b4001c4035040140403502440e02041407080f00402c1c0c0d02a41d01801048030340b1560b400314898031803400d0040000c0144940f00126180300f0079a0080302d564400d0109484105083e56203400308000320600d0320130b51144003001c01084c070086d0014101030364000d800040040c41420318182c028079000b010841c03480160400e80c00c2c1d0703007041180485d85040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 344902922 1250 344901672 344901677
    0x1050c031611030a050c060a03090c0605090103050a05090a0209060102010e0a0b04060507180b0a170109090209090106051302090f06220801051501032309010c031b021519050421 78
    0x241c0c1080d42d54280d071006c50485a900c5850003280d46e00c074841c8250000e80105500050800300c80399580009003040c0c000d011124086814071000415110352440303054460b11182d0021300c161091a024800040f501515850441d5210380c0b101690341030030010041094400c1500604910740f0381071410031194064a48400c0103081d01700710070141580d001343d400f03607a8000442540c8014150051b10701e403007080f07075550180440e4030000a1405260b4001c1402034009c1e20165004c1c0c0c0c030041d00c142210454000c0c107501c1a0220b019002c10240d540c0640000c1c00c0250100d149882c0c504001000d5800c80c5000d904030011a01003681c1c882c560426401c01860114000e2250341000c1030503507010301d03141401d24101555802c0f0070794600000b0007880601c8101c02203074001820110f11590103405c240e1300c0c140c08a4140b280c1601082c02c58540e81b5620382d46540582407070342280c3c0940701000406400b0311180c013081100d18007854111310810340514030a20301144c3d0b030801d003111445603009007207840b0305 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 344904172 1250 344902922 344902933
    0xf0406030c1806080601180f0504020102030d0e031b012403021003020d4508040905070c1406011a130b03060d08390d03020901050c03161103 62
    0x88500395400c064a01080900454055022410000780310756800038806111351000081d21101100c681000387c6c840240c1480218902800c0500f81c0d00c2c107850081c0180c0c02085881d28686155005008440401c425245001698141c615000342040c0200e0070310b07552120014002da4007200011206604100c01040c050f156400180d2601d01e00039402052540015030420803a0082d80b10f91075842c2c80c50030400c6c00320207044400190a50010500d204910382844010718113403030500f1862516445050245080e0a142024020b001c01902010a200d4110340c600d0020301c80140c628045903010740281017540c54854105810072110508003842081000003182245e000201d000903600d1442e1865526100c1d00c0200b4680d244805000d004034602048a00301e00f8040c0190301030b107800d0008030840040581201207140d0811900900d481da1005009441c1c1c2406900a80540304050419a040c14815103546085034044020310301000300c2405d0000401040341803031a8186404c3c0d00900c0f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 344905422 1250 344904172 344904179
    0x12030f06150d0b04091b030308010902130b09030304030503280c0b310605040b060604120314040e01140102010501060203250507081507081b030402090402040603080c0c0f0406 77
    0x79107101e90405641020340302e89010000d07072641e4001e090000d80c0b0200c15400391454004124030341180d0b01084001404903000010b08240e02d000380d400c4008049451010b80345000d00c103000d10740c44502066014003040c0720000201d00288003402d41c400d0140030f128880c0c0e0034003a541c1d02c81140b8004041c180001c400701d88001c540c500115a0344a0a582076442404240c600d4642c4050988080170703920800200400701007041e590803941c0914411200003505c1c0d1500c1c001c10509005074010342c08034902c51858000401e10a0f8544c0020100202c90300f454140c903140c08501c1c404090708404c00010440082d1b800550342407051900414991003d1341c206280c1048120204440804201c07881c20800c20301824420180110310041c03d0460440c2e01c01401041111b841e184100c407010041009a00043c214400c00803050728000c5058541c90301d10f556560070400030135000f130020307600710341e56101c00301c009480d15004050020118004040d40300070304041189468813240c01d240180d04000d400c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 344906672 1250 344905422 344905459
    0x40b130b040e04080d1b0c030905030d0c0f1505010f031103011e0b04060b1303030908060f07120905070602010f0609090809040908070606030f0c0602030a0815060403020312030f06 79
    0x3d4010b54445010b40c0d4518490a5040240585086440c4c0080c640101c03a0140e5070000075140440f4403d84441a203e5174450401d40c441180e860303810041400440803030000340a204110a1141c0b24281d400da0388440840d0590458100360881020311510185c1071080c0304450300422105035088000344140b2800440c02070122070043c4410b04180e0b180c50803540d20b40e480d0703004007000d400907810b102c0d200c0a41d4401d80051841502c03094000c00e80d0950082029500821018411001c1070b40139405600c48000031541c5d00c4401040000159407141c0c0c1c000046c0081c4246802403019900102e203a4400300360386803c07910039502c0042114a8003007408000303500c61082d40c8055070300301c0300051000382c1800d001080b4030403c10010310240c90550b01004110310f5414140381103008900094400e51030700010380c1d80307101e4442178001045c1d40a0000b25405044205150550400313000c8900b895603c0c0d001c02d1414088000070001101c000c410448840d041402d002d501030000ca0b038106069201d081c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 344907922 1250 344906672 344906699
    0xf0203070e060901050c160512060106140307031103090a05060606090d0210020111131401030c02101e020c06091006050907080a2003060108060306090c060c0f03040b130b04 76
    0x145004800114980442e13a00441c10707030380125040000d41e2001e04c50440c010061030480d0180c144901720303120840e40346140005d030103410381e0043d4450700300081343c3c241c2c00100c50300010007000405880d054a5202006a4009180101c509a0081520740c1c51464000e0401340e00900140c0540b40a008400c51a5100091a0440c0b5015103201101401c10310b412405040503a55209a003100000c920002c1030300040b46004481c02e040c1c501c050036030790300c0044082e240c2d242d40650040c0c0c00460b00d00300302c0513240d1150701007501075100d0403e2003640c410b00c1416078211070b00e5418039411200410040c0d400c103012040d802c2e00744d2881084004d0422001484040c8060400c07010044903500182e54840750b54041c4101401c40355482203101c414800850065000301c84d218001007840300440c009003400110b171402071b00340c2e8019140243c550414445143c010706e62403d0588503200348498104420700041c1f0150118102d1642c2d03543c004080424080e42c541d0000440c000d04100402160898125 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 344909172 1250 344907922 344907947
    0xa090c0c0305031005030105090d030b0a030f02040b0d120905011107030803070f050c10330b09010c060e010e210d020a210204050103060e0c0304140a0b090a060f020307 74
    0x40c10b9880307407500800d480141c2215041190035619003000d000806d080014140303904505079400b03022004606051103440c0d070a6200060410031000300900c018505900400a1807002412035001a201c41c2c0b0340740c3d500704000010101040b5540010300282d640410b070031550019500050a099145580d1290588001071131403042040d0b40c43e800d00018855001c880c1c0c0c0034004001c82c0c0040300c80c3c9510170001c1546d51004d00000145180a14900c11104c0c545041e610240360412704071450048184010313400007040604010407011614009034040c40f504400718030b03a00001030b25000341c030750a618000ba280d40d181000040c8142a040e010960b204a81500303a10b07040268980d003c0c107500b41c0c0c1c000c070901a8030400012190a01d0010381650340070740104d81099a052004035681c1074540341030300c02960102c1ca070200410008001c6515060280310300844a011551032600300c0d00d50b804509007d451000d100c0c0c02c58949042406414001c2c0c80340025440c1c0210b240d400c100c80c010b49006030000c1e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 344910422 1250 344909172 344909177
    0x1a03030703080403090803031e0f070c03050c03090a0306050906090a1509020a05040203190c0302070206091e12030406020c010e030c10020f191b0e0406020c03130303020307020a090c0c03 82
    0x2d000508051042c4107110080540c0c0307003101c2e240d0074544101560404c5640c0385d9440c8642d580c002807021f1000003041c0c0d002d100380f616016002941a00c04503010b0703110b0f00820701d00d0701c410030803241e0701d856502d00c032001180541000a203c0c2003201d40c1500300302c1c02400b0303904154080308412002c15a005540d80c140c050301480001c2000d168404101c00072401d60013950710034030200401542a041104d040d002100101003000180c0f041d400030b4003240565031019402a1007404070492600b040d481c5120710b41e01120012803000c0c4403000103a8442541955400c00da0404a81002183d40401c038640c00c1c0d12003401c06040d540101e0000c0b941d9605075000c518454041c50410b011074a009010410074118443e040e1101c001c610789038945106021001258410b4054900400502094540700f0541d07076400000301050b2101c0e11900d010303400c035484404a03400104a20405809903240c2000110300c20340255445ea0000e00402420805a0b07010070700035406c0040340c420103a40000000a01903050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 344911672 1250 344910422 344910437
    0x1b150f1b0709050f04030807051e0d090602131d1b0d24050a0b0c06060112020f1201030b130201050d0e0c03070e010e01090b010806010c0f05060a0b041a03030703 71
    0xc0c14014902100d6600000810345400140142050340181092185010b51100250f6803240076044805110b90300a1070816000030303c17501040720a0f0001840b06611000c1c000c0360414290301c500c0b040380e0044180c4001720040d40c00030403080308030045040c2c07121646022690710307103003460301d1103180204400c2c0c0b0802110f0028100d90b0b1075030640d012198841d00c0c80780201815091041c0a803618100e0b00a9605c070b4100300400180031220041144c200c9482400503003480c5d19010019038444080d20f452110840d001d22800704458401d82c0500944500303242c1d01400c55140d03082100640c0c1d00074100300070b08207080c40f0360340250b60030504030380b400c043c41c80d4001001111100701a040c01c0300c1c034007142d606024003100004d0380f1090f640610706a940c540110b07005640d0380c0c080072003110844007145010600d0080042e0196004000c1844003500610010f003001c4d0107951083c0c2441c408548030820346903200d07003200321820070780f0032300c4075560074002074800b01200200001c2c0c2d42e000f103820040c1041042c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 344912922 1250 344911672 344911717
    0x903070201232b1107080d0914061018021201030305090a170708010c020706021203061512070912030504030213020913051f05012f1b150f 61
    0x2d41c400c803694041e0081c040c0303140340d5020700c0407182c43c400414545a80d80c02c0a100880080091040710b100343da00021680c5422155020140900407406050740c5829041640002d489024049d042c803402d904c8240b1aa014181140b03a10b103246d09003c28902e0394810b100b41181c50344100c03440b40c10f4035050f0620780d484200d404000340e01203001d900300411100b148030900900100000d034510a03108010000e100c40b0420000c101d958081034458140140d011303a042c0038540c149500119081007014100b40b100038403c0c03070392500b25400b6080b0f90230120103400810003030b03d6002500c207000d000c10010500394015161402021800380d800040c1c499146812205106501070b81101d000c0c3c480680f8001003403191006400052400311082c101f03204808010551101c1074010310016105c0c140c482c4070064002e0100f2105203070f40e03092400d28840311081c1e00350f0710350b034100104c28000c48401c2146078200707040024001d0030304809a075003115a00522022185c81d1a8206444e41d091010b0f51132000000d8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 344914172 1250 344912922 344912987
    0x1a0304120315050409030306150e0907030b19081c0311041406071a1005030102070b010e0406200a170c070311150403030504020f0a081b12120a080903070201 69
    0x202c9921055000c0d1419208604043e05900013204480e224600a2039407444010141d590700900f0b03c116901010500c000f56005010b50b10100300b4031005001c5841c3d0100d10445034003c1840c3d50000f03d401c3e440200b800a00a100c0010504141002d18040c40000056252290310340078074050b14a0982038007829210b691540415611150341240b011920707180814501e03070003c08150744904170b00300868008100c5060500803500901d6000d079250320540c1c81d100d80811103407800741084440f50303151b071038031428500c0c4590000c01107007541303400030f030303200c100540280011407003003083c1904811150030003600c0c8102100365014650507003801000714200251560504901051040401002a081c8018903905a0001d44210710944001c0c40c0030150404000302c4085600c07030f2070b4096100307a136403010342800d4605140700360801401049625240d1809241450308000c0390220f288001300f40100119400302c0d07102d07004411740c0e0156141a8507900000d020f85103250044032265411800d4404021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 344915422 1250 344914172 344914211
    0x603090f02060301060806120f0a0308070c05060703050924010b1b03030903040302040c02011a120c0d1104060509070c0206070c050325081203040f080702030d03061a03041203 77
    0x6500400440c0e813580c60b0b17030006e0300481c1c1c03c0d64058001c0c5100c085400d00c410700010401d46186080004128400160f40d0072030b11860300030060f0042054085408000030750404c04c1c01d0281005803804a030b0b502d01111032915105444c55452041e100d20300c0344201030001002014107441000c122684d590b41e09800980b903406100600e14021b02c0000100011200c0100160003543d1003200d0a010721072030b55504070709a40c81e4401c0c00141100c00a0100000d00e060704550340b8904c04801501c0405045400040407003000311400c1e5000500342641c4010751034140308440141c00101c6600c645401c3c0030341c0c002c00000b92102c00030300034000082c8220501c40500c0c3ca40d002000e00601b207900c0328082c10b00011052040a10b404a0072640c8000481e50700b4012905a107000c081d614a6800d641c0e4a8903500a030501c214401d41d84c1030310070408070380962414000c500348807400c0c0e1400325049241000b60144502002c441107980c05041c8180800a0320b1b804004c650001e080c41d000c07810001362184641d210 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 344916672 1250 344915422 344915453
    0x307020901060207051924020f010c020a0c09050c0f070f0b0115080c270a050402030c04080c10200f07060207030b090c010c1b030c0b0d0c0e030601060309 68
    0x1040c10000520301c3e50010306101920750070780320f404805a003210b80004640321401080c40411101c0a00c1e04440395215520551004900c1140d00740c851000d203e50840301d5020f0201c005800c0082d85005010105c05114001e00f08101d08002c645025030101c0114042e03210200100a40025210140601c1d191345190098002281c042c403543c1d22000c1c0c03120340d24001c0c81400440c1030300300041d6040354041c0580c2c0c1e0020540e9280555a01c05002c0318401020720805280d1107030b0000c00126060319244095032080d441321041d00e96843c10240428034126100e50068030032a402021105801d0f400b000e0310b80e06a4100d87d0355a034504185215034140b030706110314864107101b200d100066940e03000450701300700c07030051000f40d5540c0c0360140d9254803416081225404034408040180014400792040c0010103617805a48003491b48036520a44120000d81c0440d9540d100400c0c0d09e5040503007842403808040b079904100c0096468107000c280c0f5044144203400074103941d401e2242c28444240000803d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 344917922 1250 344916672 344916679
    0xc0307021e1504030b0708040b16020f150105121b041e09050d030b04060e0c0307180f06090e0f011a090d1208070206040312200d050403080705090d060905030702 71
    0x540c48000c5a0307450b90b00300e4801a240a0320300000700700c0c02c5020389501d501036900710b02114602d82c0c54a2800b40200b60860240c8114440c507100541c0c02601417001102e42462600f070828035514000410210507000c0e40c441c0c10640190905561005d00828084817181040c0d501240c0050040c020b0380301c1091065140039024140001c0104201000c40c01c21359074500b50724100003031040c4034244012250700c1c0c0542460075400b0004141c3c102303107450155900c50301600d03102c0c1c3c038001001d04c104a400c0303407503008080e90f401072035003440200d410a90f0b0300050225604940b84a1515020f09100c0b05010311400082901e41141840c400a60004079902e558002d01004c44d2070005192074100c000c1401052400201c4500c04038065500c04640e10b0700564040da1540300c0c402050402600502e82500004450020480110030b60102d410207001a4142c182001545141070708001c2c0040704000c107464100036007004210700c51380d00c51503100d980380d400030b00009a0100c50302e0700c40d107517108103c40a0350 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 344919172 1250 344917922 344917939
    0x15071803060c030b04050c04060504050603090304030c1d0a0e030313031412090c03010e0a060507030912030914030903070b0f09180103030306140907230d0b01030608030c0307021e 79
    0x81c0143c054100703003400a8107603010000d0f03695410229100d40990300030400000c1e41000b080003246000005980c0107a43c0c0d40980b0701d0140e90b56584103c0c801d550740b06850b400130000041201c120f40b200c525511424203c00be00150116491107510303480010f0a44071303c81004e00107030040c544156000d010101c0d030100050b035030b400741031101540008100d03a00c00c002c3c8518003404100b41418003400d02004031903802420100c00a9881b00c0c003410700100345004156807418031b600454070000c80b41c8008405034800145445403400d00c0300d08145003410000f9a50700030850001181c074006000002c90fa581441c0940b10004038810b445503205403002e550b44040030307207094107203c0b02c03000b07a590484c1e209840410440b90350310b0b980e141001103031a01c507a02c6001500040c941d2070040c20310241e65185208a84403074141c030b0304c0b190900d81108e40304800950344c442c21140b581d609485804054240c01700294100ba80c0c0304880755682c41002c100a010b500c400307040340c061700301c40078120400079401000d450 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 344920422 1250 344919172 344919191
    0x5041205070515071d10081801021207030207060b090f06010f020309030307060b190b0909090309040507030b041805060103081c0609090b0c0c060103030318050105130c081507180306 80
    0x14400d880da8220f42c15172401e1007001108030700d041d140b1000d04d03c0c000c0d02c0c1e101e800d0740d91040204510062614603c819502007240d40401c8000c2400a84101c41c542c03030050b2240c0302d5040170350840d5541c0700540d0154002d0f405003c00342195003101540302c1800d103452100441c1e0038400f02e040d406074020340c903014300c0003060341002c11501e500030300b804000030f4440c2c411107c0244041d1410409500c1403c0032281d0800045c42170303050804000380e000b16140112894288031310041403c5910840350107001039900c03a0581100e25142c0981d22809188000b4240b200c3e000d52034a944550701803100824030840000c0040c0300422070790000d1a0754401100810030f6030703911900c1c00c01038041d40c1012100721240c2c00000300c1942d00a030070b842142c0034140c021718140e801c5035020b0b002400c0e010b510b198840d5242c0e031000002882406000d100d0801d1a400444444c05807414a0492030580c00100a40e000100020f00b015000c3c1c6450707138030102600e0085680c44904100d914a00040c0e00b014080c030f8140b4903243c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 344921672 1250 344920422 344920427
    0x3100c030f05011d0702070e070f050403050607110d020a1a04020a0308030a1a06070f02120309060d020702091503031905070212010507080604020c03040b071e0b0108060a0504120507051507 83
    0x140f0020544600d00c00b101e603217010040b40c40f112503009103140c4224001c04501018030400d41c029840d007540c20500d1406483c0d0321540d15040f4102d07040c03c0000c92142a4144510040c05034942c0320086000130030402e402542da0031410a00103903079444070706074200003805554524000750001e43e0001900b9550b41440ca8601c005040c85a00364016044280e5001c034013403d1a00844803070640100c1d80040b0100d044d0b00b08066030b10180c480041e144800c0c88030310040d50b500b000802e8000078403940141d42c1c6109105110b00c03280001c110000f003594141c101c5040c1e480210480769010b2410304861020b900102c3c0582e614010510f019400410b140c0e500c1e500120158841400f946c0c1546620009948010800007270340b14216040e80340ba04103010411441c8600d0380645245846841d956050140610891440003140c041c00d6034010301080040080d25000c0c0030003900410300c0002404217241c5070b101e82c00d01c1803203113002204118002840c40280a01400200d061002c032410a40075030a101400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 344922922 1250 344921672 344921699
    0x60f040b0c15040305031f17030409050c07110d05010f051602060f010b04150e1c0c0b0301030203061605090d0b06010908011a10050408030a1809090203100c030f0501 73
    0x20100706100c1c6140105a08184032106442594503994140c6160b51b4080d050700000e1159002549844110f60041070401c09012002181e04c203540041d501d86141110720810345402070100220034808200f40000b0401101c40902c1d0301d00705903500005030859161003030040500c1040c0071121454281800700c0b403801c1c50030103030084203103600300d841030303141c1c80702e00517088000b0b21900440c040d04000c05c02107000001903421644019007880041d048000c8049000148c0105a01e00d000c601c0601000c20020424182c00c050100425454115819903011070703901e44015003c0d2600402c191040903250340300304115680040042c103000721030080c0745810020001e054401d5070204580a00100d00315005104184514550000c80802d4074103070780a04c203d2840501681003000420440464a00c90400c02003001d000da07503030b8002c1c00c4810407c5101200580f038116185135820b280d00d03800960344c0024544d10360002441e0025254002c0c4505a00034015001032078001c6041500001d030035802e10b0780c0c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 344924172 1250 344922922 344922937
    0x40e030f030123040516080619090e010e030406090605160f050105070e03011e1128030b0105070302060703051f030b04050c0405060307061206170609100209010203070b06060f040b 79
    0x8903100c074007a60204000c113641c0c04840d02208280f81c0410151107d120f451a550403203805880c00e50900303071050201000d115039402c0f40200e0740d241d00c464a4040f0b002d00ca0394000c0d01c013800280d410306003010b50041035013546104007402c209020490403070fa5200b03552401d07111540804000c5000d2124600a4083c0000b101c02c0004504d0324181d100460a040c013940a2101244407680300c500759a4105000811a14540910185040c846036145006e40c49101400c020070100c8001c1400c00324400400f0340c0c2ea400071040c1049018010381000036000a0b019800c15060306000c1038551703500e50000310041c0e03040c085d055080401803001090200044540d4013441c010070903128002001c106100907101305641c0a41c00d58002d07941082020300c0361068172910302d0ac911001c00c1440e940e106802020580c0f00156950340c1114091020420040110400c000885038003903040c0f1542c200003035100d004240001e0324680c031160025004c2c0d50350104031070455800d20343e000d8071540c07600e03600481e0341c00200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 344925422 1250 344924172 344924219
    0x150f12021509060f0304140a05061006020307080403140a121101051f030f03120f0b01111507030213080307050309011106011802090303090a0e160806090402040e030f0301 75
    0x8290720510391500c001c0382c119800c05801d0a203820700d0f105030602d290380010030a450144251010000b414002d0103840310480c00741c00103000f58180b07001040b8603611036a08c0201598010804000080d4010080e24212a0040c1488540c040140d17107007400c0045891000349802d4000f4140d10380d50f070f0007000015413802032500030840e84d61095000405141d04422542014200d5101000002d081030324002c4014801c0c178103003420314000c9100e40f0940b07210140364402175407607640c5207420b035030710240400040d8a44070090804540c80c4003040c1da400e102610050400d600020091007125003807520000405d28901146d41d2980d1074284142c59401040d0610b0000c0c001d0b51808000c0304000503014180da90344130460040f55190f0314500000d502001003a6050b020610035040c40303613208031310007000300900d9090746074500d04549201c0d4009030b80c1d800c0000748101c08044c0059030f01c50000e1198401d6050b100000e00480100c095840c6000d03001c0c0d0820980c1001001040f2188610080034207881c540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 344926672 1250 344925422 344925439
    0xc08090423071101150306150939080106141c050109060b040b030721051005030d1106220b01060c0303110306060702240f07120c0203060703150f1202 66
    0x1404a03400e07500117196a8140c2605c40380c0500204141e9442040301301c45403188148036946c0e440070307034042e1a44841f416004007000000c00c4003040c0c1040c407c0b251134480001180c0300c4040070001420034078042c0105810449125402078420031600115481c400350450101c1d0b00b804800c8503400030300803d0041112150800d00c0001b400200782064800340c404112002d401c6985d01d102c105e030040e1351148886090400400302880200c454400d480c01013101c1300d01d014215003010181031400220541c00707030800628000c42201e40201080064011071000b03a03e00d244c4000c80b80c1c48201000c9a00c008c2c00a060390400000d0054002c4201c070f00040c070030b413402e01010201e104081002d000071130b49144c0041c0100400c4005142c110003100f602014064860b01c5041000340000d0150010100d03c0b1041000085c3e407428031101d0301000c1c03004000c034642a01c580e00260701007a1690400742100d0207068842001c43c844400006507100502080010140016039405202d03413001c01c000d000780d0052941 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 344927922 1250 344926672 344926697
    0xb030106050d05030706020306190e0402030c01050c100905030c0d090312080f0c0901170903090a05030601051c0302010902042310060806010f09350109030c0809042307 74
    0x4090903031102e50004091410001540c031104081d5000405161b0300540c507160364100345550403d850040c0c141c94503144568a400e1061510344801c0d402d4850522806001920315000006112060f0000c54031001c1a00d070124a0200c4c954018061450034902403035000302d1005030701c04050404c5030300070300907000120018071003524400416100700024062100008401105400c014001c81b541031500f041400b903a0358040508841c1900e0394000380e0000520300c400c52901ca114076019250407400b905155141ca4001400e07500c0c0d401f00ea1b81543c0301d0b981c440d030a05000b035000c078803030540280061000740e00180c43e81c0a102c144141c07070706014000306d002c580c3c004003072280714043d0340d03171603c4641300f40c0c42d030000540325408011586400c00c00041c002081038150f03a05c15024071040d807590135a802d240c9540c00140000c2e26841801c2c4c981c98410614040f075401155442c4440d00300c011640e444142501150140c1800ea0788500b550381da80c030280c45540c0c2980b80e010700c1501c3c61742c1c404420f640e4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 344929172 1250 344927922 344927929
    0x90503030714032a0909010f0501020c01050f090d0311010609090b070c020d1b03081b0c0102240402040b0603090604050709091a07030b10020705191d0403020f100b03010605 76
    0x81a66261400c0036000108200f40e01000c202001d40100d5490040c20400c40e05c0c00a140400241c0000c145294000d008009650b01040700344441d15090a0040c00c10481c02c281c0001e50007100307200d0340300e52a00c0009405041c0150103080d1241c400c47d009025240d00c86503454003501900d28100c802240582c00a025240b144102541d10b50707000341600000c85054450301215a00e000c2c3c0200041014080080041d1008008142c42030030f1000304103401250b40c07040d40c10139280302c1c040d90640d000b81a080b407110070210300c0d05803060303410112003005440c1c90020a00078294040f5a41e00100c0c0007042c080c0c806e0380000d030584224801c008595500b6218003041c025100a108001d00e14040b4400c803140400540301c0c5c15900260900e40001c0e02c102c8200004c203180c0d0651075000c0903030007608007445a8100322a001e10448000d01200600510740504507034000b0140c034041081c003140718040ad040620a20100b01980c20020071642c250f50055412030081c03103642c043c648213600e00b01c8002217508 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 344930422 1250 344929172 344929177
    0x3110a0506161e050601170a0302060106050c190602090916050406080612070f030c090c140702011101020d0e010e0705090606160f031106070311040b07020f04090503030714 76
    0x300040e01050810725940b600c0004090b20540445100c40b4801845030044200024410240e0041c0c000741031a5160040c5c116030207030741410010365500503100c4003000c00d8000034800c2c115007035454155941c4905040447c00c0c044400041d21800031110700c11024421144c0152548117000c50789040d05403501c2c0740d2040310601554954011030700600c0200422401103148560054001c3d01d49003020000700015820443c550300140100a035080041c41807291840044015101e02c003020405100c011502401e145e07540c00820900b40c40000b140340441e4400c00e85007094855a800039501c1ea4110301a03180640081c1c1409445d80d840c102080380310500000700c1500300e51b4080d041c004640c41c1c0c038081c4500c0368014200712803e088580360700b03400115803414a0005074000d581e00c00c4100419401c150030404042d02e9681014284080e1421303180c14a011a030031140500c0800b550340300c952010903003a0782e03840365056209213084440000c1c02004001180b2900c02c0b6940c0d0000304080450329515030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 344931672 1250 344930422 344930429
    0x9030a0c180e0601120c05030609060f0903090d0b0601050705010507030e0c040605060703030506120d0c03030c080403090b031f08030d2d0b010903080c0106083009061903050103110a 80
    0x540c40440100242038801107a5004039020301911600d15880340c0108c1c0c42c1100517103230640d02e0b9001030100040715501c3c8411a404c0402000514601442100041c65504420320041c1c102c070643c00c08980541e01620071902c1c4564400c00a009920301210054020030a80f1180c07401c074041e614074644140307010302c038540035588014000c504108507514100c1c01000020704542d000a600c04000803100303000c00c508842e0069a60301d0011854490ad00201038030180107140d0f090052071802e000c00260440d005000b41d612032001552a940d42105015102e600c2640100d5001d00d10007010941407000700c020040380034915018441c00d0384000c80c07505034200400054008010040000c40d019480c1d0b0420000305030140350582c546a20303901e4004031944040c010341483d0303540c2d21080281001c00d110b9031000f42d0414800c200f08040303111545109050030341d84e50403858000960001c2d140d480790107848404031380c080112040214544054000c0c082130206071405c80340b110401e0300340c2c030704956040240d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 344932922 1250 344931672 344931701
    0x2030f07030c14040e03070b0403120207020105030f04030915170702070b071707020405190b100e061303080a0f02061f060c0302010f020d0204030209010801020306030a03080c09030a0c18 82
    0x40b0745080a615102507142d6045540b154940c9110400004100090800e10380900c0310b898003400c00b49005003520f40070ba62a0350f2014018482c10b0003507a00030060340c0e40003089000f4105282d403586010dd4030446681c00208070040707140e01950b20700d58080d9018150560b20b6084c80d0481c0c49050f420380ea01c010902c1000c000c01307010800100080e034815040f00803201c03c614114106075240d030004007681c40c21251090b18100c10802e50f800340c022400342980044041c3d48000241d604104018900c00540300c09502600c00000d50000d00260790751808021500400d00c544c989200c4480244500141440f0320014418103001c200001d0b600d220301c2030b80f00c4036407040d410350b9490506c05840c90a007420741901555666580005d0b50a010700082940030f003010740040ea00c03415481004109601a004000786a01c107008204483d100092101142030305403c0c4601e640d92009415131961045020060701405524101410089048000b0080d125002260250301a0401d420b00846403401030f03503100c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 344934172 1250 344932922 344932943
    0x15180201110f011109010e041109040b0a0e0c0901091a03040204050c0d090c0519140f0334060f09060f0e031c08010b040308091e0d050a02030f0703 65
    0x6600801c110301c52080004280c50a242540e49110b0844100460043c0d960b5000508040c4540e80260801110748040f1002c00503501c085000354054092400002e005990740c115180c482e9641807800c0d40141030304000c40400d444c00307060103070341358000c0c0d0b1a55010410b0110003050070720003844081c0485985404281c02c564854080101510020740307090181102000114810b411500a10411030b00a01200740d00c80e1038141801064501c10400c0f0044200584085c400340700008407031603051200303e8511445180100000b03013440e1a508490002d46040000a13418400c21007115011005004a5069103a0b85034400e0304c0c200d0328985803100190340c5000c1404018010f00507404644542d00d80301018003903480100e0310703099010048504084036908940645030388060340d0341c00742013035100080c00d240c41d554800706e4901929400c10704c104901440c005602d4903d034010b44c162030300188401c0d40419182807403502c80821481c240c0c081d005078550b44104017000039000c01102c0c0c1c002c88105 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 344935422 1250 344934172 344934221
    0x60506030f040308040609021c140106050306041b05091f060509061902072105060108030913051b0f0a02060906132306040b012309010b180402040603020715 69
    0x1130719500000c4c0105d071150354818541d03001d611030904500c0c00092a54102d9514607040c00c2115034000ca150441c40b96070704000c01400b99403408540076400079444903451400b02d500401112528461760040b50300701c6080420404813480c56402107080740305244a00564a4858070112898890000995001310b020449000f0103051801c5840000380f2601c15034848036200c43c104400c0c01c01d41c140c1110130b00c944010038414400103000e0320380101030301001507140401050202e22098019440071021a07502e80014000c007850340d000c0c5400402c0d81c080550b4800e509001d803204c035080905404010701c207640025903c07010018819019240c101c8000711601c07180d0341d8080b90b0258040c4101d10600300c40180041c80c1100304041e45c01248a44440d80e200c3d030400a001070010023503e4015040c20000d40048001d49458007018195913000c1c2c0d085581e4050807030302c0c002c846024801503801a200003400240e01d64141c2c060000c0902c43e4007003410181100f40a44180c40700801d0b1400c2000310712020b01d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 344936672 1250 344935422 344935427
    0xc041a0918090a0b011d01050a0509010308070804080d0507060e1506061309090b0106113016080301050406090b1f120e07030b0606030f0609181f060506030f0403 71
    0x1154002c1900c8210303000b40020307540300001c2c80070a9108500c0c0340002c25010b181c078a201c1c80003e025150559488140914180000e803158006100160410f940041c4103410302440108403409003c140b070450703411200b040c40c0140164050082503507101e10f010507280324a107000c02e10300c05a41e62802c500c5a261240b60401c50301c0da00580d091304c0814103211000488103550b0003501911030050b0310a40c01d9604d070500c00391030245101c2c1015800d030000062140b00000c0d00e4010300e441c00d00300300c0d107424860700f40d01510f441c1d00c2061078900501494010031801c0180c104000c41c16502d06490030b12aa41c0d0300c00c070340d0080d1407000d002d4076401400060300c990200d5001e00c4c00302890314645011100b440110300210111244401040c0040c0c1182c201401840301401d50385802c00d20a4840c0ca1840c0380c0400d540301500e5001c3c08a901c101c3c2040041515004001103813402c88100e0000d903585071a404801d011201e000c110121002c500305400042c1d689024400d4034440d54883c603c48415558a5804 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 344937922 1250 344936672 344936719
    0x304090e030333030703080c0f0a0302100c170f09190302100203060402040e010b0a0806010e0f0910090c0306080706020a0308130609060f0e010b0f0307060806060f030c041a09 77
    0x800c03c40d440c1c041400105590400074140118061421181da6891a80a481c2080d42580c160101c41d440001d1280003c0d60000d8a00360801210b1000a40400d100300c00302d4149100a10401e401c1e08410207000302d4081952000d8000e0010034115a46002e12a403004542c481c00308001e80942c200c544a413001c42034603002554003500c000c20051900d9215008102d500000fa0400003c00c000400c0d4141103030b03000304a5541184003403c14014519001000030a407420100f4842c0c0140d1250021072502c401e0141c070381c800742101c10014000c591030441c00070010701e585c1c443c04059202d8120700240140c00400c00c0081550541d0314040d440c0d0712294900600d1800d15800c80c0c120360303264914404a00584111081c4441d030b00030119009400c01a50350944e58085d9805100e020311048040c01a0b500003140c200312415410041c4050355a031001900c1c5018000c090485400000204401c14081c48000e20a44401d113407282200030200c40901828050300e019141c001c0c90680c040c2c051500a0f652 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 344939172 1250 344937922 344937991
    0x30e0d0c05010605100c050606040603080f070606090203090a030201051f23060711030d032708070b0721060b18130e0601140909060403141204050304090e0303 70
    0x4540c0540d99000b08036185d10020700350300020141030500d802c000d01801940d8004104035000e02c101400c5880c0c03405688540c4800380000000080d412081003091341000c4010710140401310740328900101d180340c5800202ca4200c005510301000903880c19110911002c00c0340328187d81e0042c0c103051101c2030204c10389480001c1c00c0380340d2010310321040da91020000c1034035078455601080c49005110a01d45003180707401c584000d144c14204180c043c441031074020446d00303032910240002e45110b400d14030240e1060a0000d0054440e25040041c001d8000704900d2a4403032040d03c21440003212010392084131183e000b03490381d07060304201425200c0307503034280d038144d142c0c0081c1a135294120029409045980c6403507502440c2c0c02040c01002140c003c480300a24030417007078500f202d40786444102c10341ca5a6004000500f4011296442015540d00d171080d201c0303a400040469403241001c0c188160740b90401d214a140c0c07503046c026421400c0c10701000f81da000300c00b451000c0c40e019010040c0c1c003d08800c01c40703 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 344940422 1250 344939172 344939183
    0x105070512040906090e0a02031203060103090f0807050708060f060910050d14010c0507020a0504020d0e060f0910020a0c0b040836010203030403120b06131502010b01030e0d0c 77
    0xd0740003251566240100010020710300001003581c0b40c00807610540d40c0d00403c11a0580001241d0700141e01d001c00c2c0300c10300c03520301c900050b52652000c0c0140c0c005c211040010307116184005640c4100807000340140352550090f0210307401195110822603840c5011245208002030f0304000c180d05052119409401906403801000019100c0703010900e0b002d1020030a541d25400340001401c240f000788501110305406203019460500c0039008650609014814240600d03070010b508289011203501c000c00b40810390b0151841810404800301c0c2a01d402e0f140d5810ba4000c8000c6061900075a20883c2c901c8074180e00c5025840b0303125103500c80031a0004001b640c860034104050198055100112030007820341200d1105100d1000540c514400b000707000050665104009000101c4c3e0041a0352074070104e40100803a005410307101256680c01403c2c82084407000007030011407c55501081c480d0a40d01c1503000b00302d050002001182a10b603440518200d80d0804861003510300c0c400c071447d15551f030055 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 344941672 1250 344940422 344940433
    0x902010201020927010b0a21060305010e1005011d071b0b0a0c080a020f09060f0702060d020702090a0c120b040e0f0a1b0e180c13020d0c031a01050705 66
    0x3c0d004038410180301c0781003070400400b01c1e140e8a10741e8542015035015110f2401c4040c200341c125180907140000c0c040000e4542107260076066011602c642160016690060090100e9114000b40c61b030760702e00d4015031a160a08200002c51510006c0411220003106504100c03490b48552800340d902029001d00d00714080c0d504ca41d20400300c2e2080c140103024025104c800105120790390401000014040c0c0100f0300c80d401000102103260718001924510350040324820746c0d5034428103a0810303511038407000a4000707102240504c00685140e000d000041c0c000c1e19450502d5031040c02460844028006c5107012500c0100c0d084d2100311107920900b14036001800c006120303400240c150b85444a212088000e541c0035600520811400818551640b007200d01c161081c541848250320b04d10b0002000d44210314842200c085058504000c410006000940384040c0c4030020001c0001a520a22143e00910305018503844003901c0391051080c100e00748483d8940c40410440115501e51040e10281c40303a01c100c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 344942922 1250 344941672 344941687
    0xa020d0e010215101701050915090307060c0801090b033903060103080d0c02060709060c08040312020a111e06090307150503070f0c02060904090c080706050c0105090d12090201020102 80
    0x25141040e0080201030f081440c6517182205800003100c00c03001150841c0d0504080c0640b1250004031083c280d02c000e03403407003403aa41d04040c2525501400102030180e9080c500c90a4441c3d8204e400310381070703c00d840d01c02d0020820380028503030355005a9203030800c080d49003003511244401401b00182040904034649a031101d1060009207130000c2a002030701c03804030000d13034000003520701d10611141e10481e002404031480c11060141000400344a440103100083c25541e00b00703c4c04400702e40145601010700f034144c0c0404030f0003d41e02c40c2a2842146c400649240e08201803600b01182400601900c0742c04178a050001c091098035003000341070a41500c98000003007078030b80303052148200d041500c1d940e1544034034042e4001030180030480703200c105000580140038050303113400341240e8a0040c2541c000c100c3c40c1c0340d4600704420301d203503902142c45401180e80210b040780e8041e008020015448009203e42d40b600451035440f4010003907180003285030115807400c1031055801203a9110300500005003007642 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 344944172 1250 344942922 344942953
    0x40506040b0a200309071d040b090a0803041a09030c07140a0b0301120b060a050a031101090801061206110a0801060c0c03080a050405131e0f180c0e0c0a020d0e0102 72
    0x1038000c6006000f040100c2007051000040101600400400c44102c0c14441d54140721038180c07801400c0500070944100005055a0003000000184d030341c0140560390740c0c0740c03904120100020bc1c509040003418108040b4041c081c000040e1550040c0b9400602034003454010309040586500e01e04a070003994910000501c001140051802081c108101044c2c42010741b41140c1d1100d00108000d02c0391412030018419521464140b10540340d00003200a49038914400503603a0050a5102666540c280880030400d00d44401501c20b81501c5504c05106200400358201c007a4014011880d000444410040080314859042d202101d4082c0c45658072a9890382c4540000d40d006e80d00c03e0000c140000b40421503402d021100210001d08030400300803510038652000e80040203092030702c50b400d031204d2180b110149540d104400c0b180d0241d07540c3d40c104006103484052092240705251003c035400000400f42080c0c007048800300103560b809464442d200000c00e0f9400c0042188490440c810b802c4d20b0105110f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 344945422 1250 344944172 344944211
    0x30d022d070b09090106180605070809040f021804050105092710060314030c100519090b070f08010602060a090804150309060b06090607120c0506070807080f040506040b0a 75
    0xc5107110300d5980c2c40c0410203000e8569010b1380048100071070201f410b10f0414880c0b2100055860034a00303150f54544034140820940a0395500d254010b20744514100b0207a030980c010162903c4c040c48040c0c3c3c00b401d4508120459109101d8980c0003058500028105c5444601104126035100303070a0341040300424956103009220b0100306141a0345180034014400703002c1d80000140c02d400b00551611540c00980741d280d02c408081003801d10b8503080411501e603855004e050200c3d803591020481d0001d117050440e5060410f540440102d080842001d0005100c0c141c11416907803250024212901e0324140c5800401403a40d00b614007440c05e110118080d5030303001ca491100121503401040015a03405c03c4c9007180c43e003504940c4604401c100201e4079403151001d80d8030003504035028012021091005891415182c00e00074054024a0100500181c00c200058000c1445a0782c00106035102c1d011144c4ea0344003554050069400a00040c00145915400c19803013404010081000b40c140e1059030001c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 344946672 1250 344945422 344945429
    0xd05030714061b03071b02131425020307030e06040314060901050f060a0603020c071511010c080f0a020d0e16030b0c13030803040314040b030a0506030d022d07 70
    0x1c0e040300b0280910429075140401c20030f0951800035156003001c20029088801c81c01c2d1a44007500520319000075551080300178055461060800d0200440c408050444840e0860700381c0350702c0710038403074040d201d0040a000c0070f040c00b202d4006600d00007e81e01c083e21300c002c034609950703808001044084005509190320340503c85002006240c00d0402000003425154010055910142500200200baa981000c1031045510301c0c200180c0d41d081400c0a1401c00e8030907081a07a1b050001c1821801c0603a04c1907580300c51541d090000c0100700d05640b012101224141e03030303134441c8141d001e004c2031940c620b580c0201070038002410000707040e042c03120030681442460f02e940980411128030401c18411120700582e4440d0100f98414a03101d01554030210251043c00060108503001c0005400c05d40144150307511103003a02d001a4956603601010a001d40c01151801180b90a240114220741000070711050801c042c1d8000d0136420f540c040b401c0c4100600541b8000390094400019680c3c10014401000074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 344947922 1250 344946672 344946713
    0xf0c090b1c0c031b030504030f0f0908030a0e030d0e061b0a060c030e01060e0103170c160306020901030b030316110a03020405090105010306150e1906030501021207090918020d050307 80
    0x2e0a400e03104070462035901e2131a48050600388000c01000030b82c005010600c1c0c4441e803c00c400040e42002d0101c81002182d00001c4480c07200045042d181074024503002181c02c81201120100c0070007010480c0c80303a09103141c0c20341200051000100800301d4001c88143c0d101e02d0011602c02000031744030030b42511200c8008a0100e03541c0c4400c06c0d11280280210001340ca404903007003009501d550341d800900449072525041440000c03940a52816080c800c2c000140c848012a4610300c0d00e0b130400200a5000a00060110386816440340980c1000310940e1404071032114051031a0b04c4544516a403a40280c002c603a00c581c0040002c001651544909801190558000140c0750306520b0301c40300300c80c041e1a20b89401c941440d000c00020010600056004105503004c0d032080900c40300e0100604070941008260754004a2580b840400c0b00000302c1c41071815179619646a1394030700383d040c00c81c0c0d10001c000001071000c0c400b030700150a0080700300360300398401c0007120b180c0724030f0782c940114913001903140c20007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 344949172 1250 344947922 344947931
    0x610171902070c030b090102040b04170c0306040c08010507090503100f0b03010207030801030b0603010b06221809060b0108013b0c03091b0609010c020d080f09040f0c090b1c0c03 78
    0x3c0c005c95286242d40440c1c904000c5251600306410034882d400345210703414400b142c1d641c000c404190140400340c244c0902900321179841c10103103445017422146001d0030754a586820006903a4030302c5640e05608644000e0080c000368410b00340003102a02400318100d0b0856101c050410590b1400d10080c41d000313010ba40c40c60510b50461030710b030600050240c88144280e0505010490540e00d80044a81600d1002c0403003100c4124000c00c0400f00c0c1e25544200d820f04a843d0400140030f07901e0300820107041c0301d034100b0005400714100655403a0b5081c018803100b1400c651209228003401180040700303034045401e40000404418418500b00002c64038510100300200038840c55002c20003520100b00d42203292800090381e250082181401140c030054100102c4851610554954903a40c0912541000d03515550301c00e0750080d0046540207110141c090740c51b00180f54a00f0380305105140a070b0300182c0d164081e0900c1d001c511481c0e81c0007480032544101c03c1c02e00f0758a02c04014840d046401e10b45490108 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 344950422 1250 344949172 344949179
    0xb010f06140910350a0510080618120a021c0206060d0b061809250e040b1b07060f0b06090a090c05070b01030b0f0610171902070c 57
    0x511407407090035000382140040c040d2811550714100d00201910307051810800914078143c0c0351003621850a03c01580c40700d007603001681d41d44a444014402c00240e02c3c28030868a40c2000d41c48044000d104240c140e402c0304002c10102c407120a40307840880200803c48034400307203806034032405500c004070b03403400740c0d1065025190b01c0c40202003002c0c1048c042d0029041c68584400400d4004440e040c000f4000032034100000c0c0039a45000d02c94a10b140320995000340f502e0300c1d180c030a07598400010803141c00d80503c85c01170f107101c00c4131307420900752241e94081c03013151307260f03961800b0f06064050316020018000300030041402da02d00000d044158042d402c0070072034088401c20755017101c844198090080d03408000c0050152a441c207a48111b4036a0980000c0f00c2404020880303440c054000d0040c5403c050b8000001800107441c840c9000c0c1d0b80603011030b52181c850104002c00c0b0751075240a03401180880c1070350301c0710f060194842ca0303200000300d0055001c90080b9030204100c0e0b00002d02190029821881132 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 344951672 1250 344950422 344950427
    0x609030c090118051803040504020f0c03070606030c2102192d050402030c070b04020f060f0c070909030c030e15030c0a0206070908030702061303021908370501090b010f06 75
    0x340c0d0480c40d0000c0365040485544025601c6e8407070f6000b9140920340004071441c0010700340c011101d481c00e42d48152a04c441141c6894000340031144800e81e020a00c402e000b24180b001c0d94106801201c105c0d011b00782560496091005103820031542412074160940c0000d9003400c031644140045644840d140c0240303010000640701d015081d080a40664418070410034110018001c45042642196003d0003d507601d10000b80e0b00030540f215541c000b00d01186014071845510050101000d144064a200a4803031900c1c0c81120140310024000481c1e0982100200e8081c814400da41403015083d5204103245498103a1a540184c2d40d10b01d13a188002085200c2e240c2c18014190058880c1c500280c485282c01c1d007080c1d4038000c443c0d000e0300c1413070b00042810110281c110b040c1c2c001c60b409807100740c00a04003141d486c1605a0f40c4900300c118028030085001688007901031064204060f84201301002940100c01c0c0c841e202c0ca5002c40361590307240d1044010410141040b402080003620400b2000d0625000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 344952922 1250 344951672 344951681
    0x150603080403240b130e010b031002041d04030c0f05010e0613021908120d09050708030c0601121e020f0414070216030c05060304021c050c15180609030c090118 70
    0x740440070b240c100301e41381d26551250a1007060004e003001040603011912242d005251080c8050750502c100301d008400b03645190060300c122000d21204408030081c40200c5009000100c1d0000e0018000492100000f07000400da41d0185015100014142040c850118501035007601d65281354201c1d41c200f41c04500d409015015800c6060342d0701000b0924041640d03a0301d03001c00a0904030920089030900e6001880c0e070000159a03000700890b203c3c1030f030300c8140c2d6480350b0044002280c28050310340085910700c040711003500c5d078560102c07855070624000700c0107841500d41c105049034400707240086c90201e640d80d40261114150301440071621820300f024080d180585080303502200d000c00035010004610180300c0002120303010b603200b903035036511071000421940e00d80c902d8070300c42107960401c081803200000e06000a01c0301501c21001002a0400c10003c078001e020301e00c0c0e1002d013400301c05401c2e4204680a03101100300070b000c030745000c40004002505001e00341c00601120764465030340404203101380079 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 344954172 1250 344952922 344952983
    0x303050d061508060145170d0c03090b0c2a030a06090206070c0806090d0e100f0302160510142a1201230301050c07150603080403 57
    0x4108400200d5602c01038200d420042c00c5505004200c14100c1c0440c000041408140c05401102440650000d0110030458a40f8a149122181480700440e848481441c201c00d500c20110040c9141140c039078048074480c1503040c0072010050b9132035002440242c503001519802c0101c03070191a4030310481181c1c41d850456104184640a52419102c680752000b284a080c8560041c1d0082241c0300b507400804e606200b41e120050410840903000201190089001d9001c0e09541040d90008110118100ca803180c02e600c20a91220025a2554220707011f11f400300260380c402d0902504040c91003504100342280f14800750340542040e10259084030300d40c8603040010803252240740403810100503ca51083c54010000604260071070300d07601d101000300544248545400500c0c0f5035684542c4a101c900207540c02d146911410421040040d02d018040c0714480e90000b21507a00f00340740c03900c5074001d0700039001101003410f60310800400130036030041c014806103009046036903c10300c00648001800d02d5482 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 344955422 1250 344954172 344954189
    0x5071e080c0405040504080f070302100b030c0a090506040e011125050a080714060103031713051b211e0f0d080604140720010e060a020f0d060303050d06 67
    0xc200d540000003082d20300303a88060b02e001507240d0fa10700d0100c449229000780404400d00104441042507800039039000b500c603600c0010b214851030ba10031b060b84c40c1010181d0607841b5044170b078140203080c00b03903101c654010310040c40400d01d2000c084280d0300711507400d03403141d1100030b001950030900480b0703a280280c0c0803c516114000d626050701c481d0348807000e500c8000e0240400241920510a1088a04c1c4c20340a901058608559480c50007400c402e002030b00b40000105104000b407102c04180214001498010015102c10030f0000028008120124140c6038802c010528401c1848065100717000310300020b100a08140c41904059100a00043c40c0581e1716171021140411110021808941c0c0c10554142000701740c40d21070004001d44002c45c0c43c00c6803c0b40b100100104554011081010303c240c2c516000d150228030846242a15000045560681e01c48404100100c00e680d0003000210780a5403041d007042010002d160640d401944103900040300401d4040e0b441d0050f1141d0001001c408 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 344956672 1250 344955422 344955437
    0x4030f1710150203220e07030515190b04090203010f170c09100b030a051b070b0f07050c1213050f0d0b0603030f0a080f060d03080a090305040905071e 66
    0x49840342070301005014030720341200440e040355155030081040d00c03030058461120302913070b1410580541008003140720702aa044440344c003180400340244074440c001c40120303c864092900036010700c010030300714031004001a024080001130080800f8080c101504480c40f025960b940b62100c80c3d40700350002d4002c00310000d04c4100049503140c00150b1f008880303a00b903c1d800815a01c05491078120581e40c1d0061850b000c0000800180d000c40c1d5015601c500300b942415407800407015401d01441c01111401020640040c0100d000070300e1040e10a54040c1e118a4080d1a14203410085410882d924288003400c101c0807911040d102e060a00c1c91010b0300c401e5440903210804100042d4102046000144c1a5209000440d1030343e20306000700d5038084407180d01e542c0c0d50301340303454000c04524040740c11000e060421000b183c07580c07504008a4071717400c0c0c00d659042c00b04e4542003152002488051412428040100070014403c1e02038000c40e4420a542d44442c210903c861620380344a19600c0c00700320030031295 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 344957922 1250 344956672 344956681
    0x2180907091404020415020a17041d0408070f05070311040903120b0112060803070312090308070f05040f06050301030b09060c160203073c0b030a05071704030f17 71
    0x50000000c80d41c200e403078520b00c881401c0118000f441030741c03ca201495044900d10511603000101010313414490340b01180080040c07074048410b80070324020b040c81502c168036401401050f00c05165007050027564050724240d01955641c0400444c07490807251500120750820a00c144401c1709d1841031402c2d6030034010304002e50340060201d40312112800da080d550b20348210302d81c1d01c1007440704840006034004010b03039130311b03003504550ba0b0b00401c60450000e911007d080075884540d000380400d50350f054a41c8869a111028155a04030341c0c04500c4007001014000000c1c00045540c490008000c16110a540c039411030800c00c03c072900c01800200c06501240a00a100310010212052401f080303900b0094024144000b9042c2443e59201301c80c002451801e0711300601c9a0503086800c14185412032500800c5120b80c10b07003c401c5031080b50102c10341880050510507079500701c00d034030840b145001d01c1c8000d0b1100c858441d50005130f405800280107000d25810b0300b0340110760300d5a03c0c3c1110000504a150 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 344959172 1250 344957922 344957927
    0x602030a020703030c030e3a1a06060717030403080a0209090c0c01020d0e060105120a03020a0201050f07021c0b01170a0609050c06030901020a090f122d03020102180907 74
    0x10b041c4801000c1100701e103151010b0502c034600c0c00d08070b1040104141103480d843d03a100c51444a495114045065142c0310205050200c43e00754540e0543c0b000080d8011464502c42049940c03000780b04503007041c010004000010302400b4030003030744500300d1601603ea0405040c010510071000b0106520280304120410a5a48031010b1660041098807042d0f628610340d0280d43c0640128000b040b49941030101880c108031004c503429050311802d5074050075011814032000d81d00e002c4000007a000d40c00c04000d00e009075100d07000504420701c0000d0b40300d181891903404500958100b10303e10070b20592420b0002d041105202005004003400c0d00d1043d08111020180e5842d500d00c0725000740110780ea0180d620801c04148070700394280030000e080c3e42c2c807032520b48a064041d41c071018030100050072895000c01c2100c1849800c038107030340302002034001e04c400540c0c1d698850314001c0f042c1040810f070025400c106a40b0400100c001038469800581c0341d1100030a451100c203031050705107109040e440c003080344840c0e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 344960422 1250 344959172 344959183
    0x30103120c081602121605030f0607080718050d060b090109050907140a12140105010f0b040306150e131b03121b020306070528051603050913150602030a02 68
    0xb24203443c20b07480e2074090b2001854a44107100e264400b4051500aa804a1480d004150441d1002c0c0e068504882c43c5241c503036151501114440b001c035900c6804600031910900b9014280219003030000041a128000a04202d0011100700c940a071106290203280c00c080303804d10300500c0410710520007401c0c040d05d201c0e04d5144a0060203200382c000c0a002d00c03551f4034055040d004105410030a8001c8040d410130380384000344080040002c0d820400002007045807038441c00c0440d44c082000d1814241036030780300700141c15208003103403410460910110740b40c14204920b43c022400b50500303440744015450a05c0c0c0d03110b008034520349070034040a010000b01d01d401e07900203404446450101c0241c503400d5074802e010806c0007801394140c45160100401683c00c003006140300b82901c003094510b00a80145c141b041300503454604001581445840040381c6481101600c5902c242402c2c0d0030101c00501081c00c130204003104050302916000c00c011000c1070380e42100060081c41c0701540c5031001890010390b1302e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 344961672 1250 344960422 344960437
    0x9090827060405101202030406090201140406141c060e090c031c03091502070b0402010e1210020c0f0102270907081603110a0f08070512041b030215030103120c08 71
    0x8502003c45601c0861107022940a0b00c848017400b1926424142803003002400041e404034013158a1103449001050b062040d1401c0301c0550307a52468030761004202e0700321b0b5040000c500840d051440300c02c914100c628051b82010386540c414200c01480c0c410486840d00165560720381c042d0b00304000e241d144d44080303000075210005504000c10404050b107032100b030803414038440740d4440340b020810104001c03011142c00d00460003603132031035001400c0e06c0810003102219540215a5849070f0318101c4100041d8026087c05e0340100282c0300d03050713810b601d00c9099074407020200c1418181d0014407031001d10a002c03c1212504107880034070302031030700400141030322501908240503010009081d441c4a4400d130009801b00c0001d04100d0380321007150001400c914034641402001c0b81c6c035140010240e6129a041c0c44200024041d205001d0f169038030b41d040d00341601d1004110b449070788980840561070742740f81403100c00e40203248150b5075031460520300081400c021008081021042d201c4021482302026645030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 344962922 1250 344961672 344961679
    0x1d0a060c0810210201020a0f0c050a050616060c050d06240e010c11040902150306030f1c20070e181c18170307020a09020910080c0409090827060405 65
    0x3c08500060340340c801032000040425044c00c002104215a00440c4012560f044e2140100780e5200c004100240c0a1881d12210b60407181a0310f20101d851a080403520071a039041c02c41c0741c403d010b000ba0044e524141c0000d000718403411030208180020b81c480420152251600d16140d2200b140000c4c6505801c001c0501030550500f425006592a40d000024a66000340076800c0c06001d600c2c2840d00b40c02c1152400e120b401001c1d00194445400f244030808115280c2c0d6440c20101448000d4070280c440b088210106140c10140054481c0e0030000c10020300340300e120000c4c0510b04440e541c4288054112034202c560042c80340c1c070440e90312101c0f40005010450420140f0002100c1e00c1d038503880300b81d601221044949181c03040e42c442022004000c2c140c000d60700300407a1340d01c1e95103100580c412a003080345c1202a62100300120b0b441803032400d13003090300d00e5601440e080c0e0307588800c0140e0352010410780d44050000303440e440003904003007088902071000e40c0c10902e07807800c000001c00500892160500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 344964028 1106 344962922 344962979
    0x2031c1a0102060424090203100b0306070201060501050f0a1b0c09180c03020405100e040b1005010206040f080a050d0219091e03061d0a060c0810 64
    0x41070f074010810000c1040390812041043c030007460100411a1b94110700401640c041c0580e03004415020701c08103409502c082014203040001d1301481c2503a240000400069030860140c1d01000c0c0302440854480d900103034181d41c0b0304419000010410600724004003002041100e820558400070310410600d40c0500e078030400311290000242100c05d58803010001454980c004036030100406202c0207010341c0c0c8540400f0b80e4041643d00310340c600202001c2240000c0c01c082110000c040c00d00c003c201a00309911100b21001c07851001514418000400241150094003100d0034410281404c40d40e80c005400c410600500d0843e6400019041101c00900101c155032040c50b040c1d03c594000c08403602e1070381c1e0b11004264604040f804c07800c860794290a6140f0038010580710700d00070b030404200c041800070014903103d002040034410505c030040c00d2000d805180b10b00011030301e5503400000c = true := by decide +kernel

theorem cover : BRFrame.Cov 344784172 344964028 := by
  have h0 := BRFrame.cov_init 344784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 344784172 ≤ n) (h2 : n < 344964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
