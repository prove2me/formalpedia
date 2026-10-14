-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3639
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:15:28.676982+00:00
-- url     : https://prove2.me/submissions/59606b90-c106-4e8a-83ff-66096d01774f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 654316546 ≤ n < 654496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 654317796 1250 654316546 654316567
    0x31d0106140312160809040603240b030f0a030e030307021c03122325030e0c03160b03071107060908060f0129040b030f1f031e0f020d0602 61
    0x440040c180c075102013450486800346905908291003402030412001040044040d591a4040d42c0215000f20a140d0504107500d14502e101d0301210440c3d404500d0326490080701e080010302c00c40c903242c0c1130b0000c001041c070b6610155607841c4882d00156140c03000300300300c3e00107844141601c1d44480b80c90b070b0b15412000c064a400b0307154010860b45c1d43c206514207030010074003513106035003108000c0241c0e28112450b03d030041310810b0380c05111a00c0180c4280304e00c28000041d8540e00844058a5134400d40d80890324560400d616803220805000d00c2080e10348003401b01c031015000550f0001d8241c00c20469a050810700030b82450311561018001c07860308602082011028421154000b1074070b00c0e0810a50b040c10340380101c41d01c0342c2e1110003004590a02c0b203040b90403400121005801c04d40c080740d44038034103112400042001110402105008207504c0301405407a140c02d44280c0b80d11402c2030b4a46000444c1008400d81e030644165000200c40140e0300c0540c5400341003410b0140110700c050794a604000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 654319046 1250 654317796 654317803
    0x30d02040b071e080d0506010210050403090f0b13031202070f09090213140a02033d080d020706081902070f031e02030d02130518070206010b040509040201031d01061403 74
    0x4049035101200f202d600c0008007148200d5070714002c5400c000445807200c60040380b5203044007288540c442c0c50a400c0c00149600a080c80040b01c41030061122029207980105406d80030300241000e50310440f41c01440028049840b5007140e401510460b500c1e0f07680c40c00504540340c81d6a20030075090395241007110a6042618900404600e100402d221500580d41a80d40d5144001d00380174240b5401720200d1044290000e05800110300c3c40c2011000303103840c00c40100202c1825550011406041600003044c25011841140c1000141c01420441d85813a07000d0b2130002008041d0528004070b00d050341c03891895071014140d5280aa0140c0048002034a005401c200c080c0041e03468200c000030a06644503800400c4950f400710600025840f074100d14110303e01c5802c1504101d510141074400c0c0c16060b440c0340c00a92203170031190700315038459903030f0482c100d05131155004407034000038000002009940a40c001b106491050406100a400100340c924211040e54004120340500c0c0d03541e201c003914041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 654320296 1250 654319046 654319073
    0x90c0e01140a030201300f0f1404120c03020a1a06030c0a050a05041508010c1e03060f150c0b2d091f06080109080901110c01020d050c030d02040b07 65
    0x142c1e07a00003440d00316000602149940400c1d07000f48007550203905030b0134004d0200041000354850084c8682d10212001d40c01074903550242d40555494020088107444010a00c6802a600185160700564000301b007150702e5080c0c04019015441000080c400149078555040343e0916803d4031f01030b15003050020141001d8880213418410480d042c400d100641c0c0c0d100c0ca40045813000ca1380002d08000b800f00c0360440f400350742c0c4044015440d020411034404c1e00710900c409850b8a40c06040e00350711480d8010340465016005901c0e4840c82030b030042c0050045982c6070b407458625810450907110203542c030105004021101e452544050701203a40c0c0034050202001e606141204548800740f42c410f2b845580c842d001c9001c81c40d10103040b80841110860790740050701404840c0000d00c03941071541460200d0f54440c6e4801c0340000d01c041c055800a40f07000c1445003654105078040c114511000c1d01c01c5565420a0441201c1c9001c20001010307540b01600c000d00c003c05200300210740318540b9051100c00c039440b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 654321546 1250 654320296 654320299
    0xc0d09090e070807090b01020a120801291b011d010c0906110c01030b010c0b0903030f0604051501050c10090b0601020105090f06040318031209050a0918020f04090c0e0114 75
    0xc0e4105003d01040400c4031400c1d41d0b1074000014112101c880101d15080b185100980104456080440d04c55131142020741a80c0311800d40ba8580444220070700c903d0140d50404008007841484449501d100c0d1070b00301016282074500104414403110845244032034803220309805690340b44882c141403a04030824000500c114203000307903d8070b1a1580503032648200aa07460406694000004107603020748180c41000e07030000ba0041e1146400098569207074015100c40006440050010b034041c94140626407103082900d43e42d40554003100d0054030150400700d05000c40b03024081c0d40080620b100d1061b4100a40910b60605c168100f8000180c02c603200580445125000b07442c50300c03000358000400c5c0b6000765140c0745c848000c150380d400318a00c0f150aa04000e00c01014142880308959011403000d050350004c0703411440c0903035155660320403200307034401d19901d0198a003802005890040e070701d0300d0034032800390002c44d141c1e04507903c03860000756680003855014110001485024100464255600f20 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 654322796 1250 654321546 654321553
    0x90b031f0b1305040c0504080609030309010b060721210b10080105091501091701020703030c09052404030507031212090803040b040309080304121b0609051201020c0d09090e 76
    0x1071981454810342c0003030049a02480d1940000c18a0fa403280e02110010b0541c0403d44501d800c1c40040943c403a4025100d010f00d0b9800d1150141651402600b01c80034a1790140150050124981644204d48803000c0d1280600920800100b40075160b00f18240c000c01c850304000071000d12220400c55898043c0810700c00700050800180125141d1110300fa070410303140c4910345203401040c0c0040318000d990307810841405408021001c88444150080d080b094031944051021446010381210199018419036611080c0c402400c080b1003420100e0b43c0e014041d0b000414a42071b12070b11480d25048190f442220110040d0103d42c05503980901d0903074001000407420701c0040d940b5100c1c1c0c849030201401c040c1442d21880041400c06000b0390044000300200c0c000e480c4c1359903854400400380c1e1075106013690341040301c50909100612040002c0240d0300c00751a5445450b003003000703029134000c00035111220740d135003003258481d80300c0104000024422507640350f0200c03500707004c0d03004266602804225031551 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 654324046 1250 654322796 654322807
    0x19150206011d0402060d0b040c0c12030c020316061d07050a15020c0105091206041506060302090a1202060408011e0e06091002032e1d0c0f0a090b031f0b 67
    0x35519003500f02d60121080d03501e4a02002d00c9074010105200c0300c40e030080c40d20310740884d407030740207142c25019500491070350700900600c1030107074243c5035020364820041c0c00030000003185c102d6002501c1d01c464000e4100064030007105c454040d540300c81d101105000e41c84841c04002500d060340400001d00706a45800d407101101d00c0020b541c0e04074180d001414808042016445c0e40c86035031050741030100d136204540c000e0a013800c0c082d0b4802032011050360841e040490216016010b4001c4a42c0c803200589000185490810311b0b00c12200c80d500700720382c46001041f0025000a00740189002d080c3c40024240c0b01e0441e4070710f9101144c02d13010250045400c414104200d640001c22500319408002c000503a80c0d990300e1414118800502d000c01c0c0901c0d42c1816504062401c12400c2c0081d141030142e958056410160f950300c07610004c40d440c8114407010084803c043c840b400150444203240d0a107003615545072140400260070440d0f14410200920300442040d0380261604401010449851443e08 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 654325296 1250 654324046 654324089
    0x60c030512180607080703051e040209091204060906021501060e0d0206130e040b09160b1312060e1203100302040e0727050705040501080a0b1915020601 67
    0x14050031500c0c0c2800c0c50141e00140001c1e855001001e0005010015a003843c0b070543c3d4068070007001550b0000c0064036180000301500961008143d412010b6606901c2c940d4565003008200340009101d409240140c95282c00000403480c064005040c142d1124140582041f00080c5000c80382ca000c41d43d52010000104142038101e8208600000701765038440d40190b15001160080c070440c40145100c02104900203003046540828078040d501c00c14500c070f4152a81c1203d207a56201e4440302d00148003804030100030084500b002008052000641c03a4001541c892140740b228050701d01c2514415129030030b051040c4801c2c043d28824400001c0900d00710300304602020120714460000038000c07035980305018284501045088010311460b45881a03034081a010440355000c602c1c0089506410400821841c3d801181528243c5006a49140780c1d541e507161100040d2150200d060b07004218211000c400441041c400303005042d00804222918040c0c000c02441c1c0a0141d2014072030800308590308921 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 654326546 1250 654325296 654325307
    0xa1e0b0a0906090503040b070201030e011406060703030608011509050a0c05180a0302030a0305070c060302070f02011d03060106020f12031306090203030f190f03021801080c070203060c030a06060c03 87
    0x1004000d100000c03a2141c0d40b60050080040242c00380043c84040303000030741681c0c400000c0c40407034807e03a42402044000c2c0c0790a170a8030001600311421070303402c400141403402c1c0700000d00111402403601168a41c0c3d07450281d4210707502c840d003607000d40444039012301c50b1480900074203400003241c1c80104028a4800f20081aa00442c4015658115000607608481d9208074401000c1c43c3c0003410388144440900d0040c10a0348030748021244d080819a000480700d0080c801e460a0030707005010741d004d0494507030045070b01c41c2010350003180200c0d02d206400300d251410004076010300f003141c00502102d1440c600b07441c901608110002900103080007000b400d60300172100d00352547d17407107100890034070103d100003419070148000e101e0201a01080c0d00d0564626010b4031610400203450303000781c2280801e003c80581c80380c2518844003425040034111342d544900c104030707030015900540c0341c18601c2d50740c0000c0c2030041c2a200444501e00220510800d495144550f82c01484642415132080c1c5c0683e03800b422 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 654327796 1250 654326546 654326551
    0xe1e0108062101020702012006040204150e043002120705011d1f0507081f080a081801051303080a090b0703020102030720120f090d050a1e0b 62
    0x1003103840c0000c00c01d541c8400500307000203401020080700000b11410254001d4005107800da000450600c0380b04e80c40d07004400c80c0c192004131403028190319030300c07034007400060201c80100d01000d80b083c02c1d000810900c51140b0030f0249100f503d40b0080a12004440c0e10400ca220321300e0a00d1210f00c2c0703121101c80c1d40006d040c442043d5100700c1c0c20344416850500c6801811a003d8461110089a0203006400c101050b40c1c90340c00c82c203007c4000d1700d020400014044480c1280c008000c0384001e00031600c01809031001c00118503003074000404003522860701e9400c0c84100141102c43d0403010a0481902007440c07180b401920302031800d107091043d40003065060b12100d00c4003900001c000119441010306c100b6528000c2d00c03455882a50314503151a000f4000c3d403007114004002540507107103041d840340b0400f507408a850f8400007012680e090000040341544207460212001c0c804001000254581c00c000e681d61600840151407208050f003400300100004041503c1074070100e0150100148a121800740c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 654329046 1250 654327796 654327799
    0x6121005090f01050711010509060c180f060d021305090403020a0b04140304230a06052209140105131b1d0d050318031203060415090501150e1e 63
    0x11680c03101541c060410b100703906460210b5003800104503d46400030b0390080b510004d04001c01403561600e1000d034840c4415150b400104d9020041e01d1941e802003641c604105e880144154030034030803080001c203d030384103032454240113801148000402c03980308000c0008000944031400d042c601582c0007034845809280040020303041002143c207001d0b03030380a12554a1030210440e03645903101c141c6410441400c50050b21503100700440d001107401c0c2051501c046036981d0321520308040030761b890081e5000c0b00039810f4940030b0000c0400139040015009082c90121200151040755041c42c0034040c40500240304810704500b82401e61041c0044a10140c40a19442ca402c110b00040c5c50b001c241d681414003807c07036000703120106000034040044010a00c3c4071812019150034031540003455140c00a000c04030903a4502400090340341d04107508a9030030590440681d10781c603500d4040c8481115000e030854001d81e1054001c0d0010305410829030404c1601c1103400e20384c101e001a010185005403198010f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 654330296 1250 654329046 654329051
    0x41506021612020319140a0b06040b1210110c01180b0105031204050607061e0e060601020712140a0f03020106050406091e0c0e030d0e0901050121110f030f0708061210 73
    0x85090041c00c00c0b803400000b00006c2a18aa80d031241481059201e00b034a82c82e11a07460000c01c1c6c00d50b440d00241c1c070348032100d0120240600d083c010b04440e00421a00300c4807450080108500300c20000c081c880c203880c004000e07001c4d04100c501c604100c0d01050050300010302980c4601121640b684410094034200c0d402201e0065403011103180c0315000c0c001103032490128010450b840c00380c3e00c0517030300310078400c0c054441250721680e0345200490341c0384964800c54a0b440300300d40350407010400f00b072a00c58202c0b070600300321240c61740b0350b6540d01481217565030260300503556001c0030310680c50b00e80544001071101c1d00f014442025260b41c1e61612802c80388445030b045a0f9600c9503421140168907034203003000e00a043e20484520008003a100100310104144170f60101e0b000880c4a60256030305d200368150031152000c0300f09200b08500d000348500802300b44005402c3c402c0c4003040106e280194480c50310080c0e1540740303003040e120180c40c0c0304018003518070480341200848102c04001680b04060100765902 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 654331546 1250 654330296 654330343
    0x1030b0c0405061b1504030c0203010515130f110a0518041a040f091b0e010b1207110c0a0b12092e110a0e01080f040201080c0304020415060216120203 66
    0x100d41703842c102508240402001400704000d140c0c1040084440d01e00a078028062942c40030300d007031680c05214074516801420280a140a20480c0d8807a9024040e81800012104007c841000d01034200340c0242c400108001110707030020f50f041e104800c1e001c0d13094070248580d065800c500b8501405000704a40640d9481480d1203414050381c001242403a0411031402c20031846030880815407426000300b110344c2050500000b0b00b006080d003101d80403d42501c0c140304903203854108480d81580e00811404900c1b4142614145030342d5800298005c1c81c1b1040020b40e5203d811210211441c4010080022500100c1f69035100e0b010010508010501051042c2c0039104000b02140061440c40580c41010002180e1104040c0c3c001c00c5403010f401090300d90300c400c3c0e51020803020804100b00c0d0002d000a0701d03000842c00050804d00074507081351006001013000020b040d450300000c4000d900c1000103030701a000c084d03012008144610007070305541d0700440d070b041c41c1500400e40c0c40300c400c9171542282081a00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 654332796 1250 654331546 654331597
    0x5090f0406140118060819020603040804092a020604050706030b01030f021903050c1813090605091b0618060c01060b040605090112060e0604090203101401030b0c040506 74
    0x1002c40d1040c220821440d41c444d116070007103030340024441542601e040c0c0007140d03801d400184007080c0c84c0c150780e100d44251059802d11803180c00151045035a248103100219202140b4080c2c2c01e005080d05821412400c5445424220030303140101c102d007550000414403000c03c20204116040e6402824040f07112941c00c40100c1c010551400482d0182c0d1010070441c01c14011700d1240d42e60b0101c280ea09200680f03c4c1a444c9069105401c045005403041d0000703c03019050a0b240c02c841884d161000295a403441d88654041d15400c40d224951078000c0c20801075180301240100c10042800c1c0d550904210405412940c1080a032180500c80e0f40c01044200040000350402e0024000c03140c0c0d9541c50f10340d01c00014080741c000e8140540414440c0e40449020800d41c4110740884050381e42e204a962200350520000701000b6500b603815010b82200101c1c45119401840d01c0e9000e1070000b08019031440c14074581c02180500784060030720080204221903034507042541d09071114072480e840520620034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 654334046 1250 654332796 654332801
    0x90515161416030918050414070b040e070302040506040b0909090f0a0b043306091103130f1704140307060c0201082a04030302010b03011509020d09020306011202030d02010605090f0406 81
    0x90000c40c041015205e400c0321400b60381c0005020714898614006281d9030b6000440d10740d80b00c1d002d07058006000784000c002180b000c041c00f0781c015115060041c502031319007001c2900b540c07041d00008151400000e40c0c007402d0400f4131480d64480314a5015003290202c0340585600c454040350f002c2e04c1d0f2101d440215061100500d18003081907205c0e41184c8003805000e03c02494402001c2000280c070786002070000e0001c0752030092404069540703181c5403865072500020101140c41500980782c0260755280c40c0e00003803414142c010342c4c1010340324441d00e03103141c401550403940d11000c400c1c1c080d412005041103042e1300304003021006a82400c09000d141e86a0b00e924412801c00c2c080700d9a0090f921800c01c0880d0a90707c0140141c0e4003a038020321800c0c041c9828142620b050025900002d0301c00401046548990f50143c03110351680140070400840c10380000f86401c50a07080200d04a0220801100b1450100039449054116000920040e032614001816411001740300d803044805850001c0d040040d0f0782d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 654335296 1250 654334046 654334049
    0xf010b0d020a050c011a1c0b01230a031b062607050d15060e100f11010236180f04020604151107082b030905151614160309 54
    0x1040200b0206c2c0d04114001ea400100c2c00c0018081c400d03807051001856803c002c251400c51308900000b195074078180341108a4800380c0c000001c80c464103e4051999900c3d08100c1000303600980b1350300c00603080d407480d440440a407036000e501031180b006070b00200400204240e10420201690b81c0b8155940c40c58242c405100c5d01118412552400c8084c440200e0011201e0b400c2d2105640e40309000500001481300005600c0300900114025408030044a0b21400300c1c0855200044000350420102060b1500f192090703000c17802c8034150115011003400300000e2803040800088685601400105089112450020b04164032501c1c5020001d015519038800700c5005240320780e1640240d00c01040000c2226000101020b001c1c050000300059400700042c040c80c20a4a01a4a40f054111003156421079428800c12005041d1202d202001284d01880138030030041100100104514054604c02d401c00b0348410751806028801000d00000742034481540c00302070030401401c0c01e14040b81000c1d91b820106 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 654336546 1250 654335296 654335317
    0xa0516110c060a030207170c06070806060720060406030f0b03150c03040c0e0403110c0604140105030a060f0608100f0608070503190221060a0501141c0603030905090f010b0d020a05 79
    0x390098031847e2412802000c0501e941820794100e500c0e8203d0440d01580c1c241c804651200c41072001344081040c1150101040a40c500803510b00c4605a0224803546c0007503024101181d9288550a00301c0240d00920210600c21000703450084d00d101384403e80e01001801c0865858004000141040000000719014103504c1d20400014a801d140c003d0120300800b40c256070a015881ca00703215410200f040d00c1c03d9584641c3c003580c01c0801d0000449030341d04001d20511110f80c6422000a64104591110018052a5807001c1582c600001210a02c0740c0650100384244079018080080039400710034290401624501075030340361600c5c0a07113000d13502c1c60040006009e1000071002d015111000800c0510b60100c4000c0c20140e4402042040744032051181c603010031440044444038a21100041180070880106004080349864221040f12444c0c2c1045000c110000410b00032403401c0c00d8410741c8040020401011581481c504030002e00521842030b18060b004515040412702803419207051081 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 654337796 1250 654336546 654336563
    0xe0103081312080a021605030c040f110307030605012d030c0e120606040608030304020d0201030c11160e01080313090c02010e031c15030b040f020411030a0516110c060a030207 77
    0x3402d0403c3c888a600040c0644050722440280e00344443d00c02010404844008000e4181e201290341400060282c0c804102421551002011005401c7c1c80255000318450f40d800100c0608050015180c10700138801070b000f10448131420800c1e9840003110b0b44d40000315107004981c0207007150041d10b2452182c4480355016840c01c0c00807180100004105101d0001203e09000190f990a8803544910050b80c1c00382d040030000e2621030155000e6044589100764074a08464004108100542410541d1000810014107054100315010302000014090b1202c1c0c4059803030401084070002c4000c071588102c5561a4483c00b050100314000e502040c80b10111205999950075007008007010504c208460164140c031781000503941e01362220321103007901d601c0500f21815032200c0d220308000d0390f030f8024102d038016110a034501035540040041e5000f0b00529101203220f007000d44000400207603a00448041005d0b088090101c0d003400944e00403a40d1056801035519550314104801a104a6801904661 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 654339046 1250 654337796 654337829
    0x509040c0e0a060f0903120c0519150b0319060f020d06170a05030406030b0a0b0706020a09170309040207110d0503250308010b180918070e010e01030813 67
    0xa400c40c041d500800012a6106082d0b5101c60b0142c031314020900309000024072005040c40007890f038818604880d006c50814808252895495514050f002594802200301005100c4100081c2c40344140300e000c0070790400d102920000d0041390f6100d1801c1c02c0320084140242c000d00500240b0707406140c2c4402c48900943d5148411050740010b8400c0d48202d100700601c030394102070480004946c0101c182d910030040c41ca403030701d4800101d0103080ca201ea100e520441110300050291001d0009020b098460800581c58000400000e8032a044592001010740c20100c090f412412011044072402442202c00503101c2c10380f4100b520680c541180c60f15041980c004418041c0000007018000030900441412000304803c0c820496511002e4401001710f4031a0005114003100d0300094010301280454100004265030001a00c50b6026540303071026030384000c051408003505000c2c48014050400b160740c90b079450207544000d0000c0511000d00b00460210b1035455a4020f0001d40c1c0c000d01c1c001207021442c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 654340296 1250 654339046 654339071
    0x4121d031608060a05090303070c0804050303040303032405060f0f070c03051606030b0a0302041d010921110a06270c06111614032406040e0313030210050904 69
    0x40041d07018040281c0b0520b030000e5083c1c01c0a000c1c0b039209aa00502940c19170f156581d050b0f07403c45200b102115403500a0001107540d4904101403c015802030742c02040712a0b26000003404541da40c80f4001c01c00202c01d1080c4480e4440400325020440c80d02403032030351010010504240ca0045400041c03010009540000071302c80001000304d001070f108a41260420782c1c1c2d04040e0300b1034030170031803258119000d0b02040015181503480301c4100c00f5101c4038141814084c2d102d403400c69142010885d800080b080360340001c0d0180d00301c042d041180f28100301001c032403044402c0f503840001c444e004058640380c40660710810b001c5041100c02d00d0302d0300c1c0d018040d04003d1400304c81e240607500500002500c1307200608400100014038100601003200703061401c600703110f41054210000564a0740611409544851001280d09580b144040218420000b03080407410042031f1500c4001d0382181398801d1044001201d004108a8111ba03412036081801041060050320b5501503103031b1050703015203440d2260485 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 654341546 1250 654340296 654340333
    0xf09010b0a030c020601120f020d12081801020f120c1201080102090102010b0a14121c0c0c060207050618030114040b060f09131401240e0105040504121d03 68
    0x70400e900c081c020051088000c9035a90024810f810520107005407040c080b0b580c0c1d8100e0709a4030300203040f0403148201604c0d0710501502242842c40065001001c024500300d0345850b070b104100076000254038080180c0514078890050301070000c10442c40d040800e400c9051107041320701e8154010000b000640c0e650014034001d420483c0418059400c04d40d18494900d866036a03041540c806154050309010705000340900038001c01680382140c80f525003a042c0c15190401c0c030023011141583c0d400044129842c0900130125140e010324255404020700380136561301d05090701d070510124544403c0042c41a0f0009002d400c18018298012816206210501102d01d5849100d070f1000c0d901c402c281e8000380c06103e03450808841e03500c0c1c2d010f800002c0300c000410055055035034503401400401c0031301130030181c0f00411041074003902c6c0218094004002e003070308103c0c1142c0100000c40d801c01161500780c0310880e0071040760003c4002c11103004e6907412450301005268120940240846481c0d06014400301d12 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 654342796 1250 654341546 654341557
    0x1e0c0c0a0320030301060801030f0302010e010e0a1434090c050d0c0c0302100b030111161403040303020304211703062e03110708030702010209130c0c0b060f09010b 72
    0x40c9018111403038a074082c000002c0b24100c030700c15034504007640c0c0b031070b200e410703a4401d030740d01c110308654940110300b40f401030034020038410b204100090021501e030341c942045050080d038003044443d088201d007241d00b903000800070724144444001010051125429a25038802e10fa0440c0c0000341c54001c0301102d40364003502034100110408401c03c80403482c49030030307201002d030504000e0050f482000c003d20082c0e041d40003002c9810000e00085040a40f000c40603029800c0260a1304c44c011705845400b060241c20005445c0e2881d840016614150031902e00070344901c5540510000600740310500003280d04044903246a4540040401144240c449207410103a40240c601c140305580b856070030056081c1040080741841e44040402d2041c504c030702e40507009405c10102c03400c0545c1c41072240c007010a01c914000c41c8520b20301c0d0300050f5141626806c102e41e143c1028203403058076180030524005943c02115042a00703402213030b80092030344e42800103580d500d00d130b03441c8a0f0803401c0038000140c0303402128058038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 654344046 1250 654342796 654342827
    0xb0408070302030f03070504060f050c070323030c01020c0c120a03051e03090f060709121b030b0f0105040516020618010608031308060a2a02030d02040e0405151e0c0c0a03 75
    0x8ac0500c0319411101405600804000ca800c404030400000302100c81d4500c11a401008050003585c19040c40340c1990031026404203180d400060f5800e0031101031004c0008448111902c0104000781080c0c0c581ea0440007500800344a40051000c44880e00d1038959a900b070100381d0044e542e40340118519807540c045594160b0107100350743c00324a6080c050455030f81603e0320404003240c88040b545807000c12402071071903400c0300350001c1e001002251b80003a02c01c0c840d42c4807890030a159454842400200c07400144480c09110f49400d600c070503a6404240381e40c01507070345280951451720b0204941d00426030369200100c14440059144220905044441d0072200464203460803981c81c00f0094041d1140b4100d0103004402540d854400c03c8420090030407407425910442e4140205102040c080364030641000b808400c45804000401804019500040d85000310360401800c283c004c6841c030700d15200c50616882d0280300018004003c0c40705032202c922180048030340c00781c0c0905014041000117003911 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 654345296 1250 654344046 654344057
    0x1020910020a170408032a0d050309060907030b040803100e07020d032007020603131b05040c11061303020322150c02130f0e010603120f03090b0408070302030f0307050406 75
    0x3e4007900d4502c291030440d0402c40185140150700c51260f001d51000a183c80850201401070403201c140400a80a001c000350710f60990f20b00701302d001c0c249086d2008041c400194071589003400040c0340329100c180c10a80c4440c45a80b640c48040303540064040c80d401c40055035455004025801d980080d03414444031041d01c003040990b011107070306050410210040360308214100300503001410518029507010406042216000e10555506c10704031080019121107000040800c0c40503181c40d00c0340f8024a1024201003410760000c400031501c9800c0101912130b40c8003081682000e05000f0300455417a952018943d00b6000e8810000038403005150060f500f070440b0740c1e0a410700c0725000d1a038080d1015001413503038003a400856084006054400c030001c50407a141c84000c020703d102401140e0180d071207007000b00c0c8a408102d07802040544400501030405060884000c0400c030605081030300700340c001a04541e1340c01c45050a03840c522414001ca103200070300108001c01c181d803007000b42c81582c0155940 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 654346546 1250 654345296 654345323
    0x809010c1524061107053723010c02190305100f060501020a08030a0203060f1003200423061309050f0711031c0e251e061101020910020a 60
    0x126a4000b041098007219840050144500c0c03410040c40200c802ea50a6804003881120100340d07030250214844404080c001d01052000c0140b5480c8d140741000000680042c058403800001d1501005040290113454442c60b059006864201d0700c0f005580c006046900c20f20100d0090b00081000b41011000c0a07d4010040360643c40414403409103900b00070900c9c19912502c0491001750710160456600120340d2030400c074943c94121440e9a410b0450314009250044d5511895811001011079007041608000510103100b41556400c0d11400000b6058417155920700400c8043c420300306144015241e803400024130801c0340d00401d21803141028084a1901c175510142c501c55440601d00082d60010701641100c0909040f040c0c410035610040030800c01c00d41039444d030400c0f294003072604040c0600000c40c02c0303c00c080703021f20008203018890701c00038003002c071a005901c24142c011802000b050080c0086404800d4040ea104003a004228001d819583d5801035500e4040e4070003200c0030540c4005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 654347796 1250 654346546 654346559
    0x61413020f07030e2b0507090204080312041a04080a1d090a0504050a060c020f0105090f06011a19080114030a0309060e010908011a0a120809010c1524 66
    0xa45032070611846580e41001c00c5654141d4540199401c541d070801280d00c803141070124003040d0082d01446143c60300e4245090703030800506091854001d520000e0040000b000034400c000200c40800d82c1c0241c4400c1c0503107031450308000e9084054440c0303110304008030500050204600c02460340310a107456480e201d00e10b03800503038140000889103950240c1c05e00c0c00900940c803107403c038940c030070700c10070075508100d50503910f05080302c032023003070120042c1e0103541a007403c02824440d290700070703c0708802044080c4800300e5036a900c240500800305481c0d03880624100d185540c01c1691b0422981410f4007106645403c0c0042c15003c0911407840b4203c080d8070307000301038140403031030100068055130ba42214604002058450308900c00101d07041003c50380000951400030300c0340035204001c00c015801c03620184810044203907090f80022481808004a400009189000320703141c1040a080c00900600c06051a204100580105003200c504140c41d148010b5601421084900e8000e22010142900d0b0306 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 654349046 1250 654347796 654347801
    0xf030206040e090c030d082403120f0706020406030b0a0b0c060f1306060e06030d0f170c0903011815060b16111005030106090b03061c15061413 63
    0x440a500524100014000d14110341c0a10f584000d0490445400c0f0700d05001080c03801310340b82d90304070000301d11300240324a035882140000c4041c02031903142a82d07850860000794840c8111260038085000018541030383d51100703800d80740850742100086450382c0d40c810015000d0001d03210020f1240640341008228049041c3c1a0780f80990700c00010411942e4841c9114111038014001001840e0a09054800100580102c1020741503603206520241491014140340c9091002e0000502c40c18007020300e690303039128940282c00780c00840d240701d4949889100050350f105101e1043c2e01035080a40c5811003004d05a804003071a40318680028040a05d110900c04448031402011401304c4100041540c0c0181194042c1c2c9480c0242000d090a0f20a80c000a5200c060154454040b50011004200741074001e8040c400800000b8483c61440c82d000d40010181d0510202c1080316042d41800c5800740075040901c44910204c2c3c81c420031842d07880e015003a107080c10510b83c5511039201d090b002d840240e206e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 654350296 1250 654349046 654349049
    0xa0f0c050304110f0105040506040b0405040513050d1b0b0109020310080c0a03021e03030408070602120a200a1b17010b0d1e15050402010e0a0e012c0109060e010f 71
    0x400600fa10526070020441d06143c40003d407410003009000c081b5076962094000c01c02801d542c00410344d0707580313040305200954100400c2c0c85a0104520202408120003142c1282110760381d1a00000b1a02a800c07000704041d0b52083c0540300f46c1c0e10200100303030380360503500440c003c40c187e6a001c0c640302d58585035540d5515102e400c0755040402c45400b0001070401000a590b075030f2540841c01c00848001e4040b0f031442d00294003160750395102560800240343c05018002c43c0c0c0600b83c8407075250152032400a0211140150400b540b0b0b03d003c1d007040520701090000c8800140d01c00f5403241e000d0310b80303001d04480400a004500c0c0504114007290510346052040541d003c001811080715000662a001102052210ba01d000c03500e0101111f00025040100a0f803002c41c13090000845041c5400010013a2010065260007040a0002445a030700080c0c4043d0444010030941c1507161302c849480142050a0315114062004403070020039180b40d60781101e01590508031009416a903184154031000009 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 654351546 1250 654350296 654350303
    0x512010e03030f0603010b24250b1b03131707020a260708060105100903120c0308010503030306130b0a0f031a0f10060302070206090d0b01080606010e01080c070c05090a0f0c050304 79
    0x100e28240341014030440c090701c270507100c0b01e03c010f143c01c00090554050a403240c40c200c503a000001d08011408081c0400c41602d080268209802d52802c4120391102018005002e1b103140d288541c415031401e49042101c20321640602000802c0340c4d142c1c100604408034929801e41070500003034502d59184000751440032100144000c154907480c0500380101c81c0800c181075801c00064220100c04516514920b06c5091040d43e900448031070035080c0204120410381040384650400c000b4041d507071380c030b0001c0002d01910300c41c1e001a952000000140380c001c9603900c1019015100d41001043c8040d40e840020440000e20240c447c039500c0124072000c1c1101182c50300e04008103140c003031024505c00d501030100c1e2440a0052131424041a0005064000d104401c8501d81c03041c40c0103001c03541051204680103942800c0c50b0082d81101d100280c140ca40090500941640108028092000304003225008000291102c4a1400d008041c000501134811100702c01d681409210015580b16230b044078402c640 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 654352796 1250 654351546 654351589
    0x105010602190f02090705040e0108030901020d0c080a0f0504050a0303020c0405070903020a0b0a051209010b040e030c1f090b1905010f030c0326030c04050a15090512010e03030f0603010b 82
    0x140c1e90800c0180040641b000b02082018040411541c944000320360290800500450721030b0308003800249003e0603440c00c9020011a400c2800c0028012029600302002074204540110310302c0e003040302e04d400380d5400b00d5400340038800c00109141e0042280b40a40c503060710180a166104c03070040d184d07030455100094011501c6501003002841000c0580f140c3c2901d03261580c9004103c0510841080064440d001e00c2d940d00e0324012110300c1c1c00d00c11401a454810042c60500c000c1c860025214495040b500c05c001d45454171846059a1682c001d040903580020b180d803990030a00e4200b5401504030041f80c6d446854000081111092850380404503988983e009455604550340ca1481c212204c105907001074001d0f1088102901c3c01e000355204040342002503442d62314040c20004243c1e41da03800030420455407107102c84425071040c06101540e4094818410400200c01e80d140140340011244005000100621128411220442d405000b088009005c0e0b0070762002005900b045030703400c1180303111 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 654354046 1250 654352796 654352823
    0x181b1802071e03020319270308090607030e031c0801080a020d08162004140c0301060c020303160b0604060611060a2309030307020d050309151017010501060219 70
    0x91000030302d40b80718464410b5a0030b1152005854a612a014505c070010a408481c00c540c01c0d2480c00221083d000584203001010b440c2d915041030701e10403000f50310700400c030011b00041411301540c81e000e40e201001c0c040700c80300100c5d44041c0084400f01d01d1280005030080740002000c040001d220703862182c0042c01d9110b2a0320710b5803811100e5100c1d242d2034041d136425101d01e8001c50340782c404203008402c40c4050325140d480c064040004449a118009810303581110501c01c140c0c09101c2643d06481483c1050800b00e4041d00029143d030040340b02d5400742c011268010740401021221a500a0509072030601c0026112403050b15203070800064140e07154071040010340000056040004864481e00704030b00950040400302d4502c002c1120784004c981d00000c14404c00560401000e256400d503803409904505100c4021511034440420220303004007084080742d900500300100000404909890710070b15500c0b103001d940a84004d11401000d4014803580501400d1000e203140092944860303005400c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 654355296 1250 654354046 654354083
    0x1505030109020a3c0f17060103060806190c0302040e1f08030a05070c0806010b0304060e1c0f0f0503060d06090614090307050d020718181b180207 64
    0xd4020b070003044100122031112091507100c184448880c4d5035060980c40b0030900d00001da007524501403062a00300040c1c03011029915a0001c060080d141c041c0309002040c0c1c8a03040100c0140c1100e8220b500c0134028403051285140d00403003c6031020700b002c01c1c1400240c1905200340c081740154401c0107440302c5803c1c00540f984d01e0782020f02d400c00d94142c800d5062640c80d17121061541c0c002000410104400090b400700303001c104030b01c0000a101e118000c1c941581000395403189404080c0004101e00c3c5c83e41c124558180e004d10240d0a43d10f5601900c04407900096801488410004004008100d43d10300350040644154212441010094900c9c00ea040055842100805e0138901c2950010756070750b5441c0c0514280b20a041c0201082c0f0021501c983c40c034201142043c18501c7c042081d50b1210b0002c2145081070310004c810460784150005200180c04209001c00141c24001011101309034559a03c5c03c403034a406009840851300500c20203071403940420124494104050100ca0807955562100f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 654356546 1250 654355296 654355301
    0x1020316050723150c04030201020a08030c160f12030c02031801140d02030f0106110c06030604231008070515092103030f0a0506010c060c14030117071505030109 71
    0x1054415104511101519007500c8070450314031030000c12940044c0040c00e06801e1080c40f4036000f403002d260070f0f0300d4945542e0001c0d54800c10420010944200030000030f4100d2070741020741b60301441003040b02e0101602071401c001c03903600b101c20440305500504134100102e44a4410f1209a400a8004618020304000348407031035141d146640c0e0401c1410011800c440901002406603003c5603000941c5904000d4203401320010142c11141c01c1120320503106852247c00100c91038520416912103079030b03880301d001142c00f42c00b00b00600c0400001c1041d43c0402d800e0000490380c4030f0103640740050845a101d081d5143c1b540854405c450348010162200300300707194840d004184030000202181c2c0614022100500c2100889000140b6a0400f00030072400404030b88201f03500841d001000c104038504000080d0000010500142542e50355255900703281d030181d0110000d152003056000d481e503a4030030311411810102c0312042268080e0301400503500000d080101d542d51031948406040d42e0801c40a50700 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 654357796 1250 654356546 654356557
    0x10b01170a09050304080705120d020a0813051c0302010e010b0f041d1002071a0f16030b0612100e100317040308160209010f0b0a031a120a140102031605 67
    0x54030703035a000b200000840c1040140000e003120805041d4003480e204c10014500300c00c0111000c1d94000039440030480d03a000c1801c411060b4070205060701e80094420401d024411034205076080003034800f8808504c1401c1c01c020290500c29402800082d503641109820f0300d02250705036800c200200c0108810f40303096002380c07142107101c0305041c400728411900d06240195000b1803055481d80005d1903c203204003407203000c00d1101c074034410a1f800e0918002212483c44e0080c0400f410301407480080b60224442e404c25140a10300130300c090345403550108811007001058400c0c4100a240f42d20004448001b007034114880c111481191050925584032540340b461500c0c84416034800070480800056450005012100103140007000426843d02c18803400500c1a0007160351610094010460031400070210f4a035500c1d24540480c0f41844a502c420118011b070005551100003408000300d480c10000d00d00a24a0203400b100d15441ca890014900301c3c4801c1e40c5101c02c86454410610006c1e005034020304 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 654359046 1250 654357796 654357811
    0x181014030619031412040e070f231c050408070f110306010b030103060c021605010c06020403020604090c300e0c03120c0c1e040506010513091b02010b0117 68
    0x1440784421406241980785800441303a0a210981c000d407080e9040001c3c2c2c0e140d08221501c0c0e49880e0a020000b010000c3c020a6001040107280d03103103d04510401c01c4009070114281030680068418444255070703004015030304504403424041c48450861800b42c46d0007160001032035031a00c01e02c0c0d280c40380c94407254001640c00350440587c5102e00d4404116190003040c0740414240c49505510701402030340c3e03000d441081194000e121990040d458040da0908864007402d044030074071460714200c4045c0c02035900c082c0d841000400c000466440682007204040c1c880da859070404056101075404070780c003041a0500061002104903801d140540c00100ca04118400b00c0b6888030303d01e000249090a0100443c202190201c0c0e4401882000c0000d0510120700719800c0340041c0000050072005042e80b403031244101d440c2d0300450381c0d5900520486001007004501c070070700541c480341014090a0032000c62500d08244c01e004002d40ba00c10311072040001d4059507100707514203107803410a850703110280149 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 654360296 1250 654359046 654359059
    0x1e0e0f0a031208100e13140105060901050105340309290f402d05120a1109040f0b0402010212040e01050a0803030c19020a080c031810140306 62
    0x115152110051241c803404039103a900c080e144552806014869100f1f80e00101681000280955641c800105c0c5065402c02e01c0d04c0d031f0700e81480140c14200c01250604402c40070000f0003803540440110310035800f605010741c482038402692858041c510f1460764620502056501d01ea0700340e800c903108000c000c140d503034401050a012030300c512851801c61900c40c0040c040e61703a00070326030320010700e201d81c0310035400406011140910b0002d4120099a00200c407031a000030702a1003920207490003e410014100183c2030028045440c450540e03114400344060701c9503c800400410710340f0308120810711440c0c0c00000488040c02d1951206603101020340100d05501a2161050251034001c2c040c00086c002d082032030030254074080034000d10b0401900607036802e400c00c10030440d491070368608031903a81c28a00440c03001806404001ca00700140c0301c000824a010018000754544800000350010404100400c110404110200301801c1c2d041c86d00540402d010710000051165240c1c06581e100d900500700c1c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 654361546 1250 654360296 654360299
    0x6020405060d1d0105070c031b050304120b010905060a03080a0e15040311030a050322090f020c0c030d080a020d1b03020703021203070e101e0e0f0a03120810 69
    0x801c03641010b400806031035558080c04102c2c0c0f81c0f10b6403010410941200030089030621110041095400410140c10f0102d034841002080980035225440c40ba04002035a44417a141c15208003d58a00c5d0401c1e1880a8400c00204424200c3d21480d03004840090083e41080c1c5103640708209904040c42c3c803001d02c419403202140744d8032000b00000c0d04001c0c949034a41d5a50442c50310305c0081546003880d500071740c0700015100001d0000412102904064004c08000004001d445c008404060300201c41aa043c008402008081074000c0c0410b80000410b8a09018500c0e0174555500e5a4950400000e0340705804100d4901c00e560041055070341800000c40c1d0b149071201c11000f454190409000044d07070006450060550601c41c445c14105469159031660800206c010b1000311001a003601c6040d01c03180c03c51760039029104030180c0c0025190280c0e015248098041e04186281c111240203141e0079410720314900c0c1c5400c0840560368840b500301400c00310584200d0328550010240815010f08010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 654362796 1250 654361546 654361549
    0x60735071d0901090f0e010b0906040207140102070309031101170a0c0309061526060601050f0702120706180305030f18180406061401120b010e040e03030402150309071206020405 78
    0x4200703000e01319000c0d003c6000710140301450304603002c0341100321590340f41c1078a901e1590b03035041c9040d400402c21100035850304c50b40e0806002c040a0f904c00c0d81865072000071035404040e005000c2c04101c82c05092124030200301c0c400103444c40c0b012040e41080711746103000086c4a08440340e11501c0b25071424500040d50240a43c0d40b002141c1043d40c2462408400303081c05c220352020803c220b0a0054400c070010401030784a0b10f040c0d9500409000c580c1448008201000c059085005645059800401c0840520881c1099940764100c038010400000c81400d02c8002c500c610608000850341d21800961600b04401030704040d9801000440c1c81107124001ca104190703482d02c1c0041c1c0710386070302154011b49007072900d000350031614241c0c41105034030041c42a20b090b40c0e800c002c0740d510400c0c0346040400e21300200e80c0101ca4803100c155100e940640783c41e545844071032000015600c0756109803009000201040e070a81d500c0c1c04120f9280d91540c0c080c10081c840034900008403030040d4030408015003003603222070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 654364046 1250 654362796 654362809
    0x110702063112050c030706020712050a06060909170f04090b270f16090303050a030e06010b070b0604060f05240d0b10030b03060114060408060735071d 66
    0x2e000180301a580711140c0140201030180d50201c8004900602c0c240c0d00d441c00207925505648200181000034008420038000180901e901680c0c0c8000100300590f00c880c0c94000400100074259822203400200310510001c2c801180c1801c0c11021160b03091070303e0301001c3c00c040d0161418260304880204611001c440c480d40600340020340d0724200e4111481c0c03080580038000301c0103007520703110640341104200b400e41040b0004c094070b405150a5564107000801500906507901610485203d810000203c42760b009000d00485c6124a6040c000c46e1207040401041d55154011b0b0200f51080e500104828500164440300f800c440c076030004192448e03840390308a00e401c0903104000c0702e61a059200b55514200114042c2c601d4141010007440b102079012075552803050080c244000035908a444065880c80301340c50040490101301d601501d40030000070420381ca4200c1c0c41443c070f02c00d9900d12054014040340032105440d825150159540c5a0000b25540c17200e202c1d0100c1c242d104000c48485c151210b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 654365296 1250 654364046 654364049
    0x5040b0d06050c071406010b030a0f0902190602010f05010b1b0a1a060109050d0515071b08040e1014060a110a0b061f02100c050c06010609091107020631 67
    0x16802d504c0b8009802d00541101440c0d40d8400c60341c000f480140a021081e100303903900a2220440041c070382c05040d0b02d00000308041c94010354010b034200091f0400105041000c400d03644180d000344242124051200b05561081c0100c0640e01300a00c05203881c41010186000c2c5880380d41d04541070740d0f9194480000c1d0440310b82c201141195841e0400285507000900807004203410740c0c01e03c19503441601d650340c546400142c070302d550300644404145458402c0403403001401c03083c45540d03c088010700d031a80d019030244c452207040400200004850107603c040084c00c44503400032030220840800200031799580881c80b0b02061007122032185443c89410007541f440c1900c9540a07049a040c04030030840d8114810b00c0903480e01c0e400c007512800d21507010545501c41a600180800d0850f03040e403099500c2d00400168000030320503070000144241d070000d84c6000b01c42544600300300921040c0000c5c03100d44292180a504603104220004141810f120200c0d900452001e003a00b5403041c0210266030315490303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 654366546 1250 654365296 654365311
    0x9090e07180605091b031512030a0215090d020316021305090a1704050a0e0a0906141005010c030c0305090a080303011d06030109020d0807050102120a020d0f051005040b0d0605 77
    0x140d007024066402e01d07540d02c9421251000c0a04108007881d0405017071031000030f02646200d074905583e4130b0b1076240c42003110603040b400e00c1680d03115206604002d540340d40c0d07195203d0180050001141e5196004284281c2e000c166034061482c011380e48410311004000b00b08101e800c1022112100d64064143c4540c6000d102e104005c0d00300c0c0c140d18200109001a0703841c01c2c804003407040004106943d0b03448804c00c1101c3c0e440c202c0402c42e0351380d0500d00009000e9110058006801d185c28903084210700c4e1046403054492400c4424215200c60045800803100d4074000e0110301d200035540040b80c044e00103040c80000081c6602c0c0c0040e1035000c818155002a48544c1e800390038444104141903c0480b070340e610000c00d40c000c001603000780d000140c25024802c006490100c0005454050080070340407140448240405070000d404d124035038600a60068480c00505458407042800035115402680e000da600f40301c4280c032203420300c2c00f040020300713400741d5088e030100390704131424009011802000d00c110071 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 654367796 1250 654366546 654366551
    0x5010c0906030f060b04091d0a050a0201021002070b07140c1605040e0102032205161401260c0d060f030605011403190303090201170a0501141009090e0718 68
    0x602080a426204a4a51610071a082c10030601801c06100191001c44082c40c3c80414905001203044014404034888c02e04603008584012051020000300290382d98401e03402c40b4030100da0b03030301660124000d41400503d80c016020204070040d00ca81101c000c4d240c01e10a80724984280c10138003526003612604c0c100501844c42c1000c100624040c8a64070317000358440c00035807461030008014004c030b400c0d10451701c0c0316042c050601c209024003003207200704071750340c0c99034260f07645840e699a45141070050320304500084450200ea03600305104402c840c0030042c891968000c07174507514005102600280d0701da1b180c03182e46030701c00996450f0f152103850055001d40710016641d410404c0c2120000d10001d1200e0103540f0a8141000c0c810121050a21154062800040384030705c03440120b03102002065519400d00ca000140300030500e05904c0b250407a541c81c0a010013820107034042c0400784075504840b134085401401d081250b090240c200404e80040342c000c2c0d0b8030403030b107030b41800021030b07480c07000d04501c0755 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 654369046 1250 654367796 654367799
    0x140f0a02011b0903050616090317070210110604020d1511090f040e0a03050903010204050603090f060a0b0d0215040e011d15150a030605030322050d0b07080c0705010c09 74
    0x920b500c603060030000c42481c1602c0c2d00c0341540c84032940c550020306611210415021400b4500740b00350007003405181d00058980801c20480b984140c2500000010ba10a4010700780c0034a52a0041455010000c0800042d01d5181d60725000c111403c0d0704031001342c4030801e00740b081d030034160100e1203201403040c68003461b192100250001e002039003501040072405646840703c0d01d041900009240850a40d06182180d9a4800800070a01a0041fa0b00c5160065008403d1041118011462403201b2294003702c4070680e03a07850f081025982e00146a1340c04c01230070044040035080140c0c0c040c0060754910000c62401d030f520a21009440801da00220030a03540da9000310030f40c009846810303040303c00602c44001c000d08441c0000c071710710080d00b88c05540500015405050502940140008202c000e060701d88409504281707110f00e0a0b0710807070402c00016a40049040e15000d1a00c1c0c5145d6001800f105c0c4035600d4080036100000081d05414030007806000c07440000d44240030781c0d02c00d48103c3e03566542e041d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 654370296 1250 654369046 654369071
    0x12060807031e0302070510140301030809091b1c140103080702090c030c0d020d0b0306040b01211716290601020d0e09062202040608061906140f0a0201 66
    0xb4650071019400004801d2480100342d0026155096a1040b40c0070402011900c0c016598078502941c040380000e000301c00003090188241c00f6102000341500c210354166240d800c4c00701100c2c1600210019210140001001448a00412208c041c02840300082c1d003e203410440800241c00d9100700c62808001501c4411424500c044a0f001080d08a41e83d0440c01e10f40c1070444103000700c0c4c0c840d840003640403501d008203e40c2038004084100019068038100d00b810300381110030b03582c2402110070301607005141100502501c0c0d50120703000d40041046c0e003656514200140294402c400605180c0b41800928020400000318048d406690351400c0c0c1081c0c4900c0c01c80c00c0041e00003004207041d03400140c0386c501925040f2402080440c022200c5086035034421002501a2006900c408141280e4411a0144220a500070000c3d1241501c4039507a55542d10100120359910f41c21030801440011820400680182c14109101c0c1c103d4000a00341650306064030134940103c00300b000181e44a04c0640b444 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 654371546 1250 654370296 654370313
    0x801020310081c0804030c1a07091a040315051f090e06010e0f040209070216060504090f0603020a170a080c0303270a03050919080a0b2d06011206080703 67
    0x2400c0b070b050264019401c002c80a0300d051130003000a8144425180c0301002c011200e03040c4082011400e0310101103003002003005014031001e01032070b02d0045414505c0d1540b00d900405403001c60f0352001d4a140068980d0503010701178035001e00302c1d0441c000d0510501c1f8040108032282409050300d95030006943c6c9040e0f00300340c070304803042c1c0c040030059a01c081072280c4125810003427540590151a50754054442c0d400403032400c0e603c0310b40c00803901a85a8003082080e8041c00a1040b01c480040034010441c0c06001079049400d1484002d500403064001000405c007a0404420703030295040968500700b031a92a004044da01481e07484030560000002c001a5660740c1d0750303050000119040c40c0100d004030b03d054942ea45002c00c409018070002060140c81c59585045410910602403102d0911a03070f01c01126903900c21098003100d440b004a40028100303a00c54480400c000100c0b9189520180d030455801e41001002d4646410003050742c0d10084076600b240280002418070310004c2c5855442e60070403649 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 654372796 1250 654371546 654371563
    0xd0f021207090509041205090a0e01080a05060f0c030402010f05040305010f0204080f010b1e190602010606080a181205130e01060f0503040c1a0d15170309100315080102031008 77
    0x4640603210510000c5400307031b829070015101d0340c106956940d03a00c000207000c9140f99071298040007034250012500f039002060300c02812344107504503907442e1140006e030010702500300c60350125460244002005584500c0c0c03548103050341400c0440c54680c03a80c4420742516115400000103030f400203001c0006560400c14880a0007140c0001c0151100740c1000aa200d02c603030100980a03610001c03142525903400b12000c038411808007854010540d02c0c0f401038003070000d074880c08000c5400500021031004c05030141d04144030340e024201003020942d030b0310903110300c0d04242e009040000a010b03d903080e25140d00c80d64090f202002c140d080c5980b6110000340050105031a42003048014802e0200080014082105940400e030241804032201d403a40c00c40c600030741050026040c05c1c504c407018040c103500c4408043c0c450901c0c1214078450f5602d540e5560b8402e00e8021a000410324440302c0245101ba4403034508000b882000e03030810313552018080c2c00d80c2c00645041c0034040080100300200c8030100000030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 654374046 1250 654372796 654372799
    0x21e0d1a1014091906080601030b040b100b070605100b0a030e0601090b09010b0304021c111e03060a0c0e0612060a06090b25080c0618210d0f0212070905 67
    0x2c00e10140c1c0000300d18415400b52406561141c514070b1039110641030740144020b0144101201d555683d241405a10010140d230140c80c0407450300c0125200850f00b41028041e200811110b619100180e034481c402408000c28010410703000382d0000c40c204507254018802e14103c2d5402150f5800d01401550501c40d060b032103c407405182911200741e0303440b80945c43d41181d014210550b145e64660001c603803d20040822840151079081210041200c120581004018181e03a04082c0800000d000c0520340b0020801e242d160f030200300051042d01c401e41080f00d0804240c81c051000031209004590650030500405940007044010419181025501180200568a440030341c0e5460250140c089200d10b0851a0032070803158501d0044801540e6207481c80f40c1d214003038a6841900c00c00c2e0a854100c03c1d1805403200f82c50a00800c0d01c0b4034000cc03160400c10707030002c10b045020080c0c082c0d03803400d07400052403007185903c803034115981c404039101420f04c41e40900c10071641864a018010415a0240c00ca40d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 654375296 1250 654374046 654374069
    0x1404231908030a05010b131a0c01091b060228021207090e0c0d080f0c0a02061b0c03010905060106030903021911031014040b040f0c03051f0603021e0d1a10 68
    0x107035038020142c0b400104e642c8e40200744400114217905140ca0300c1401c0600c0840c0d828400c0300c1d03080144094683c0d68007181c2c0c1c030707544e0551900c4800407600c0e42a840f201034040c4100305804114002004119070f41a40300408a48005e00c4d03104001d17040011a50143c003105903a000b821220400a00c01188203081c100ea100808180d80da0700d2100c0c500a40e003880e004002c001c111080210781c2004041549a00144030a8807556070100d100e00b40d0380008d42c141140c1c001e866000440f400e05000d000e013144d520002600d183d07820f0490860043c0101d1000b41c0c110702c98524480300c10406921100d8042d4003403d126102d104121080c1481c100c038491b18882020300e00082440074070884060703640c120350b1010b007101050300c442c1000000185042005402c045003440000100040050704c184804021004600c06158082c0f100741110030320703c0301a401031001040c0c8041541d002a00a0a0120007018141e464246486224401d1031081d12640702c000101c0c28841c5030380346e60085c4c0004200e01e6114 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 654376546 1250 654375296 654375307
    0x21022e061502010c02240c13030501150602190620191403070801090f02190206040b010605130510050f070f02010e2209050c030a151404231908030a05010b 68
    0x140310380107910a8001b40224100c0042016600840225080140b103800404141e0740c90f41030141c02050b5407150020511124070001a0080c000f11301035000c54583d04425199401d80d85074103000d8030301e00d4505880c0290749648404070f100c022001d0201c4080c0e0340b9001d6544001c8a80241002c42004000d15035508148104150b0540c446030180c195201c00d03002240b860b0510341c2c1d545c040c1c000e18107035403945000820642005640000d07464492809214100f40350f90781c2d0700082d00c0b070f4440c48102d80280c8003048c106009908240d17801c81110207040ca0103514200b65a009100e1640161400300d0364034144820a100b50f6a1081e00030110020031580000149600c03020000341091002a121100381c0b92038004042c48005c1c002d030702c1d18000c0034040d103481c12014a0030440c083c5540310074030015441c3c00300004510750400103880c80f895005809044130040c15907041e9601c0c030146030111844c0f20700000c0b00c4400d01403460114405114240751a00e0341003003c046815503105800048003240144070307 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 654377796 1250 654376546 654376573
    0xf0f0f0f0b0d0807060b030a0b04120f1107061d0603090a2603010e090c030d021e030c070605031302100c150902031906230421022e061502010c02 64
    0x103d50740b4a6202900280112844001c88d003030070303021240980784018200c1040107200c590902c0700c1680d1400c0c0c0d40d80071542176400b4181c50702e00c189480120180c0c4403100a004980c0140e0a50038425150038101800c4100c60000604580c01107078000e040741c100c03840c404100000300b500040440745040b14140b4040743c80c0c086101500051180000150003500400e00704c0348140720b07042020f00301405841030880c030301c0b10103552206180488190058454100d40b80760b003010082e54410700300301c8080c102c040e00d008000c5a207a08081d240e0b020320312422061500682c2e401174810540e0a640c0c441507800a800d0030720056214400c0d5040600500b420411401a50003042c0c04608a04404440c01290b2460070140000c0805840800c9140c1c252240c4c02c0c8140a0560b4092245114204480082080c1080c903840041340a000b4005a07008058022070031003401c04800714403061000d040c0c0a0005003070307200e054031010f07800100c40704020455210115420b02038801609140d000800c0007410424 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 654379046 1250 654377796 654377813
    0xc190501120b0904020d0614040308090d1407030302030c0d09050c0406051c15020c061317070b0109020d1b17010803120a09032708010c0e03060a0f0f0f0f0b0d 70
    0x44c00244a81103a914a008018199012602e4007036160b2000c61903180602c2d020b0150b903000c2d5010307242ea01c59542c1c1443c00314441c01441c000030b0324102b0071034205a4540d9050380603410103000a40b54000510030440c14503260b11604c16100c1c014030081100f41000e1040c0421160150800c900420030507581c0355981140c4003859000070751242104485810f120100b90003130080b421844000e0003070409224102e01c03420fa000389024000c032003410240190147d1440e0510880100509103412140100302c42d141641c0942200300800c0008107290504641a13060760301c65642110100e10561030360385412030241c032034502404800740214a4418a1628688100001030400c4403640d210300004080510940401c8106951280546080040800c00f2803240c1c200c4d0050b00043c0d8079103007454030a18030414100c0340000f0064090081515140f41d000003602100d944424031540f41c1e50380241c40307900361280080b40500c0c41d00001d42d140100c0c0783d4109807040b6a42c0ca52084104000f20008500c0c0c44 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 654380296 1250 654379046 654379051
    0x110a020a1511090121140603010e150a0b011701030501021e0a02070306090f05070e0411010e1c06060b030c04180203040b0708040507150c0b06010f021207050c190501120b09 76
    0x2402c043c0185417202a00f152040c500141c1c441c41d183c24079901d0b07000c0358961842c0c035010b19003c43c000d02101d80103004076079451900c1c980c040c06114460002c40c0242c8107a502c103404c10081890071701c0200d1580b8078400751003407003a80200d0b41a035001946c6003210031000c4040f030b651101a41e446113814080c42c0020340d6140c107800b0203403106a9a81000f0200803c50a00c14001640503003550f17085a078900d82c0160103842141c0c00e807003001e039846c2c04030407940c030030018440d194400400030311010240c00041c510300314041008403021680c4e1600442c441d03001001031031042c01d007503545a40d0341d420401f107a0904403181035014103082c01442404006544254010360113503103450306949640d19820068505088d9610220f104ca8403000340c40742240e40300250002c100e02030392464529031102c000442d50744030120b07a8a40160060f8a0094981000c40010036096008100b150b035500840310000f0018684a0004060a94001030402155801070360100b03082e140414104800c10250010610001c2c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 654381546 1250 654380296 654380299
    0x8090f06010e150301090f0303240315180c0e0117010621030212030108010204051c150209010504030c0b090108090d0819060e13050c0d030e1003110a020a151109 71
    0x141d006403c0319890943c407070a241c0d034000e40c61456106150801400500701d01841d03051601901480c408026078920444084a510550341301c20345140c1001c100040c10f032018001c64507003d0825010100c2d096220440250100c591010300315454155600244070b40107051914a9040c070b60100a80c41c2c3c883d0210381061040c180540000c00d881c03034103d041072910401600c0b086d2011001082c0b400c4154050000d540301607500602044c4100e40f4280c1107072003079800424072045994044860035a81d009000041c2060504c5814140c50b6510441040704540000041120104a170615907901000b082d42180d000340250000040746100102030720001044c0424625225004591541c0240c0c8480000d220f1003100c80d040c0d0404298464103040200c3d42503569120319403a44200b440c2245412000c60b43c59201c181c009940102071145412600c0c40c51014075644600400040b2040300082000781c0555010741008000c52401c81c1000403c0290b05a90f9440d201c1401140042081141c069450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 654382796 1250 654381546 654381571
    0x905100804120e12060a110c1c0509030a0807170c0706140f0d020307030e03030106090e061908030a02160506040603020c0f0118210507022b0308090f06010e 69
    0x404840683d001030000c81d4041e00040500d42c4a250300e1030108501740603003030380c480c00e1148914001d0701c1101801844540091b6411264000c04d50000d171141000c000d2890f03061180c18071101341c0001c0c2c00c129007008141d40c0c0d010b0005440301002808014180d001c070b040070b44107080c01c0440406039540c9016010302c0c0c0c28848a449002c50320164141a141407420780620705903030380b900d404428080d410680310100824286400718059810210950703040e02c2440d5100e10046240501d40b002208029041e03a0304a001c010b085d4507009400002000904650030045645880c0460b00a103400d07400f00741c0c04d400e111841420302c842d0f0b5507101140c2c12a1801d207000740e11121140f0149041c482ca90066005a46c6811720915101c5081d480300703420319006070368800c411150f0f410b40c0c3d8070000f2250611400104100074a1006280410400b508108a0484182051501c0ca00550f81107280701c0f041e4042030120b010032082031000c008212003040084041c122079491714140000000c00540341c80041e07103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 654384046 1250 654382796 654382823
    0x90618061d0c131401031218080613030504091113090605030a02060a030e1f0609180215250b060102030705280215041409011d130206190905100804 65
    0x100182c000c4101300d0741004c0e102500303582d02d02c0e0000001c1503005248000c0348a0507480f05289219015071700c1110080e001611141c0d6443e03800c1807110342444801c41c24018180400b10303043c1c0300c91281c0b164000481d20102d0f900c0d401001c4540c1142016484100c0484c200f2400784860b03100820701981789641500c2d0745454040020094026022402c888075840c03107201030707803c0c044280c1c0c40032841d89401c8520030040c0030384481d803060541e12800c00250340c021813084120014100201401c084481c9102da2908103c03040303103000d403080d803d0310b0310300f4001c003001c4416028072000941094014909000941c07401045540f2030f03071903891603080ca040b00d0002d08945c4404c0c1e0080391400b920f20340d00400008150301c201d001c03120142c1060144444403064041040b4490520500090580307606080c4c044418021001d9803d0340300008040c4001e6403000d1044900503201d8802806100119001c2200c00c0d068102006042260a40c0881d1041d499511603102554100c1e480c250004d420045811580 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 654385296 1250 654384046 654384079
    0xc1c09030c05100f0c0507021c05070b1305040c0c2619030218010201110f0307051215040c0503100314030921010515010504140301090618061d0c 64
    0x9403001d0058154050100d00784150038841c0e01c801040d04000c41c0420080740308001c00c0b982800b9805009404c0241030190b0f00181c0c88500c1021080ca03c920111030203241c41d14040106130b0080018011207659050301405103240a01400030600c243d80361140340c00465072108214515000d20789442c101c41000140710082c2c1803800c03071b86011340000700100d1300c402044c80100254481c02045203440c0c21b142d061405588103004400034819400d4542e07040150210000340907620191080042c0a810042e04000e0344682c0c000f107110300c42036102740007010110010700c81583c007407030101c034100314040003006490b6070907100b41019a078020460701c0b00300407503500d054658859070b400310b5806441c0c0c82c110004d0340e842025005100d40d109000f030010b40c4502c4c11b0307038108a086503051070100700c040c803061020900345d400e4881c0641f0300400108491240703490b0301c000c0342d00300a0b4070410702202d40707008070522680d40202d0000e011518220007c0c4115400e4036525140804400740c4101040445400c0c030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 654386546 1250 654385296 654385307
    0x30902040b0411040e010503010e0a121e090501080f06030631060e10110a08070e0a06261003020d0f0602030112020a1d0615040b0c030c01050c1c0903 66
    0xa011000e841004201c140c9080c0b10f1103500140f003400540c00003034001007610705060040c80180c1401030014050091a540d40d000031421031011039041100c00d401c0c0d9040c000e9212510803c409080c1ca90002042c209400184000c0d00100240009502c60060240070307100081d40c41ea00c00400e0b0b1001c1c200f07200e03011032903155803004800490503421155440c0184000e99100c0e40c2c1000303182c0100c0d05c9482444c540070b020b4807480c51010007000024400d8400090042d01d03060380c00801890860001b20002000900c403e00540007a0001103116044400d0845404c000d46200024140351400b01d00d4031541b40e8121341403d0000034054900810b2180812603920502c0c00c1c43c50780002c00395240d6841314160707000012000801c1e80f040c4130061001680500200e04031a04041c1e6000020b10766a0728014003070361400c1c14400480380b50040200182a400f01300207440c1c1d148081e40507660300e0501404480c2900d40280c040242d885040020f800b60134a13814080c00382180020b00032031a42c4450405880 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 654387796 1250 654386546 654386561
    0x5131401020f0615100906050f07021503090c0109050f06030c22030f0209010f0302060318031b06060a0e190b0402070221060f16031e0e06090c180703090204 69
    0x3003900c100018010040d52031130381c2c802c8065042c1d0301183d01003c0600c080f9600e016506c42c050201d00b08021200310790015030000e050450000d005000758101008642c511903004440d066065009840f811b01c140d0f030f00401203402840c0403200c10300c44815400000b070341480058000424580000341c0103c0000d0243c28a80f980101a81d07078000603a0b407820980001008450101d1103030150b8070003c10a013449d00d003084152038001e81018150382e203101003822407032540c0c1056101131005100701e040c00c0d00a1204004d01c2a05007015000c2814804240003015009420072804c01d0059010081c1307003110100800410b500b82c03031001c40d114803140e021400910030040042e400103840c0c2100f110910003071313042c03981c000a55000c4a002c0d81da031080040b000f0340300b03541810703078040f9900710300c0c1e5401c0c4a500b10460342c40100e5000240c4102c2d840c1002c0c101c41ca039075500c1d0360030780241040042caa0024065000444820795401c2144501d14a221480410091081c0e0525540355154020754403182d01a20 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 654389046 1250 654387796 654387823
    0x13091401080303271c080708010603180602090d0501060b301f030b07110d020f121e040905041a040f0b0c220503010c031103040209060d0b071e0513140102 68
    0x901c21705800b50040202e04200d9405001c6141940005a1144644255104000c81a0303000081c1581c1c2e41c0d0b00c3d00650b12503200a544244180840302c0800c2c1c0030711481009145c0c00071071702e6480e00381c4034003214a0500707844138010310340f6030782c11468456122000259010700d4008200325031808111801031450050b400160080c00000c082000d16604610700d02d50700800c6504481c41d100f400d1008980d5152000d003900e905070081007903400050406001b500e00f40403452a0746869020080b2643e910750055032008854075107410500003480f20380802868048150420b203106441c254031a92220f1300325001c010315040c00d19000806800000080e200d03408010410f1080300034110311084404000303030082501c00c2d484c15140b0b0220780d0203481034180740705200740440d00b140d455408005180750000d01c440c0e088a681000400003442500750030344515110b0b00d44145500c0e0f0042c103003485811040d911300074454100010020010405203901c01c0301d004001d070001c2c80044400403414004480c5036207 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 654390296 1250 654389046 654389083
    0x60c0a050102071e02150a0e0904050c01030b0307061409010306180c030e0d090e060a05030d03020c0d1b14390603010e130201051309140108030327 65
    0x10403806400425410f401410b0a2040603a090421650b0075402c10000354400c0400c5e00310300c13941443c040078101841203800c100c8c40c403030070310340100d0440340c07044034222500e800c60f5050101a41e014461014607080640080a50508201c409010320f03204000e09011001c0120f01c1500c0351b842600000042c00004400701c06c8040760441c40409020345e4041030340407908064007032515240000c0c2e40000002d85a886032010b51924400d42c001c0c01000e40401d4124442c410040380d5520204615030b0226225a00103030b40720b05e03680429060100404503901000031303601416662108000030220f0003908034004c90400000404078615005c1e20503020848004134440c28500c0c0703006400780310101e401120f10b41c2c1102801c402040030520090140d0300308000e01502064000b40f0302c1892440756841030411510340030b440c8000030380c099901d61216a015446031500d04400080d005d9080c014a0024015429030401741044507111b006226000300d0030010354004c0010000170444481110030441c5503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 654391546 1250 654390296 654390313
    0x5100305061806030a02011119050a150504030e100924020f032a030403062d3c2c031806210a06060906110318060c 51
    0x19000c0c0c8811035a041c4281400e2140d19180440007026500c99072004014100c0000a0b41c01036030300c0301079015001200c3c0b062050040802061040c1254038a0040300200b00c038000d140f8290fa05140d0b000e41c10660309040c8414040083e402c407440b6040c0c0101150003c1c88070540c0c1e0340032103006c0c407603a000c2010600134195804052140a000351150134550342515102c408100b0150365038401c09080c8c030740d000008441c240800c0502e8020718941340560003580d140907680d845000540c0d01e9010300c004007024031900c0c03e0301d428a041c0907000c0c01d40030100c10702000000e00048801441c031440380c40c0400c020041264809061252180207040004030704205409024043c0c2c182e0a00f40118800c0030500e008070380036400d200200341c518100e0f0840100064403074075814464a0382080046445040191721081e4111480f5042d00d480380c080c108001407801d141c40001480d45546501031404e01540112043d107140e00070045500000306500b8860b003122611020030000d21598100810a0050081 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 654392796 1250 654391546 654391579
    0x23120c100e1804020603130c0902070309090b100c030e03070909060203061801120818091602060c0406020c190e100e010e0f0a050705220810020a020a060b0a05 70
    0xa04942000003920320740307108500841180e40b48807064a01a5120381d040c400145800c1c5650703200981b841c0300d80c4040007001e54070040310b01a608020001c4010400400b4140102140361042e00800c2e94221075250f5681c41c07820014194140b44c0401404008400c0000740e01502e0400202c1c005081f0802c0410005120b41082da0003074009454103841800740140d41c0c0380822071030f00e41070306a600101003007608a44691b15900360b540b00407101150781e1201080c038001d0b55035408141c0c0c41028094120308100602141c02030615400500c0030190340350a201c00c3c041980e00041008840d98141d0310600c0c941907900500840c4003040c3c1c0f000d0414000d9038100600c40055004180407280e190855252590700c920b081c0036240d5007101c0710000c0300c2c5680c0018100d1072aa40005402a000b030500610703101c00216406200c01582c5072003c1c0d643e0103a181000304460801618007054100c601c114100303500048001e481300380241018000d16114100341110783c1c0ca20030305030b000f8003004040810092015a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 654394046 1250 654392796 654392807
    0x807091d0102070309140f040e01092f040b06090607081b1c0503060f1c1110020c0d031116090f050402030304050112140f090723120c10 60
    0x5105110300102008820010405000751aa9150315480b01e0341c0e41c80c241240c80c4031609844503000c0d4440c4900381c50021030f40b00e03441454460179441001050101040c01e2841901070200011410600c1003003036034441020078000030700c0b2814211008184000c400340000c0c1c0380c1c090889800c2c0c0c0304034001070301d1f01005070034801410000880f0600100060200c42c03503644582e0040c23246100000801000c0f0540c1d44214011944608024141b180c907450305008541001c0c200303481142e5080c41c4440b81010700007012000c0f0b0883c2c01c100c900039808241200001d4698030031580e4980500007102c42c40d410540222110f00c41003c4044c03ca0308a01d09503841490000c08500c42d03e00d40618000604040c194640220742c41290098001c2d46400d01d040011642960700e078041880312541d90710303401140c80c40318824034029680141201c0c0d441c06c110100301d0900549600188881718080a07102003860351144001040030119062070452a18609032820100c400c107520781d00c250f8007203002030300b660000b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 654395296 1250 654394046 654394061
    0x90105040915050907090503030f2805040810050402030a12122a02030c0715050702030105010b0301052d061b06130606170604060f06030515010e0a1107030c020a080709 74
    0x1201c055401d40c445c0003056030020710760b0007040d8140d0010030880c0d40c0b65000000a01c21003003072801001103403002201c10b9130220380c038004940015070001010060b00b14100229842c0a12000e030810141c10a50300080e40d0301e0000c0381c018400e07001c403002064000e0051000c010380a10502c024041c0b0980302442403c0002944a43e041005420f48c1c1140070510020580c1c41d035100441c02050070318246803a0b4910341c1e071044107260421000b0000b12006071002c0c0151402402c100e6102c0781c5031b5060004001420f0201d00001580318007418008a40b80080440601000000d0301c25981e0f605c080d0a2000c003c0c103d84208001c0d9100d140d0501203600d030b010034038404443c040c1c01c0400851792a0114105420b400300305082c1c0c0c0d640300001183c0424040d40c0600c02c03803420840c001954a540740c2d00c0130305002c0042c407401c442c00030942c0100000c82d94020855481850170400f0011000d600307502ca401800343c41400f80c20407091100c00c008648464070f0f2034010b440e040781158119a40c441401001d841503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 654396546 1250 654395296 654395299
    0xf13110d0f060e07021504081603030509011b2709020403030806031509120f2107030e0604121b0b090109020f1f300614010e0105090609010504091505 66
    0x7410780c005000040d03103c0043c050300c040e6024191007160001c030b0880314100900b003a542c801042182c00c8454840b44c68511000340309840c082480d16000c0243c07821600081c2d050b01c84d4849c91620614084d40c009000c0303040030351a88400595003600340350203000664980210418920008000c014160040c0e8041e02c585e504134215111419030a10ba01a841820b950106141c9d2102c0054040500d0034409403910502d2400110b0408064a0360010301d103041102602803282c043c000d101c0502d0f45402079800c003c00c2c4100800060401e551000124007a80181c1d1040000365030004510390f000a613205001504003640d80c2103800c007440254001d000c810401c80c41061101d002d08bc2504011501c070100c0c1e2442510f0380d0f0041010231040e170b800700c4200d20840408404400000c0c04605141c84000c641d61030400000d100e40c01d00358240210000030090506102d28140c811031240e92200458409400c1541c9003601e070308509006950900440d0001c01c141800c00e081040340081036103402044840 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 654397796 1250 654396546 654396551
    0x20109240c0c0804060c110a06090f12030f030b1f0504210804140d0516030c0605030f04030f110a0b0f070503040b0f1513060906050307050f13110d0f 66
    0x11550180c801c0d840440300100f2096050000704083c070701803e5400141c0e4002d07007004076241042000107a41040e070307410040c0170071118142400014403180010740501020703010b4099140c0c2d40d0710003a001907503403c40d007810035072903001c0000140c0300c40e0040302c200320904030346000c4020481d001501d1500704d8000c0f020180ba88006010940c03c0b11011900050340140b9654681410301118942801580510039008000b04c05000c00040c0c00f041001c003009940c00041651038150301d010300010a130b5074000b80801000348284000b240d0041d240a41180e4141054900300400940544185070300c00000b48aa02601070381c5010310004200c00303440b40071106040800c40c3e60705481517940717000035640504071043c4d11002601031004401000d810905400c64410b40d54200c4000888000b8a040b07240c201c01c1d110b40007002481d0a5000380b9014203400c82c00341001e01d00380781c0800ca9810412201601c0390039940200b801000ea16404550303241c14544801d41d580e84420411005881180301d09407420b80b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 654399046 1250 654397796 654397811
    0x1c05100c18060c06050a0b0d0b010e10060f0e120f010f0f02070807080c07050a121109060105070813050312210f06090702070b0c0a0302063402010924 66
    0x110704160402c0c1c0310b10752101c983e80c1c6072507207602c4003e00c03005002d08055a620408554190382d041803502185120701e4460505604011030510707101c001628040c4030130140354013800020380140040306040e82c0c601c0c0880c0b91400d2000080e469503c06550030a9034000d44842e65207149044d04020101c0c403101c40309110301190b000440302280f0642c031000e00348807030074400303000020032410083c14200480d0013255105070700d81c03000031040d040c5940a0415110f000251200308000e02803070b4103010300110745004d020b28100c1e0010b01103201d6031070001c0007007000003004c2d20352080c68201d010140101a088680b5240f02c0320f00c2403d25403040410032b002807400761400982003000b4034004d200c1c50440da030b2403500303890388018014904800381400081d802036807008100384010402406d42c8074402c2d001000845d000e8100a81040e101a210080d2082070400032500a0103003050040c54044a030541cbc600c2c9001b10134124010400c03144e00070140079809001500b468401042d040300000282000c202c40c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 654400296 1250 654399046 654399077
    0x9062206030c0510050915040803030f040318050f01030e0a0b040302030307110c1011010b03100203012909010503090703170301060e04020a0225120c0312020d0507021c05100c 77
    0xc80240d211303613000440410114105060103c0080009250b000a460500b501c13400c4460458100300e0f401c03680101104100400c1c1648000d201c0c07620001400078441007400c060101d159000e1110b491814103807108801e540c1c40f1000c0240c0c01c41150040e821b403025081c03034540251203620544602c00090b401003083d9010a00200340440da01600038140d01498017018030503246181e1103490208195030350024488140c6060110100301086d865005940350b050080c80d40144503900f00f00e001c3d85524060ba1046014184101d48590b20242403a03501c035074030142c4041c94030041d034200800c03051640071145c001c1d890b01000342d41a2a01a11040603004140062000300d0054800b9200168000b10b0303404036903401d500e040c3c1e5541e9100800c26100303d0b29014520005802803c0c1142c004041a00410500900319034001c6004024400f074036a183c200c8500801500030700c0c1c0c0181c4180ca903085100000d00400f802102c100f54007005903808200242c500c400100180c0c085031000c82c88141682000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 654401546 1250 654400296 654400309
    0x8070e0f01120f0602070803100302040e03040b030a0e0a02100503070306050108161227020f0616080306010203040512030d0c080106170c090d0c03060b010c1109062206030c05 77
    0x1a5200401d48182c808065192161034000041064411075070030000c20005c02c0741440150321450703030504580b001514500c18081210041d02059965400a0200b4010a901c1e1411039400942c0200b010496100d020191801c00c404140000c0d403040000300000703410742d04200035504c142c0603070710208085d03a40c0b14015100c1c3c0004464040c01c08100c21007680702c85000e044041c0c001030010100041d80d0840940f8103190b02d1260807107020004a01d9101011880d03c0260440c2d00301f420b40e1118101601d10070031101c901540d5000406440c0040000781d4264400c1064400504004201041081d40c45000075102d0f072003120030700000c03402c054450380080d000c2c0a5081c126580c5540c0d203c06100d540200c203a02e000040d2036506c42c2700b0204482d007420b68900505003201c4e8007840c041d9407e01d01e0f51400b10102c9144d50001414480c1c1d080300b00d40400d0390402c12a01e5500d0070380300d162003680d0f9000095891165808065140d1701b90b00b102c560040f07040e40c440300036280f00c2c8019400c2141c0716005c100d403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 654402796 1250 654401546 654401549
    0x60a1d18040b0720070e09010b150c2d0d08070503071209080c0609060919080715060e09010605061312020a17010f0609020703080610050904050108070e0f01 69
    0xc20051020110300020600e01505a010b4160300c0c100e0154030641200c0f080301181c20001e5100c2e82d105c50750a1020b040c030076000035080500c04008000226120300804c03000801c0d60b07800d031405600400c40c0c2144a0050010407c2c40120301100c42c000844540312103500d1000c0884800c0768840c0300d60749082c1901503400a03000301200d4a98505690b200d120840d0343d012640c0201945944920388030f800a04100b000d0031001c600800035204614140c84014903045c00140089920b07804940d03a0510350b400d018044403180d070005465542c440560420604c114610098402d980c0d00e80a0300180801c0c80303505031801283c8940080c014980e0703e104008032400303056042e0100400000d810891a010124002e21161003e010442c0c01c50741c40c0c0f03018104511003640d0749940d035151900403104000e144140006090003d408504140c0282c50080c24180014491802408480c1c0400e031014007400a4802c0d52900810900042d07841d1581603845000a100b00c01041e44100041004140211445030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 654404046 1250 654402796 654402829
    0x3121116031a0f011806181d0628020c060403020106030201021b011202090d02100504031e030804060c1b1a1003050a0807230c0306070f090b031005060a1d 68
    0x500903405c140305542c0686002151031146540c840300000c1c8031030004200014040560400903092024924035007803c1d6100d2580d0407103400c0030007046440b074004c542169084c5240b2455070390503c01081c08a000f44100c0541100394800c2c44100030801d6415004041980d100f1303801d03100941041e8940400700c080d401c14050100740504201d03142100a03034080d003001d1500812600d4040c406130045507503051080040d1000400010f01071041c0064900b080e86600603004400d060341600e61401000202c0150005000c0c6403a050000c2c41948035180700419a40d421408048181c00da00c1c1c070180f0242c001c0c148003290510800080c80b10603501450204803a0001c002e44003000003036440c07503c0c5500032901254555140c0680e04030701c07a040c0c1c0f1541c0b0500d10040040915104407010986840c1c40208034800300300c030f101c5c3c0d552106a407201c041001c850588a02940383d071034000e48600c01d1000c5030045900200c0100e411050144c0c0b01c0000e52550b040d9a22141c12411417006001203c02c01950700c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 654405296 1250 654404046 654404071
    0x80702032b1d0405010b0301090c08010617070e1207031506140d0c0902030a060602011a030319090506030a06060f0323060607050609030c0c030c030703121116031a 72
    0x100c074a074000e01600d80400040c098400400e404040081e0031624281c2007089107440200c01440884e405200e00044001e45080c40203103503250520040603034144070107174500c84c01d0f420041340031a40594006038401d6401803020600c029805465030395840d1906c400e235112035045c103014400b10b849105d403400743d038000b40d00011100410410320000a1ba4054126440500b4081c0000c00c071400344041c0d8040d0354040c3c0302040c0c661034442d0007400e6031f41d80340d044071142c03043c204807a80540e00041166040e620740c0081e03040c6203107590380a032519144c41c0d1095400c080700008102000501340d1081060300d5468031030b0780310025401750403411a901002c500010000544c0303e103400e40f815030b0480d544007400030429071800340e11b03580303c0f814101c090301d6496440c1d001161850440e4030034411040302070400e80041c02c2400d40c3c0c0340001c0d511002d5100280410403210104c0c071060703101d09201d003c0c0450b40011a8000520043d00ca0241840d501c0142d8118640d244483c080091070160f55018070380d000041c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 654406546 1250 654405296 654405373
    0x11040f060e0612030d05011428030b070c0803180f06040807082b050108060105010309080409020a03140f1009060e07121805011a0a03080d1a0a0308070203 68
    0x140032006400b00346030003884c8001d00c510f2030354600c503025a80c0030700540314480143c5403440303080c080d90014414030341d107901e10091040500401101c2451086a4000b00380141c203032a00301050f070740c02c12454405041170500000300080304950110000590106070b08880c1420f454285043d11200c00307450040402c0c1c030070000b000c00304800034094914609101c200164407003945110303024080b03c010b40b14501039150b0004000e210020303c9802e00426007030905101160196aa000003803266004201c003450380807600c090715911a0b0b1209114003500d104158003820695038810042604449003a100b00d048400426141164080c0314111080d8081055581d2500041a15200c1c4804007000f0000d544060341490139014903c0b4680d090302640001400b1004c0998020320001015a40ca02902100c03001300006440c200c226040e81880321800100c614100c5100c0b0007544c840c501c065031028000c10040140002c0383c0050441c94800c4044a00009604628030000003aa07210a14074034800e142 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 654407796 1250 654406546 654406549
    0x60209040f0e071d04030c0317091c030b060901050c1024050d080703260705090102010e2407051603030e0115050a1403071a030412030608060a1d060411040f060e06 72
    0x607102c8040c1d101c0c0c100001046270f20b034134100340f84c03200b1903000c41d1075032210081c051010003400d03510203c40814036086c00710394080e0022442034805c600c2c3d16410000005001c041d450300500c07803100c42c0080040180910748002034a0020000800c0756010309034480500060103242c50700214030803641c840c51440c10703c02c4588003138a20040c2092100084805001001c42c00a4032102c030a1203000f543e1111074540c0c45500c00282141c28480c9640b24940c05103005502103606490001c2c0301f110706030944641136444400440f242d01440b03410042c180d00c225114010580c158018020766480400200050740700a030101c0740309110380c0714042d000310188a00b0b004442442980d51409100a02100c5e40540e4800340004284915104920b1548001c03040c0020014149a000c041401c80d03c1c085c08014100041315480e100007410b0322140c1c95031a802c0e55594682072181c151440c81c0700040d80d02e98940790404428220320101c21611030307450302e48030000594a40c81801c043c0d62900c080e03a2200e82d5000f0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 654409046 1250 654407796 654407807
    0x1020705011523090c0933070215031f140f090610050c16030b07080108070e01150903021017010506280302070b191109030604020d060209040f0e071d0403 68
    0x7000034170426402c100052050303e40c0d848014441e000249038a800c0070038001d2507804c99004010010075081c0400010b0090b83d00d0080d5070100240d141ea4059407a151113100b11100b218a0103c030b016410710038000141016080310728174507403c0c180c0b140450703d5140010482d154004803081d40c0c0c07042540020b201e0b0741d071241d409054180801802c80307030760b41080118011420b41c0c0d0751084030401d41400030030152903805903001d401080e4a10041103900c0c145a90322848040500a10290a50481446079801d115410440c01503402500604030040402e200420112403195918980c0c1c041400000c0c09081ca503044030881818941402089007641d070b20b5024150314040712008058081c003e20005c103807a038a400c0d014203120f0001c14880c40743c01140341d0a5801040705094034400900c008581d0b5100810455807107641114281c0400c02030740b621500a00840c00c5681d0440d2800140c4203904500b5403002401e4010305c4212200c40d40c2c2c0e00d00000c0c09010755444602c0007420390003c60006800340 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 654410296 1250 654409046 654409051
    0x80c0c030706112a0d0309080406030b0f040e01020309120f09221103040b06010f0e0d020406150306050f040504022d031f0c0c02010e01200102070501152309 69
    0x1d10306031500c040b001c81d240704900100101c2c000c5900a46425595884c204032411961540d0704040c081070030140c846101c0d90080c1e01c40c1505145e1a4450a034043d0390754004513402c0c1100030700030001c0145a800351030003504101e4200009103d81d19210180f841c100066465070612422218503046c4120b082c40009060b0000b000440c0d5807807034001c0303051f01c11030041c00c0d083c808070a00c094907460300f4240341d0042000940010305000c02d584411a0071984010000400c1e501640d410b143c9440c1440440c00828944e48a0400c0c0e007071804e40d09400c04d07450b801001c11260b00300c607441001444c42041108641e000c2c0c4000798441e03003281e60501c0c080c2100104ac0c0300a440304640d6045180c520000c13904005c649810301034450031840d08285c0e20103240c803a0810300340ca5031401c071242407450b5001a1002c40710310341d500d040c0000c015800c0d1500400910311004018040002d5407224a03510301903000c1d1030301042c06003071f0030002d40010601c1800302003440301e20244101000c2c54009600700344541d81101 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 654411546 1250 654410296 654410321
    0x50a020a0203031b0601170613081b071403031c0b0d0501020406090e01170c09060613031b171002091216050f04020702090a151a0307080c0c030706 65
    0x4403002180981d5003440900180c0d060706903404501340300642d01900b096016000142280e50019101c40004e0300002d009910102c944610741e200340050401415038056058550945071000004048600b00441c09508444a50454001d050940004c154807809885a20803500e5601000594070b800150001ca0b108000503040c00d002d075003140c850a0aa0340203400440205d00d98031410451001e01146540c01001c60242b00c1d60880a002ca4a580b540c13030341c41100303200b01e03004000301d9060b036916021166000c0859070104012941ca1820200e910b10b109503507000c04040e0f03080012020a040340101448020b1030107011072442d000103000c001c0d00050089600885807000c0005001c0c010070680e00880155840000d06528040401600482c1030008600880c014415140161074880d40340380c21007450300e0701150704490000704540194459100d03a013101445403203400d0101c0d500300114058411560340300b006548a100000c0d10303102e41900c90034294002c200c408003080c400c0e840000b00c03405 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 654412796 1250 654411546 654411553
    0xc03160c030209070815040b01390606081615080403020a120203180307081f0b03191b0315021b0d02030a0801150504170f010219032a050a02 62
    0x1c5940200f800103c0840f01c52003c6003480c014081d205c0c42184102d00100001c5401b0700904440307900085c103401905d0704202003a001da0744482d40384c96085101c1d02c800640140101c42400d15810014041d0003070b8401c441080c0101039240d16000700310350465040d1800d03102690441491183c1c1104c65400080045e000c500558461170000341c802d80200001c885141d00854071407089182c3c2c04500d2080c280031500c2030b071150707a040122820110b024041da0305010444030030043c883c00314201800c4d5808140b6814012104403204003042c00108000050203201c0715510300484080d50300c2e024420b80009040c5019101c0300d009500a903070002c096441e5032050402c80740d20280d5240d80b43c9140c8c4074010015801c0401d031080003070341c0032001300d0040141c44031b041302c0c01c090090060441e2245000d01c3d141800781070200b0b085000304110011000303000c000219680c2d60709506c0d82161154107074029000900300540da81001c1c5a40c9074007100e03c003450441e60341e0501521000e8405500c16002c0100791b00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 654414046 1250 654412796 654412799
    0x27030507050a050a0b061003060609091a040e0d1106071403060f090708190212040224030709050f0906030c01200703081e1801120209060d0b1002030c03160c 69
    0xc1c418440012054411504011720b030500d00108212400b11000c2501010701d01041084200e0703100100d02c045514000b800500c420904191145043c48800c0c85601304d0b0429040c041c00c1c00c00042c2980c50074040b81d942c68014180d019225894407800d85030341e0001103c8024840340c1600d24401160000c0c1c00030714007450864480f02003400050100c4000000c29001e004020740019603c03102401058411003c43c54a00200e102c00c0301d0490151000e40541155014110500d01d03d02507408420034a407881d940300d00d807130315000b0551040c9014060180c90080102c1a4500b005016940144002005400004c060301e004440d100d5604201100f002e10904400003404030500a09015502a2980360f03030706c2c4031441c00490421903500751040340742c0003005100c3c40311061900840302c045092801d8401c007c070110740d110280c0511051182d0011000500850a00080d44107001c003480075940216140b81d4040144d850340030704d00c0345d1305582d0010440b04529208841c51884c130948210301d40c02e0201d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 654415296 1250 654414046 654414053
    0x9010813050a030e120a210201061806080706030e10051b0a0e33180a0605180328290f0c031605090424050427030507050a 54
    0x40340380802a0b0102d0310713a0300c4d03038069420202402080107052100070210b841050b619885002840045540c203078500b0b0740b9904986200b90420001410f0088034400e0882c0c1450000c40102840d04c64500e0324400c0c4c02d400510203010f4000c682c82440542d014007074070082007141c0805404010301680c1c0e10541c1c000c07a107200100b0100a01300d207101c1c0b036030360148201d0b8030000d00840c8412100f0030148008513070b0744c07032010040310040301c09500141d400c555125007034542c083d000100282c40c16a4800c402441c080303000e0368410080c1010000b150071106103c41e442c400d040d10b5040098101040198641c2c07040200c00114010080040c481c8100c8501040c445600007805030061500c07105502c8180c041c0449100b842503095005503421304010b1071420150045042c0d000659010010710002050300d840c2130b51944d110107100141022550726145c074042e0b5408041a0501031240f04074a8004410280400720021030700c200300c0e06641d200c040f929070720b00380c9040d042540d0458640c41004542c0c0c002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 654416546 1250 654415296 654415303
    0x1706060a1701080c01030e0a0c170705030106060519030606050409110f1305030d0801150f110a0b070f080108150402150c0102030a1b0903060e0a08190206010b0703050901081305 78
    0x83c90b50b00003400444525800040654100e100228110781c002c101580c080388000c01d404007250b000803840c0d5544821082070a05000035030340215450352814400040441d0018018000b0444101c00360320302c84071210f81a0201c4203075004580001340280003d120300480c5500100c40d0b150020040d030700304680c4040404007580a40c2014000c512444006c00442c00c04000901880c202d604000247d13604182c0c00c0c203c520381000d40c690420640c0200800083d009130780f1401c98500ca0300c2900c0c95803800b801d24100c03d401c256440c00008480541d5503411724420400030341607491040240c02e00c1e0901401d565039015002d4001d981c002c0d41c460304002280e24400c014030650b0440c000158070b03807800c18103041c126070300c2c002445440c0d140407c6d940c030b0413a0b02c51046c406407940990b000601e01d00c0e0540791440d040120301c000b0446400040c20f00c075554900c1f00c00220030b001940c01c58005a0321510f07100614020680c004011410074407405c4403d40c094514581d0103c1e00c070440d800c0c115041e8076413900c1c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 654417796 1250 654416546 654416549
    0x190507260705060c07031407080a080a023117030904110c0604140c0d0312090809040c0909180804032d060903020c01080112061a030601241706060a1701 67
    0x15403404c0025240209030708202c203040170101c801c8115050021a445010380340c4180300448041000c0500020341c00c0440350b040c0c40109058a040f40ba50500501c0102c0019400a0380030800d0420f02d80c00281000d1203449078628103100320b000e54141603c80c400d2101410800396040b042e60000d005144481c802049614801c602070600c0d04800442071031240c0c24013441c44541801407070035064802c0030035003000301d86202e5200000009280034031400d01982500512440c507500c103003032541c0000d040740e000041d07a0503075070004030400500c000b1816888654040081c000c01d110300500007000491030368228000c0d1180041c00005c1000105810550103941695044414595981541c014141e04210f0304130020301c282400780322541070002c00a016007140034020801506c0c1e402e031803240905030504800700c0754064200d81c4035507180c221081402100f24001d865003500d40300c410700c54502c21001e0300c0910804050031806074880e5000d020203688880c00f40c00500c82c1d860170768001039982c0002c050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 654419046 1250 654417796 654417811
    0x10b2a070329010801020a0c0f020d02031204030c09181b080604060c03150b041401020102040f09050108060702010c050a0c0822090f06031a060a170319050726070506 73
    0x440c1c5804207103610a2550b0181c012145a030f02c14000e20003490b401441c847c0c04107400c0300704215141c00500c005500c0f030182c804001e415000d0f403280c211415030b50741c000c1d2041e0f80c40b0305020000d10ba111160f04080380d02843c20f01d0503041c566807035040404c03162620049441341e40c080488550b82c03107010307541c03074904182c0d011206e00f0b59403407511143c19894401c442000e050311b5201c0d02c5152414101702032600890192040440e511078643c43c0c168004d40c110350003000400c9130580c1503a910075540008010902c80d110382d07030048800042145106102c1d55000074420746a43c0c1c1000c0056004a49420107014100c8030200b04004441d1046010040555a850410100d00d80360781010b5180c000d481a07031010711140c9040103c10b01c0000c403030030314000c4038418509108645549100000d070402070030f41d0010499401c07c6c8282090b0034000b20080055a01746143c040290217440700032155885244c2e00a003a00601b021802010340109007000c4501035060040c50810842d51607207400d1280544980c07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 654420296 1250 654419046 654419093
    0x2506020c03030a06091b03020c030409090606060f0207230a0e0412270308030601030b060f070302070608010810050405010e0d0c020907081b0904090b0c0a08010b2a0703 74
    0x403442103201d00a403005031a1040d0140035586c2c0103040c2406001595414000b13041d008541083c40b00d0301041903d0003032803071420621050560303050641c0280305034015400040d0244010b41030847c0001810011640c00310b0402284003045283d039100d80c0010740380690700c5801d0b501d001550f1840f400c0c1c6107009a008100c9880c008000e40b40c094204501003c480412401035441e4465011a03a9034400440b50070051075a40c030b41c1c038400101c009041c0c1d0140b0075846607000c2901d503843c41e40e0754040c00c6c0399072190302190486a00e42ea402e89a4203002d126480381f5904c8841409074120450b008150401c0c415800411008165120a0700b030030b4801042e02d00141c4c0e140e01940640c0340c500702c0d0030342001c1d403402d000c2442c2c180729001c541c01031018400c030110024000344140003601c56a11104500341c001060008038288201030321900d500c142e81d85c0c0b00280460002040030403050003115144240d02c1405414400540310000001140d9140ca910600036900b002010a0701900816002c00d444c0010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 654421546 1250 654420296 654420301
    0x90507120614010501020706171807081e061009090303110c0307030e1c0f140a03051b073204050a0209010f0219080906070c15020c152506020c0303 65
    0x10114482e030164001411944190403c1212070340107042107000c00d11160455503e6942e140d00042d00c46500483d6098500c2584e000082c05000415803511a941d2001007201303440c2000704840e80c840050711a00043d0b0910b003410003035042c20382d000514161003400e0101c1d481281e45081d000c1340e04554035410030f42e000042c1c21002c140c0e00420000e2000c100702c80c815000c04020340080840324107804010f148810407010340050141c00c10380d02c030744009200c007203900708580741c90b0007002500b0141d654900c51f451032316030440704400480d03903d01b51841c080c221050b5030a050321050315090401e0b000000440d0342c04c9407030310980703882c0913840c40396039030720f001581d0341c00040b000410b6652031030304040464103c00080103c05c5a9145000718846e041901d29803640102400625235200d500030007001900c1c40c0c403000440302038401586505000580944820244410a00880300050b0500c000c03031a008101500c400885151315900007121240c0c0707074040041303590310f000499225654811455002204 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 654422796 1250 654421546 654421571
    0x4021c0501180605030601030f0f031124060609030d0f030612060516080c03010902030a1e0b090901020f0415030605030a150f0b01020d140903071e0e010f090905071206 74
    0x40d00020042039000313080548c035640301c0c404a812115002480c1c1034200c03404405051244c4400c0076075121318420356000500c09004008c507a4034500140500300d10349400161145461020b0b03c00d2140702401a181401780424101c1e1070146a880c07040c1415070310b14000c21082d60005c8080741ca0740c41010000b8280c1400242c000350540200c4100d000c0282070f4041100010189040d2030441e03100001c05a1203071207520000024041110004050803400c10801540e00c40b203810a100a243c29610340c80c007621080201c0d42030b482010088685884200020002860b00030540c3c0e0521000e803800144164036000041c0c10880d2541058a41c00110070701513009180f18451320004480d8640c3c2000500c003400d0002c0d4681031860104070038028509034005058401340c044803c141402000e85603a60307210f00b005c83ca155540d03200c4410b4030324000400309a01c030300f0410f1213040c0c80b2401c02503018076290440740000b504607008211524001c0250004201142e1000000d44912481000c0f40d5640c0101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 654424046 1250 654422796 654422801
    0x150c14061608310c1509051c05150a0c0f0c11181303080606041409070c0c0f18060b031b1303030203191d04021c050118 53
    0x111a5903800c0081070140880c00c1c1c070201d61101803141040078450356521000a440a04007844001e14a110207500781c100f00703041c82e40c030821481101c01c120130644881d0600300c21808100014003003603034208140264640311440400082d4540800112069140c2d42d1504000c1d09007020000064130405208544505000704940001c40d45804000e000a80200415407144202d02500e80c14402d68040c82d191035510102c0c1c03849034824440c0b9030f64100031060003501c003141d010541c0010000c0000c80c000f807805104890880ea4402201c00310400c1400c1044903440003c1c3c110070501510f00501d1001540d407000700310003000c80c4288081e541d443c00c21807a4040f8018034110f41d406140c000b003444900d080400b80d030b4102c010100f54003510160300303010741558842d01084c410f0101d014a000410968004002d000c01d00c0244920a040404011b050b21107129140c00000d282c0e4000c018656542860390291071035030fa03454180d40c42d504204140320225174083c0c00070300c15210002c20000d401e44150 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 654425296 1250 654424046 654424073
    0x1060b1605060c07020a151b0b01090c05090312030c190e0a050d0b010905101707053303060a091a1f0e0f0301020702090c0903010b0f030c0108090106150c 68
    0x1a10141e01c4c082e83d990008181a8850050100d802006251090380700e00c40c040e89511841c01402c044030030006030400c1c3c01c92660074407030202601d0a0032101c0c22417921a0301900e0786040b000e07000f0030342c0c21200c504030042500300400300c801d2090300b80164100c40e078009210b04032348409a102c80800840100030301613488101d1300042d001d00a0059482c0006944400b898111540c66000155030b0301c6e0010b4010700d500c42a40070034520400300e9a521400400481c000c002c5990459142c00003840c0040405100801210b0564950058039045203224801400031644004c000300201e8680352900039aa08031040320051610b10035044141034281d040c49404105032203940f5072030650503240020020030314422082c035140a00d80888100f00c564800b501176132200369004128140e05e2510307070440340d625085403064912075820f2804142c11414120002c81c075080d0f004c1e026000005c26100195480c1c20042c018000c00d640c0e9510005902c00c1c143c0249008040c507039140c0c3c000e40300b507081940708903c00c1d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 654426546 1250 654425296 654425311
    0xf0b01120c051f0c02010e0301060e0a061208070807060b04050705030405010f06081b03030c01020319150f050603060a0f060e040b041404031d10110624040b0301060b160506 76
    0x141d49011025000820403d80364000526041441c0b10081c80125440e8070b04400181e01076003019804541e202211400c20301c10f0b030703c0c504100172582d911408440030418840c0003925a02c000c00c0180089185038000382803d90141001080000e10180441d088840c00c49140340041e2011091004211080c040c2901410f5402c4060000505101c121521080b0340d80c00001030041a10b410346c0c580c0c40078000c0e0381094551360000c5403689007900c0854aa0060f0103604c1c0b40081c600480c00345440d0045c0f40394001d581c800250106094240802d2000c5640007034007445e40300400903000502014025440341c080e2106a86122924203d04140310544400800483c4182c0c28129508840c03200350010940c050341601e0700c100103400c6102000c107007030110000242c0200d1803040052949800198688180000604490031540c0f00386e051300940f88990b078000c1d104840d880c0543c060f45820340042c0c4200f00c0086c00065010f41d21411140e25034400c030360241c0c800685a5801d030501c01f0502c00141d20445 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 654427796 1250 654426546 654426559
    0x602070308060f090703020d15030b0403022a04180b0408250f0f020d05010e0304150e0a23130b09060a0e0f10180e010c0207031a040f0b01120c05 64
    0x10f50800104565070003820501015400b01c3c090b01d0b10b6149410018583c20646581307400e003034403400d2415003c1000c0380c040e0050300c0b13103040d80c11030055141c049240c12251403c503034400c035130440c08000140580304030400c880f01d0758032020301c049030810841a001d14420400c685e40d504146d8442584d4001480800074000320412072a00071604203006800040d0b03105010000d0240144002640d94903001d00246c4070390f203803040c6519a84030010007041500d68803900c02c2c1280d00c0072401203903011501c800c0c80b0b80283e914041001a1240000b00c00641601070017203901c425526000700b0514802c4800e1541c5841d103400401009003061481240c2026059640202207414010003030b41008014200401c8200720314001000c44806010342800350091001e48012100201c20210160000c118a0a19546040034401d10a030000501100b00c0f980001d640089581d826060850b601c0020803d448070121106030070009840310301c1c00c90107005645032f2001c0720400c42c10072a0381c41242d07401c1180241c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 654429046 1250 654427796 654427819
    0xd1d0307030206010b2503050a1418011809020a0503010f0e0402180901090b011203020c03210c0f0f07030c0801021e09010905120a0516030209010b030a060f03060207030806 76
    0x750b010420506480341d001c0b0b521741c0e400301c03203040d84800c0d15008280b0084506807a81c50307040540c407000801004c802552100782801d005002c0e418a8410180c4000380041c10709085412175000d100c40201c4514000d0040b0301f000d91f6154020166807280041c540003450000042c018a8000b180c002c3c050240186108603d280a50104d40b601221001c10704125901000040803032109401410182d40e02404501d05569615500e04110b5180e0a04038090301a88003100ca00d4240011001c4d440100022840510044150b080e58164813442c1104150b008290b200304030760750200099500f88020318020040c262039400c04941000d56600441c07501c0c0d00402000d45980040c0340e280a401c1040c640d51580c60205200503201c41c49503610140d0816603416403c0d40d5403102254003000315014000780c072030520361009032720604805030000961020740e1500600445001501541e409800b402c80065540c0e21242d0b8407840c0c40300780e44102e80070b5400040104c105a8407000704c80d0400c0040d1400391551 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 654430296 1250 654429046 654429053
    0xf1017151c1101050d0b030a080304020108150102030a0c1406090601172b05090918010605060306060a031d0609030a0908061e100506040f060f0f08130f05030d1d0307 73
    0x500002c1001810001d001c0340c40c0f01d54000581c40058011802012160740488502e424113158100311400d0740440d401100092001402000f4174008003816405036140182800003582c0c008a80f1509031606210b415030749924003010844a0b0103090140000d0800b0761404101051000c8404a13000c03440d0040d031000c5071034031a041580040f00240300904683c03401500030846040c000e07580402d80c440c8006041c400c40858281400000000c8500203019840d1944240500c40c40240c0e03030785070407007001c00c0308401c0d4900c00d03444000e40300d00300c8182101c8980703080000b6240281c2640c1c12409500300180d1048003540092046c001004284040c0841e4a0699101001c0c003003410b190001d004c1c1640001003090602c0030b9070401070301006200c00e450302d840b03c40d2099144618082c0c00d01213142c1c0c0301d40040b05806031034a841406040c0d0345200c600d903103203485003c0030050180d040320038152642c2c2d0000024400d001400030300c1d9080c400014a00e2940c60300d40c5c02904800da80031200e810410002011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 654431546 1250 654430296 654430313
    0x51011060f0604110307180605120c0c0304150806010807090b07240903050915070c03081606020a030b0102011b090b09030c03032b05060f1017151c 65
    0x22400281d03100c0c1c01e68603800494040e240154106a815000204002105e600185e00007451100c12421207282c503241c0e00c05032140d204901004009a60740d1000a84039030030080180b642e002c007082582e090551f41c0c0d010303050444100b0080004907201c24100070b00c40d644030b1348007544a0707c5072805100c4646410500c100500c0351072000740120000380a40e030100117070b111100703119843d280070400c0800c1d036a0600600035009018900e105540328650100300c00316490603905400d802000c05109241341d9030301c141d055403043c0c05540001110884c000003042070303880640000003c81e20302145d40c80b95080024215100c1c10900c07410385082d151094506540b08815205907400c541060b5aa04440c400191802150842455061000203140001420000c40c95695200d80c90b491492060020320300c0e0040d0354048400d6a0425400303d2090001d02d0107029803c51403004d170412400c1032039400708420b50800111a048284001065414160304001d000b442c110104202c3e805034155041d038603c0c04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 654432796 1250 654431546 654431551
    0x3050618071d0a181a1005070c03060603300e37030c1202010e040218040524091302010810240e03150103080f0912030405101106 57
    0x1004250846a00340382c480c950070595510000b00080c00196a40e03d46201c15030f034010f681003459080480b5680307403480003080300c1c8507180010400f00101c0082c13101181d40b50890101901e40c0c0c3c006070760000100da486d10810b000380d0300801c940e00018011134a400e02444139120414800d141d80c404201d00c595101c0161124002c00b181c00455030b2540c161090507084141c0c00d4250300b0002900c0c6402c02605902c0320340300704c901c6403580080d01d654450341300c0c505c81084030020f8003089003844a07001e64a420f600800344004080c0d00305100d0341c12040828200c44003100ca80300f5107003407403107400c0c00c850601c03051086562045034128018500420014643d0701e404400030f0601c500803002c94040074030605004040c20100c08001d525500c02403502d1582c41c0f0a5a4040103e644c180121419090115680d5000291209010203503480c41d0341c0d4003140d510048080301e1000092103800b0300d69466864803d034810700c9000454907541400100021018100490410f01182d800360303103011600400c0720355 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 654434046 1250 654432796 654432811
    0xc1205070e06040e0106090507030c020703050d120e2a03070311040203090109020607081e121b040801020f12010e1014060d02032404050c0d020c070f0602070603050618 74
    0x1c21036142d140105001d00b104005100c007039404c002000c42c1e90156507000501c101e0f8299001d101000070707098240e0f251421030002901c5608180d549240039402500d0b5859075070300307c840001d01001c030341c0c0e07515090000c203846115021400c2e0086211007106440500503050084010b8981e06140d60b4a9000300c000320f54050b40243e40210000d0500007080d0f01c00e100c101c0d005002107503a04072510300f91000b94802080d90000c940c4444070f00f2070840309103042ea034442c000e00010386060380390900b0a1030451440c0507590800f407000c01020034100004e0000d8160403600110058407000801084212081e05800c4001c078078440d1010403c3c40b079151030340d6408a8201d6a504000581d07080d0129506100380562000d0709800001031124a1040c0b000d60302014940c480d01c6910450424100002e403401a654001c212005010b12a1440456030092000c40d46901c01c945a05035644000d072400c1400340e200d900075130883d0808100a40e05802400d5100c6401c41d03804000c1c0103500003e00d44040701501c1030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 654435296 1250 654434046 654434069
    0x120b09120a02100e10060303050415030c050714070302060c0d08130201020d1107120818010c0b150a0306050103050f060a020a080103150f05010306050a0c030912050a091706040c120507 81
    0x4c605940901c4000242e04080400f80145500c030305000d4201e51041c42800502442030002840003171191107103000006440e91214900551900d0b5040510108803144069004041000006079101002040070001c480080e00142103280390140c10598001c2005941c1896002c03981c0c010307a40416403c1503150141001c002d007486098070035180010a0300100c1c034021b6000c80c00e4050004c04400b900040e407911924006d1503801200445110b51415030003000c41d0b03004000315001c003540c900c106206200141a601d14180e49460f2602510420780c4280d0f00c1e90002213190b281560b09000d1643c0c0100300304010b501e41ba4045c500100000ca0520018141c445040d819000317542e01600455141c16154805200b907503140e0604200514041d500055110302d41030106201d5402800303088412030b00104458260564020161220360003030800c0c800300100404c021030080b40502a160380070b03042100030001443e0502c0d00f1a20340a582d0003200d40e40c100c80d02c8000c001400003521906442e080ba249 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 654436546 1250 654435296 654435311
    0xc0901180e280c080d090b18060304060b0406061b031d0d0308090d0e15030403030b09010602150f0f18030d020c01051902040e0c090109120b09120a0210 67
    0x80d4184060702840003400c10220401e1540003510400b031082c10b9001d40d0308260415610441c071a130301c000c0310071503901107070000008001801e42d04000d066400c1c00f501c501800469038000040d003d5108803001c0303070301c942e64003224421401c0074403d60002c4c00302420120310700340080c210b4240161400c407006040004959900f000e003440145a42c10b00d18001d4100302a48a00d490081c00304803003140c034992144502c45a07007030f02c2c03071141407220803602029000d042200784442003c15264030052040d4145606c4a0002d41c154a40000719802880c1c26030140c05209140c45811900d50780c05024042d508040c001031100800c0050860364114040c066184962191111600d0650103111900000c207440814103810000e0107410041c40b1700c1d032107010400c5000c41c82c20088120700440c092055060b440c00002006461010700802c101c0ca014106040110303500c1c20103c44c01c000f0000b0485500c45000103200040f071040102400306810701d10424206031071180001d681d40c2e07034011084601d540340d420 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 654437796 1250 654436546 654436571
    0x30406061203030e010b091311180906041e150519020a02070801061505120411060403060204050f03010e0c06070c0312021e0c0a091109040e06090c090118 68
    0x10110081162070000c03403168080307050240040010f0050300d500d6500784810036600c0e180c2407103480e01c070342d03203c0b03801c1303540d124142e290300e0109150400c509810207042c1c0072100101802860403441011402e0040c5210701d801e2810b08030600c05114403011000e907116410f000190401e00300d405442130450002042d07942c0b0384141081500200b1540302952000407036251440d4003003401030950340c0c07020003440040d5503101d1907130341c00404c0307404400000c00034012045040250039000350018040c6810f400c0c40c8454000282e802d80c080d80c4101d940d5580002c0400c000e0504200c042501481240200050025024856100d85d462001c0c1c41c4210342c005044000c10014550400c040d540102010f03003150b86002019595182d414890303011401c840c5440c0d03e88040c00074103402c2e0360001920b401c0056150003800302c090f10100c1340d1012040000d0200209544461160f83c03000c1d010b00c4001e04950034240400c5040031050b10700c45014110010060118402d03c00345800d11901d078100002d100f0316001c2e03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 654439046 1250 654437796 654437801
    0x10203160506060103060509090726070f03031215060302030c1b07080c03070b04062303091b0319020f040204120c090c0305060d11190314011817030406 67
    0x203111040c90060003000300306010000070103900c952001c4e00c081100d44d40f160100b04050300222890000780e4000101481010f444044442841a410342e04e000c0034201850b41f107040044d103402800c0880c4031410108145a407210100c2001e1101a604011009414001201c1c40b44240203040603d0340000200d8100010b440442d2250b03e0140b100b84c8c05044200700481d101d143c03600c0354407000e1184000d0400145400700b255001c45540750301c0c0504e414076007901511900e00107624449c241821082000180d4500c800840c82500c140e0040c040d80c448201c07807e1041215541044d029920565a14001065514a460b092501110280c09010740200010301a10031900071010101c00500c44904010504401c0029501a81414801d030206c800c012001c448003103e05680c88906024030300c0129500a02000d048a07018010013000e0058500e49503500c5091390003200c4c5010b00300d040400400702849070340000c0010390051703040b071206038503507081c40020190440000701001020404005250303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 654440296 1250 654439046 654439057
    0x50d0c050309092806080601050102030f07140c0a060f0305090c010903150b1c1a100e0603070b0307261302120c100e040507080f16050d06030f031b02010c0f02010203 73
    0x62060b03205154041c02c640d002d00b0706440761406c42d03c11840049410b60002c400d43e10003a4081c0005e900708036240e15042e4190401c004001224015100101682c1c0c80381c0e01e040002d40482d0300d801c410740400c07240c020103c03900141a04ca04e5000759041450980c1d11103c01c80c01c5a1b0401f819200c10500c110b4120001c0122400d0700768440e030a541f210360b0a0181e6035142c440d03980201101040707202c031005202d17040c040498802402d51009041402001c004c103010b01d82000340501103442c000d460b002c40411682c01a030b106808074040e1501c220850b0403a83c0c5c41d440c001c812400c8440c05041c4180f23802d080076032011001b4406d0806001c444d0a158041144542c0c0a6000340390702c9440b00003c034090401440e0f0f50b1601e000702e040000140f0340d24001c801d030314020002003e44845680d556140c0b000721000b05440d12040110811400300c6580603401010051405003107080b8000e81d541c0707005440d2002315003400e06010100c0c1c49200250382c200798902e100079040550345081c1a12880100c2c114070a4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 654441546 1250 654440296 654440341
    0xd090203060705180f10210e0f070b04050a050618091807050109140f010c05030a0309062901030507050c060c1306080c180409050610031101140f0702012604050d0c05030909 76
    0x400c004801e911900084413a0272550250076030b9030b00b41c1c8401400860384502e000b100d13080207086200b00302904102009080c01c40324158805c907021640c9000400a140941d01c140c49080c41c0c15100248000a200300c00c0141000d0a025081c42c2c90400480c20100001080c1c2d4800e008502501c103699020703041c228216a800070550380e507840108006030090a403c403055404910b058a0001c1d0345a508074003441d01d0f81b030183d03060320500440c40110003414000b0001d0003004400c0c4420280c42c0340400c0564001c020020403d03480f00c0010340e2410340e402940d07104504000280b02400b00030500d100c02c0311100284500248082c90911010401401032070303000902521440c001c000b0307414110040309040c0c9200d641c080442448041c01100c000d001d060100c2c03903105040090440c072000143c0140503042c4113042c40c28204074120070706051019080c0e2600c03070101010007000f0030002c1c140807940780f40c2110700b4210b0b8404416100c142d968041c90301010301818070800845c0c2286100d0500c1c096a407003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 654442796 1250 654441546 654441551
    0x1807090c110a030908061506070605060f0607080405090f04031407030512070206150105030c09010507150203130b0129030a0e100209010206090c01080c0d090203060705180f1021 78
    0x1042c64001c0144804c0d00c10341440e40104000b00304020445840c0c0d00000000038512820705401d501c0301401000c0c0541304a5000d04650480034250300e6440140880701e02420285884038581424811410001001d039150901c1075800c000000750441d5600851744200e580a9031241c246240a440c68411006d5100f00c2007480e0041140d882e40c0020309510079040c1c0300000c04080c04000042d2410700007035604c5019800c0621480000c0c0d40f0503800307802100d001d003250741c0803905e80c2c01c031401c100e0f801941d0308424980480041024450310007900c80c01810300700c1000c42c0e0900064080300e0040403100b0800013050000001c546051865000803e520510381c0c107613121445d0801c5080d0084d8404507009015001e01400550740d1070021444400d500c1040e120704d1060364030350403104500d50148c1d100b600580d550300303801ca0250300c0c200f01d803504c10343c01c03070322041d42da0f0414000a500342c5808101c072038031644a8140030042c907128000c403800e0144990414040c040030402e54084180e2403003051a0f0140d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 654444046 1250 654442796 654442813
    0x50a0e280812040302150f011206021605070314031c0506010e10020d0f090b04090902030718270314160803040b04140a03171902211807090c11 63
    0x30002c490242d8425002c4824044c9a06001e46240404880024000324140c00420004401d14190b20115201c1d40c0c00501d40201c00442c0b1806244070503050340e1503806814240100010b802034996034100c410020760500108101e0214841070100c0030080e5030f525213001c41c9059018000b00f5030104402080401c0348086444000e5444818400c103000080101180c0780740e441c09460101d040d14400e4282034605420070b60320074007500c0e28440403038062080480000780130500d9215618410146000440c0d0481c410310981c0f46a4407003c401080d01c00103803000d50000f0b1b085071144207100c039502c00007610307640a26203030490100e0503040a80b80700000400c03c01042a200d10652140e880b8801407082c90003060002c036910800568000c003c50007299030b25901801566407650b002c800081c0e0303240d242c900c10200388140d0304000039003080e404d0626292410b090032081520341c401c3c0040c0004022030005004103907154018031a016007943c1e100300a80030580304400c140301c20202d290442d030104 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 654445296 1250 654444046 654444067
    0x15020c0a02032505091f0b09180c031f05030d0503090105090f03070f060204180c020c010206220c0504090309151418030106170a0204050a0e2808 64
    0x16011600102d00c41c0c060881d50404050142e500c286965070b9080803c10b0302814001071003d1281702805a0406001e404140c000c0c94807000b07050740180510001141d101c5458105100c02e4844c202c240084005801040242e4506550705480d4050416216a07100c0d0300103070004016607010303400003034042c0900490040320603045001980a02080d900030807881d6074200d15551281040b0003181c203240c0040060320040742d41001c3c00980240250310061806030b64540800340d0a2500803040c0030a52a4066101c0c660340501c220000340b0400c0c00600f00c10f1501440745201c1100a9446012040010701c00d8014072075034646150103030101030020080042d082c20b01401039400d42c8501c4118031040f1941c40030741ca1180c030b0400c80d850f000100250918840e00c5060316038101c140b89450f0159650303503000807603504542c160301500d0140350140c4014006801444140c40e0018803204207036040480385c901081e03000911080942500c828840d8203860520390b0b000c0724184100140c200800400c040b03211 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 654446546 1250 654445296 654445303
    0x1005120d090f030b04020607050c0316062d0f1215150306060807030e0c090a0509010e0f100e19150b011b030f200d090f1a0715020c 58
    0x1084460344918101070b50700c1024015000c0e01d800003c1507026280c01007001820010054548244510184c070305100b01603011915109510090722054034242030204403268000c411041c4100078500351300451000391040c489170300380404890080100b05410b05094034404c07214030310030a12a440c140000000100c2c008010031a50040c514007271040d0b0403030110705020b885071404407551a261052140d6610401350b004040e58500100b06018000302d03070348c0c01c2d078991200911072a90850f00060701e060281c1c002d0300711500a0071030b0900341e00c0810340c01d40c010300006001115904140f00030440b5282207110703604241a10900e00e049540980310b0504100031106d5900a100b0425070800c01a0804801103030001030340328419911001e8000a0000700780309144071142c0e10490304298003108060031207802100e0310b8044601041d000880129805544a21200010514415000c440c05c1c10600200d1070524081d0a812030b806d40060000c0c00c01c040c0c00b030703403c0740b0424442c3c04541b10030842101548 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 654447796 1250 654446546 654446563
    0x10905070e0d03020c1528091d01030f0512210705030402281509030b090f030f0a03090804350a0201270f060e0409150203100512 57
    0x20626111410740c0d2400c02400c4441c00c160154014070001280b4001d00c000411003140720390303840c90101710360b070200340e20300605520203268903140b030074000040c01c00140000f415803c4a0200d084000b06070341690107031111380d415a504000c80502c0304140c0c1c07411310f00c1c3c0f000d41e51030f1444010380442c1d90b105102003410020400c81c072805034501180c0d12540203c1c0d0f80d22040342d000307502582240011900c2c00540c030302480c6081280740300c0d003500d40d00d40c00700c11401d00d1a0700740c1100045401109000700b01000c50360a0708a0408002003c07a080c1816182c0e860340648030810090b1807000c50290311991103a00071050540d04a610140c4c0c8a0321001407042d01c5600744550414048410040c0f04641e0350035600155a04a1034060040010250300454860b55181c04450124106040161403c009015800c1c01040012004270159251281c054480c485095546104030f250407412408501082c1800d801c803400f0410060350703a80e40640101e00600d050308140d40080e41c0c41d0701808941d80010b40043d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 654449046 1250 654447796 654447811
    0x141c0b0702070e09010b0d0f14060a0b040f0501050d0b0a0b100801170c03030901110109082b1104030f0816050601090b040b03030d150e0907060807020a050604021512010905 76
    0x11099481c01e188178283e13588030700d00c03a400941d03a480311b60100fa4810180010140709008402c8451003034000e203850b022096401c0700319680d0743c04043c072840c90030b0b00c1aa00a1207985100340050340c58440040d05500110720058946c0e03101d400080c3c0204101c0c0d00c0714161083c01804414010751601c40108005024029102c8a0400103100c840348200008c80350400a4014010740c41c280c101c100441c0c000c0300709841c00d1a0342d9210441e003000a04540c0c003620b03054030303002c41502804440300200d40151000d504501c400760302c0c0541c0410301d402d1030400c403000e5941104a0001e14580340c039140c0113070b10808071584620780102a680c42040307130115000d0704991140005001e011840310401c000c0351004004198540e20401c2082c1d00d40d981a0014031002111030718400c22f590741c031802c07000220300841303402a0b1604084420700800345c00c4031801d608908984000c202400450f543c1507a40c2c000940701901c60b52612424080f00c81d42d4070f04441d10300242c0050940ca95940704800030207420181c8012 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 654450296 1250 654449046 654449069
    0x60b0103050702011a062203060212100e040b04140a060b090115091a07140c01030c14030f060f03011418010203040528081801031104141c0b070207 65
    0x30303070b074a01c140240b061514102c810b2035140410101005819440003524842c100c5880942c400d01d0580e10b4843c40041d8041c110142e40c42d54640d00a120006004050120700079005401740182c0040168566009030f10280f0300c191500ca600700741c2c000ba88100440c04980c0310301d07448802000070395000721039451400d4800d504140d0322240542c40030f80d0410382c04800a459030b141044a1084088070380022090ac1c440586404a01d48070010320800394454018140d00c480f003030600550f4180300e2400d030300c0c2c600c0c42c0241104a02c0d502804203072201501100401801c2408285c265032140d11800400328020001c03c9901950203400c86090740c1100c080b0140d4010254040d22180e043c02144e12450380903000c2c01d088c040310065144040701000390700c051200c0c40203600c00000c42070001001c441c00d15102c3c01010401c040700040a5030901d020801e0101c000303010030081d10b078642e001802194001c403421501310004002140484004840c0644050251810b001001c0c1d004207150041d00c000b400e00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 654451546 1250 654450296 654450301
    0x1d070b0c0316020d020910030c050603040809190905090a030e040203070c1b0504020a0801090b0a181802040615080c090a0e07170a0507031413080c07090603060b010305 74
    0x54064010050090010303001040365200301d10b1020b01c505165071000b0162001a03007260041b41000804685000d00130b0b0705a070307050060014003c41c40d4002e26084070a18514509680c0320800c5004010b911805100356610000c41d188007e003820018003114002008649440c1800564801c1000425408502c0888040c8190f003014000c891146502d91591124080b50365640600650300860081c030540c0c0c14a0701240a9640f400144000c10f00c0391388100c01c44d410040d030791049450f56a412440741d003000314200044000d80125100802000000092000d61481d2602d45020300800003503106281003008907540c405281102250111507840540b6079550004803407880c8241c902113648030f845280108108100500450303030040d40d900c0c08108292043c10760303440d601d4003920842000c030748400400904d25414810580600e40121428000d803c0c00300d00070000740c14400c4007800042001468400c100310030086400241940c40c0c08124095590808000602001c002d040c00031382401301 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 654452796 1250 654451546 654451559
    0xa0c0e040b181801050f102112020705060f040e130b0609071e020106150c0305090906010e0307030b1b0306011704060e0109080c070b03010602070b0c010b041d07 71
    0x107a28050401504003110b240e40065000c0c00d80c00018141c07201010307071094414145000380913143c010000040c1141c61410314020362a541070803900040c058512403180310903182d84042c0d07480d48054201c4021141c0e040c602604a050101540080e90440400141c0541001c40000100221154416451103684840c5c4070000101c44594019080d000068085882894200740b41d03030704000c2c50704102c1030205200048180303038481d210041003d17035941e80c800c0001f11307503004c0140c404940c503260907000d14586d03540140c0a4010800c00c41c0c0a455501c2c000780742c0d039000e5405003007507160081c110340700542c2c0e034585401000000c0f25504280c881420005000d54902001c1d00c0c09140140c440002140d40050401503070700c002041960031541721000340a2092080c400d00c48854043c20106541d4040c0008852500e00540d0000345201c10800041041581c0811010159104101c0301680d43c0300c0071446a0151403031042050b406803500466484459000d0108040a0445c60035141e440741d0755103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 654454046 1250 654452796 654452801
    0x3070b090d020f0d03020a0302041a12071e1107170f07051f050304030c0b01060c1b120209091f0603060b0a0b031519080307031205010f0e0405150a0c0e04 68
    0x103d0b00e0784140c0c07020741103034080e0300170f049170002520b0014140761781c421200c01c2e03c10340410f01070702040000aa0b83c4409224918181c0e102d100780c181507001c8015140700003083c10914840760304129014009007034401e414041c0c0c500401c0c00b0900326000c41113841070180c07a130900105d0040244a007480c00035640c03c20411040301c0b11940d02c0565607000f01c0710790544e2540d0009000701d0402c261640c803c1d00061a00c000d40303019040950b41c0400e08500c51400351199102c1c12000c0300301841c009410080560004203d00b02c159054489400310b803a0040000d01d032030301190700c99210100a01c0b456880c1a800e60040c401ca03805044103101e0010b95100340701c035050050041e00b108000c00c00000300841c1da02d15442c403081f80003501c1e08210a014030100c1880e011075402a0b0203642002900605140d40044800b21a4410382c40c200055403500e8034000c40f40c071a520a5840d500d1040001405200007800301c15900b80200a200b1042d280440820006111003060381010414040c10090142400d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 654455296 1250 654454046 654454063
    0x312130609031a072715050313080702060c030414310e030405090f01090b091e04030504080619241a270a24120e03070b090d02 56
    0x3255034961501e8004041c00084020940c8040c0104081ca514900749a01a0208090030000c0903405d03241c28540c00340d03462160403607140b041142c24028420074203056600140c00a51007051981c0e00c0c007480c8049005401030391301c00304d4603020201e0009040c82c032003070550100c4401100c9041c0c9541105200081492005500e08114810220060302101c55580010101c040f01401c0300c1c1840d507107100080d800c0e50102c450302c00e8075400300010400d2340b040e80503080801c01c084030000e0306440e0442000e6841c42c480355400c50003080010208080c1406181150f004c2c25000d000c0d581c05281240122409248440001c0c11443c82e054854010040c4203803280b0b00c0b00500c41101203140d142180030003440c101d140c429404000e0410401004290050783d9028058210401c50004000401044407a00040e400308023441481030300c1c0103482c0d26040300b01c00100f005051040b1000f401b803040c2c0e001801305800611540c4400100801444903600d4100d00c59040e00c000ca0b610840c10300300803a128a01c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 654456546 1250 654455296 654455303
    0xc02210c10020a060504051204030309090606050a14130f03050609060709050f01110f2e050601050409020304050a0203010e0f19020a0b0d0b040203010603020a0201140606030a09020f031213060903 86
    0x1a07003e410004055404c4141c00034024000c035500259841c401400725031055104602080400030108580c03030782e03800f601009202c5403c0650400c801200090404449071140010021000400aa4200d0341948001c0035012000401c0c200036124030701b00340d44a409031040c80d958400c000005107203e115513a04025030328043c20304070200300c81c00f0065464910b03550440c0c0c264003880c80d40410f5000200f000000304184000410010000803600c3e00000303002c00e00c03114425041208000503660040111000c85028260059682e51030342801810007600910003989542041030809a111002407802040c66240d0192020024080440c00b180e501c10b000c02508508136080400c1691007690250001122404020884440d0540058200d070301c242c0003607010030340c0842c1c0810103da0911580000c010075944104e40c3c2d0500400040040c00300401851034182c582965504548440c440e02d05030900113012a480c43c20040400c0b0100e401a0128940c4007a103220005800d41c8076035030190031241c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 654457796 1250 654456546 654456553
    0x32a04181506030c02030c1510121208070e0a03031d301c09030308010b09032a18041403030c0d020711060a0207080c01111203070c02210c1002 63
    0xc0d000043e409000c814040c8420360006011202c2e42d00028400a001200c040b0320035900c2c0e00d0209003103010703e6010f4200b1101c1c00d0b18081079200242e003440300c0038048000313070030241c106070b03107481080381c00030000c1c0d039590b0304a503194100200b0190002c4443c083e005142c4006a000088a002c4c0108140c110601d1a985601001c900341c0310068030046504100e146d400741c901d840ca00baa400c0f480021071103499400500c14490800a16a01400c020302400c41581c0041c50021404002580e803603104070760100c02240c0c2002d007110b078208401c1e40443d036800948643c140c86100c6000c100782c0501100d05440544c2c049210710602d01c40841200c1c425000b486540b4109005801c2d1040250800b61084546c40c5c0f812607038100c144d503984041d02e41d0302005d034020800c1c00d08200f20310342801c0c0c0482029040c0141034024900c80040418818505051164480d440755101e50007140e98040240b0080d40040c1e040301d2880901c003501049181481c81030085891001c42a000c0c031100c0000507454100580 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 654459046 1250 654457796 654457799
    0x3050d1206080a0c091107050f0705011b022101060801110301030c0e06060304110303130306050a0e0601080304030201050f04091803020f0606060d1e1b091703030c032a041815 77
    0x2011b0b4005202c0320409100d01d420715829984461501100300c2d11901298030a420402c541c2da40f2503400c00703141c00ac0416424042e0900e41c00300311020602d4440482c007421003462088444e009501c200000c0c010400203011800c1c151100d8010b80d0f0081c0010b450b241c004800c00b040a103a0303c003050f0b0148030050401d91544c2d841d038a6110100020030030300c0c1d40c540802c008012004401d50050800f46005130340c001703910300b00712000704100c46d03d840d203410050300070800411000c2008000d8030116602824426514206070301c61000c1c0f4856500002c180901e041c00380840007186912405205d4400c0d000c0341d01c2c281100d05481e0b610f16040b195140e2040c01081592803518180d0005d40d0500074901e10a0f00c08024422075600340c91a20308140300b511451030b442d02d07085038441c030943c00400300305038210400d40589440307a4591000804030060354030000040f44c400c00c80706006458280041031a01c141d2542a00c05e019144c0c0a80310741d41300200c0a032008000e00314984251100c4041c00c50307454010300d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 654460296 1250 654459046 654459059
    0x10506030129041517130809040b040204050901030b0106111603020f3c0f092208030103030c150516030b01030b090a050a11120f1003050d1206080a0c 66
    0x6200440c01c10481c00b428400060041c900c003030542c1d1880220345503910b03900a418417a0100d144001d00e864062260b01c0316250101c0d44c004212403890700c1c203840114a8445010104001e0b2046601941d04030000b0380c00081481908008030703041e903d1541c1c4114042480a0135035030350b125118002c00601c2c8042004200521b01107640000ca10310142019030a901c041c4102c0407003200b049985689a0b404001e210b00e40c0b0b0720500441942c500803a9000d940b10301090111710070140040519510b458401e002141c1000d080100c0b0050300c1d40541440d590790303100d02d0b0080c8101c070403030021103c0c400402024816440c1c580126481500700c9800901085032200048010b0314100350064103040e55007042c08007c0d16107010301c41c8506c0100901082d40d0422840540845290211a00b0f05100034010840302c0c1c4882088c2c10b421401c40c0811450303944409070072409107407440d84010121321501c880041d03142d4010b001c058284480f90020090150b503800601e40b205038519005002d1808030b142440340 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 654461546 1250 654460296 654460349
    0x5010b090f0114010908100c11030f030c03060409120e101b0f08090d2102070b0706420608010f03080309010b060a08011415030f1506210105060301 65
    0x2560149000c000c1c45e80d445401d1390800b02c20007000d44105031035189130049140c00c240400c140c080300f03000542c5040c440918020700703404003808003482400008042405a525600060021500301d04401518080500043c2c81110030000003401a035800c80683e600c17030b0080d038a00102130706046410b0088081c1d5030b01c0080c5d0801c0c0c140d0440d5090414002d60503961606240070604500c11b241c175550204200307240244942402000340210350224005002c40c010044c15103104981c8410040398000300c015140702c0481c41c1004c0c40b0454401401c0f010342450404c540c6001c44070420f0070000c90f181d00e03040b089802a509010b0a45a156800e10400025550000540d8850080000001c8681003500000e100d030b44131030307044c0700024542401400b018051018603075a596045404954007101e80c0c45c80c3c0401d01004000040c0408a40300207000082485c4040684c0d000081405e81d440e281c0303100e00100300c0c40108048040d19000c80000c642e606121040b00d060f2101081800c0a8031001140f00701d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 654462796 1250 654461546 654461579
    0x30403030608120d1b270914010314070605090d0512030702070e070813020103022203060609180b060f060c0303010806070f03021c270501050405010b090f01 69
    0x800d03641d20340c000b410b040d040c804080756144040c442c90f6a5405403281c01c0030b440c0c1d414401c216129103080550082d5800c1700354424008840700b080d40000682c9003030300c4c010712080d5100250503400e2250325500580341300c01e0135040c1e070306c603443c01d240c0160281941540d901442c010480403d608102407042c42c606407400c2a802c2d84200b00b01c1e24401095071002180341c00a07198400503074000c14051000400703c080c0c01e9403210041c6001c0959250807000e2070fa04060203070010b03040c540e00048010056035400c18100f11400481c02c0c482e417503544c1c1d00d80f900042c01d180c40394003000f40ca410001030b1a018441524068160801040030041c0c64280c10440a091016100b56010108010907500154140042d5008024401c0904094640710502a10042c08500d90004151040122601213103401801002c2c10407003100000c1c03000d082820b00761061244100d1084106030300900c0004100701500440e2065125000900280c0701c0c12040c030030018001e80380c000340c03c00202d005004402601e111581d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 654464046 1250 654462796 654462803
    0x6010c0219081f2007021909052e14090c09150c010606050a080412091a040f05010c050d03020d18052103010f140a15050409140402150304 61
    0x1e000d140c2c0d076041a8640000740800c103880240f240c03221a2110407a1091900c6116a48020100f2041c100d00c3c089041c424224001c0c4204001221707006100c000280c180050201c0329820840741c1420169642101004a40c22840e055400c0c444505100481103090032100440650202038100c201040591000100032100d0341905201105040d92440c0c101802444484816039507140e4074202207094440315049031061000401801028561240e040c0350701030340184003003800400c20700e803c5681c0c00143d44488641030b807000003c00f107010345034001c008a5074604100016940d40710019034849540b41c10240c0140c100d2071a004d5164000e030010f0100580c1c501c1d00040d045a480904100f4011030302e82a00c07250320401c041d0302049010380420723a00859880a540c119032601041c0d007005100d81c0641811401e6a500d00c6005440742030307a40300900030120300c0e0321044100f041c0c01000758005100b180c0c40c1d5420010001000c4e22103500c0c090050303402601c8100700c1c9004140381d0038684c1c0043d2040703 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 654465296 1250 654464046 654464089
    0xa17070615031101030912030b1f1808010606270e010909020102150906061e060a080702070f030f03030b13090501020c0f03040e012105030f04030c0b0306010c02 71
    0x490000341030303100300c0c00300d5405a100e080c0c0c124118203000d4244440100d02c5414140b07406107642c0491942c190840c4c40350290700e00840c1045110005c03407032079a40300c4230001350185081944504140c014500c40051403d0301c94078121141d0f41c8400300e003615880d128107400305030310a102c038428130400e4240034140e0031141c0d040c2c20100d54a8002d400e585400340c1c0441c40180e071740c00b00a41150790502000032954000200005e0794104814450785504018112610840c00e5040d983c0b0648256028060503110003030404c0d44a810f000c1001d050f2a01c1101c03084018040c3c0a008117010003001c007140240c80d00132080410050b40b6039000c0e0010007500300c41c1c82e40075402c1c8500c0700300c5140c41d01550200034425400561201140101e943c9000c0000105140a810a0005105c80d80010300140d0440d00350252a08032500002c1803003803103409e020400b50450100040018900c80241700a108a0f8452800c240016558000f0b450b1103001c19a215030020344405009802340c54043c944110705202090318 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 654466546 1250 654465296 654465307
    0x10270f08071a04030e4b030f0102070201030c170a0c0509030118060614030606100e0a120b1006080a050c0c0f06041103070f03060c0c0c0806040c080c030a17 69
    0x810803442d0301103a04400052007111048550b0510880d10000c14a1307440440ca9000d01551085c0c2e9202420008410003c14498a078104040600781c142040107001d81aa006a400104081d0207540720010581c04203013010000e03641d9610408030213507103950302070038080ca6480340c440ba44064000041020200601400924030540e001e11a0704100450f821202491a0403442c004003a58500d602c02c54140c0c04c401402d807000d071400700c1c00030341c0103208484506401308801c5e005d032440d0688400d03080d00301c0c082507400728141300c40c400400b800d14051380303030300803580e6407404481c070718a10601445000541074008200c001c1c034560841a0051084170002e4104101c01e44403038a001300c0c0808024450744040140301c213018401c0070a04c00c2d118140c0142440034204003005066114a1000800130780c0d54081c1d140100c0c0c450769801000d280d0001301a2034072507561141356541c01c0f0544095034036168891000902201c0090040c4520078050058408881c9545801c4c8840c0c156160040181404225 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 654467796 1250 654466546 654466583
    0x1003020904090b07110609060c0d110f040f061719050403020703050d1706180403050715022107030b150d060b0c240f012610270f0807 59
    0x19418840d001e03590b43e010f810800e80504506c1e200000e17041d48103940020f42881942141c00c0101c5088124034030001c00c4c0d0020b1030002c10801e20034035400d41041d40c0c1c01301380031034011480b5181d0012904a980e801160040c11581c0f00540780d01030304c4011a2030b102101e8403940007601d411407548103000e0700581d00d0243d030300d440e45030420584054400000d0b42162101e0701c25100066890740103031041e0790301c0c6c20300c1d040e21815a000040c00741000d0140a404103a40c07040201d00710070300901d01c0003148159240c0302440f40329801403010001c50209601e001c000a02d03c00c0c424030507035100307230001058841c0c000400344007034503039a10800c61105026100c03000428100c015400030145980c2a00c000c02080c0c01d030011007019619010070500702c1c040400140005004191426415242e500401e42c00d040b007030081681d03144004005200e01805440207104218489500c0106102490351400e2000c04014040440381c000a80000780368918002c04030011034a24000390078124841c0509040d036510b80c50 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 654469046 1250 654467796 654467813
    0x403170f0304171912060605191103070f0302011e0902090a020a02010207020405010f05030f240a0204030209070206040212030c1905010605030a15150b07060b131a10020705100302090409 82
    0x44c903030010900712121205010314a00c01c0500400291a1090801071140060398600d00f01190b22400c01600703a100c2d04a0b100706000b224070301c0b42d01040b1200c010500b886c000e8060440e8408070031080c85182c0140e4101c0c109402092103965004001c1c004607030310302c41840000c3d007103160362004641d401d0100c0c00061b212442102e000e0b00c000e401c080141032070b000415142541032020180b058011039130300c24880841c0c120700c880b86001c400d1100040e9a44001f42c02c000e00655101952100bd0754007800101c640120b041c0d80524000e5401c044150034205d1981d07541d00c2087c584510030760060414201180c048805030740070f940b04034000b01c2e00c01da403100001d103803051102e0255882d05280e201850008014410f01c0c0100358640030300c0941c10714155030700b09903005200001d4141e1b43c0b80e0749003a0b00c580d2034034400384403114402e0080029118484403403601007486082103004000001c2007100c0e05000003004811148018002102e282804404a019420056a941c0c119450f00340d4540051301c401c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 654470296 1250 654469046 654469087
    0x23040f0b060f09030c0d0f030c031e0503090607090f03020105070f020a08030d0c02161809140a0204060515030106181505030405060601080403410403170f030417 71
    0xb5940b41e11a60a10101400c0900840040b803060300041c01001c0080d00e01da9000c0c0c021074140c10002401381e080d040940d4040280050124156003920b03a050341d640d00580954000c000c1c520403582140d40301c0c9010b5400748900c1c044c502c042d81a00c0810401903110f00002d224441c4100030004001c405940410f42d5a04160016401c0f03800c040303140910020548501c0c0d144403014030003002c2061440c802c00300404000e00400d460181c1d8002d001c01040407036000300c8103147d80b0090381d01d40c00c548a00074a848060b120340491117641054000203140c50f00b48045011100e04d6000c051450b4640341c0e054600070642041c00f1020001524001020090030100910f03004185c1c903580c1d607a1401e03280c4103050000060810341804000340c10721000c40c0d071001509030140c140f00c0b01c90390301e040b0b20201520382d00c0310191403940303580750243c81222452004000d041100d2160f40d461606068500c0c08003410b020b0480c0c80c5410010920000340807030080b041c5101d07240d140010356440e11700383d0203c5645001c2c10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 654471546 1250 654470296 654470317
    0x609040e0102070314090d0303020307020a1223041404051b0708040501110d08180f0106032102030432100305091606051206011110050f0123040f0b06 66
    0x3c01c01c04145070304148108003002801d50f803a45000c0b40d40300052412a800b0320050201640800010300740c5008001c2c410719140c20600061148006203c01002400e500340d40031b10200e411207404500700c0e501010356096604280074a51031085c0c0710240002084d00520815440d8007001031140728180310030003840e07002c0c01003c40300d60300c0b400c11002415040b05040070207800c0e80800c4041412691003114547c0040d039640103007400d61034800d800740c50710654814204c070325460844d0004c00c001250036500036004412a400380307040840308040c3d03202c4c00307144141184510200c15142254648070500c81045034101d4603e401d50301e07401c0c04600c80c0d03071011700c120f00802d5460091080d02c505c1080180d159100510051010a007401c3d4010618020100c034811420025004908035078050001c4200c00e06d03030300084600a200b283c0815004d81000e81d2280184502d18001240700d02e0044040041072990f07c101500d680700c5030707040c080181000c12440c903185980e03034510b92103943c40d0801040324014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 654472796 1250 654471546 654471551
    0x303040b130219060f050c0c04110c1002030406050906061011010908031602010605030f121b0f0a110102010c140315030f100b190308030408120f010602390609040e01 73
    0x284134020f000000380c08840010301c441071246041600700020200340c400c00030f076404102c1c0100c2a84100f0a4007c84580050500400c14061000c5a050340594492405100140019121640f4941c1c4400d000d448403608081c0c04003550707480ca8058003480300051040d500000d451280e60302c5503030807a082a2030826045104120044007264240070300c0024202c00c4010307003900008959101d40c0c076801c0b82c81c0c02d10f00c03100204e40441401030640500106462006c00d80d00202c00d503924250300c440c600402107940220741c2c0c5080543d07500c140300e42d050b8000b05865044400d030114091030100e40004007100c681c01200c00302c410407620184445003101440768002e0960108a030728540548140c4109a4022440c02c1d4903a10340001c00c20902d030031a41c12129040d903d03203460a046003588985a0803031804009101800300150001100e181282c54980c02d503601c0401c2546445009410902c0c3d2044030251680d4650425569a103851250307c8000e00071890a81d2020116050300c0305041401020396 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 654474046 1250 654472796 654472799
    0x16120516020d0f020d030f0603020a092403110114160b0603071409061c1703040c0902120a02160203102310120f0b10061d030303040b130219 62
    0xa404020502031002c0034100003a0000c0f201070020f43d01c2038504000400c141d00c5d0a0040140501c9500c604051500606203003806504d801c0e00401421841c1d01e24241d6841450581c000c500000401c2402e42e64004007401c807280019004441501c10007199850540c000c12401a58104002a00a03503a00c01e911100091500f4002c0508040850f0701408194540850b12801940d40c188004e90051046551820312459100090b46903070758124010043d645c2d0b0b0f80d441030071084440165121340d1181142442c00b5844a030807001360700404d10708451040070800400c401141c16006403052403100b0b014030144045130f0b000a80b138500100250210581d840c4141e007030b00e556005150102d8118402001e5960071f000558011110a9200320b1102e165954641020030443e124074440054200e82d8602c0c09060645c2d4441c407191f0144154400701c0c0d810040c10b1903400c0100454072141000601035401c66a075515171810804005040144001c030a000c0000140d4441002c0818030000c1000001076070f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 654475296 1250 654474046 654474091
    0x3080a111b100c021509010e250b04030b061e0301022a07120b090309040f1401092c0304030215030f0c070f061e0c02030c19050303161205 61
    0x3407071180c07a44444a04001010083d603800040d09648000b60b200c3c200042c0d96090402c0b0300400c0c030002191818000c1080064414101701e4611419140c0103180c09c08580d03864908040134800d41c80018003a0b4009000202c0a01e1306405040c0800e4480700c149848840940c0040e003240c0c0300700c0301c020307900d0b04100115400c0001010072241d11101200101041410042c00203d1031806940003808255030f4000109008420700a907818400050814480340000d9540d40c00940620440d60408540ca01e00019064a5034090b01044000c484000d10800340c01d00440c072814481014001143d2000300030020042e00d6244445035a8161482566200d00304081d03004010300c2d0103402c02801000a1150710040303481403542c940b08950044c4009071000e00d880d0182e00072420500c1000300c0520384000c00c00c1068010009110011100050320410850584600002250a50090111341c42800042c1041c680900140410806410709010400403031302c407003041d66801c032502c070200071a5481ea2000d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 654476546 1250 654475296 654475303
    0xc050a1101060e06060706060302041a040507140307140906030708090d020303070e0111251806030510020702190807170606032104030c0e06030d0f020a03080a111b 72
    0x40035080024081c803460028645102d1901410542c0b1980c07000030702008004c120340c045001941d01034800e12107400f000da03131100014628018180a00d0400b8006050148102d4107402610440b0f5007880c02c6441d03031881200c02e001c41000c0000302070020450100e49a07107101c00742d13210b0042c0c0e9481144d03e00d0104100c604126511002005661051050041c91074200d005440c2c0040b082c0781002d40100700008071441d2840c4c0110306a03001074003482c1c00c00e2241c1c003c1900f400b51741020410701520744042002000b11502c500c0090110303084007100e1081c9007280e40042c8460350000f041001c111813002e841e0030510031254010300850744102420820250303403210300c001c1c0c58089070140055141503808652210701840340c298035904c50b00e54502110301140b0641d0041d6401c001550000d985030b00d04101194410f0b190a4864407560586812081c420310043c01c450f56564050310325a4170340d40d0140c031060001740c01c51084585481e16000d0300c24024000d4880c000c500952994104101e01c2e4890a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 654477796 1250 654476546 654476567
    0xa0504030201150b0315040207120c0507050a0501080426040b090a0b2704020d0207030323010f062307050102070606060513231c05191220010c050a 65
    0x40f0106050000c01a6582c2c48013900d81c4800056000c458040a81c00050003e200e00d10005100700712030083d00c0d6402d5404060141c509106800b2200d01c1c0e5281d00030007611310f00d00d00c20355000840440c0010700250303664451a9044c800030105100c000381c11603420075503070042e4002c400320b81c4000c00c201005141180031720008020703402d1401d00e890011410300071800b502052580050100494481450303c8a03412a40c643d103a90303500b1522603029140040180c5903221400911800c0c03000242106608000602d04a03078a03032003415413440c54400c040c0d400302e01044001a981164039400345c5885044001400518491000103940f04980d1600c6400c441c81604003208102d001d02c000003104030f0540405040c0c800110000701c0d034001e112400f8070690101100d9580150070300c1140203402c030318001069032003446081a60f0740031116038031210441008000c06000388035a0603080030800c1c01800341c04000b2001c1e4003030340d60000101c1041400d50321000303600000910009485401541d000e4440c01c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 654479046 1250 654477796 654477821
    0xc0506070e0901050409020f270609130308040516060906080f10120f0f05010c020601120b040f020f15090f012c120d02030301060305070f1d04060e0a0504030201 71
    0x75400008a002c901c0038941405400e018903a207100c410107642e180b90700101c600c40010042d4028410502a44600d8010400c03919a48035a800200760185000c0f00700c03500c01c07189800d50f030100030140e803012110520044e00c1034415005840408110082040d0440040e19260f150014002d20f84000181504002040100c4040c1d28800f4402c110083c400b6440894040c204101010b00081c10041c505842d10310005080c140ca441ea914104001904109030314000c0d5001c2c0c0300c89030783e10800080c5560100f0001800540b0500002c0d00182c40c0c0605200700310b002a000d01c0c2c0c145400340210702c4092007809032a89001d030104207a40145844d00b003040d601d00c428608521603203400600035030f12034000b43c02d06007280300c2c1d064540c0351500c990548103040c501800488403101520000651203601c203000e1200021b04200016000c0b0307000d103c0400101599030b82e0740c0204549051424100c402d10128036a0040e21182c000445c000c81e41c0000c0d0246482e082c000456051924000c0e085406112058 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 654480296 1250 654479046 654479057
    0x1060804230d0f0306120f020301060501020a170315040207060b040c050403020109140102121c05060906061b190b06030f06100603050a061502010b04050a0b03120c0f0d0c050607 78
    0x19444000042000701c1400290300700f0400b07600456034294080d2456400266019802e01c0200c81071080291002e0b99a038001d0700200092900d42c0700498840020130701c0909043e1000d501c000b4581c24a2005541c4000200d0380803484040e0000020166445208180e44041c0c4032541015076240c1445000c0344015941000d174a0103145500107000e0440600c141107541054100c01400340c2d000780011040c84600d1540e040e42c0b0300d001c80d0b030388016120014003813005a2074034001031054148980880c1c040d0000800d96030425220b030590844103070225001d0b821600809602c800301c490344031131410406200313240d480700e0b40c80c006040c946480090105405a40d100c0d00511041c0c081a500c5041607810501c1c000c6150381d03c002c542c40140100380d000124040c600100402599410741c803004641d0000c0350244a00d40301c1c0c1c1e9111003a01c4010407070a52682001203102c2c032078480103004142410b94807043d60007030f4000d0106c05003002001a072a40200304021040010030400f8001c481c1d1200d02414603 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 654481546 1250 654480296 654480353
    0x70e070e090f011206050604090b1006080c072003101a180402060712050712030222150302070f05031308060702010e0d050304060f0515120a0f17070b01060804 70
    0x2c0b08004c03103418001800841c0e848000c150940c44581054180a03007007068418581451040e22059814901c40c0900143c8900c010500c0c04410314121000d00ba009100d030f9404802450807034180325280701001d83e052140826210b01f0107460f004002101e0000d041845007551a8000d0000502c1544d4200c65906000c0d000c0000694a20003036403000340c1c010f5400c20f482202c10030285c85030b20940101801480b00011080181640f540041c500e852142000700701841c803d542c981085405030041c0c3c52454294503660f00039602c00d60141c0744485c02090351a40f0802c07140c46150540e03105e030085400c04c6c1c1c0b010406000006040001a8000c5024030080181890729500151682c4c1c000c0d000004110000000c03030700340400c2d50081803450245100820007801c200540038202c0316404000ea00450038002c1e000c080344404110040d120341c0225032944004040d5030b44a03130105030307503025642e0304505001c200080b13001484254007030300c0d01c0d8480d00c070740b410a801e1040f40802660704150208152080d07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 654482796 1250 654481546 654481559
    0xf0903120f0b15070206210103030f210b1314010e0c0313032006090c121b09040212061315020301060e10021905030403021306081e070e070e090f01 65
    0x420000f1200096120707610f60603507100049052042e1500c0d030724102140c8034107148114910580d14100e274401d4950244e000ca1003801521206a284040c20321840d81d07411a0000e1f492075040050000c0001300030701c5601c0705442007401200e051288055144120074010b00603841031006040d0842c8100001c0350540c507001d13000140004e81c94200508001070705034019041119182d0b460a8800c149068940703a01c0c2560700305682d40e40c015903242c03141d1001c01a0b10424440401d109810f002000542200c000ca034405000441c24003a004a030420000160060900c07418040c440c01180038003007030b03011b10b00e00d42000c1c110682c0000a8881c060301c100b0040052540190004074188029240c0c040050340031a0103a0801a0031000102a400007424007000c20a000c0001c1054030302c00c840100c2000e2507104c815044554501a940340d69004024100e100600c0d00c0403500c0d40f0185000b01d0b030039180c40c0c640062141c0b2041d242c03800441c8500d0917014817032814241d0207520030350b40d689441c03c5614100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 654484046 1250 654482796 654482809
    0x3060b0403150b04051602010b0907020d110a0828050a0e0d0303060b0c1e010c02060105131b080114010305070516060e0f0c0a080a0206040302040f0f0903120f0b 71
    0x4002064424407400e0b000c00c0000c2904510803d09006000300541d28002c28501e9450a1a80102005500c1c02054445038030300f0325112400394207250300501d40d000c00c20388180e0715600f128800000d68420603c400000400100052400702c090b84010001001500e01d0f02915a004204040a20a0601c44007001c41c3d44101100c5208400f215124031031452030405400805035a00584915040002c440d108040e001959031031001208001143c4041c160b20804d0880c2c103201d443c0c10050b007010307004004a24040ea120007011400c14000607241c9040030041d40075440c2000100042001a4010414401018501203c4010a080602c8180741c405030042c003510807182c0000e03d50580c01180c5081c0503071a40007070325102d00c10702200c0000c1501100d1543d40c410f800d000921030254058041008600440c41030810b542c083d00e900c1c107040c1540c0c20040907104140c21182c00c15914058210680d1090003000c81060281d1a01070034a01040c1d000c40c207a1b6039020442e0542424200111f00ac0d441d0034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 654485296 1250 654484046 654484049
    0x60711030a0806060c07030302030910080c031b0f0d0603030e01020a050c040e01060b130f0f0305100c171005032103061309080a2f0c010e0103061208180103060b04 72
    0xc2ca0014102d40d5128005141805080d5010303d091007a224040101a0004001c2042640480e40c403400400410030458605204070340724440780805001103102e0584000928000390410440c4608140e001c05540705503400819506a4440d01d5040400a040d084001c1140d50031085c400707000703420080e8489550350000542d0039402543c3d41d1345074840d4000294001c90140001c10543c0e941c50310b491b10050440f481d107000f1915500542407000490208034091501125842009400d52043c0f4441c0d110003424400002c100740000c00000c00d81b00c40c989103000f0300c204500c5c621244a64284824146814005200c5940350200108111413200304c090580c0c2c3d10030783c01c075104102d0040c154401000303011100c0e0024885080855200000b03030f0045100d803511101407041d0040810030a80b45044a1900a28403040d500302032200d0320154480c2200508a00c418100400c1a5507510b000ca8000720140303500f0b45041c080401c0c8031038400c01581000a4038032003482c05104441c100011b214042c400d9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 654486546 1250 654485296 654485317
    0x3030a080c1303060b03070f1a0901170a0c0806120a0b0c04080105010b0d0c05070c0b093606030a0209010e0403170a09050114010608011401050705030d0e06071103 72
    0x100000c41c0d52015504546012054403800c0c960a50f0f280b400502601950032402e120b8043d440c80458821809451101120201c284081c8641c1c0c08901c42121039000c11521810000440d404032401641c024900f405800c101c2c03000603e82c084c10200401d82031000d040c0318401e21000744420800400016108440c42d004404401140c44100d8078242c144259840b480b480d5013418000225070a4480290041d070012075401d000c00380c0c4c03a0f101100e040c492014000c0082c1c0040320705102c0c4a6000300603104501024011808a43d005c2e4080018140c4680006d01b650f404400d05005451140c40910f400c40415001404442c0303260f400070743c0442050042c002040b49440000b401d0610a0030042d095014651420090781010307621003014000d00242030380c803507081c403c2000e42c11108801c024103e50044e5034403405a401e208044511508011000741080010710075180410b4041c001008003004c0c502000850040740c0340654204900100b040042c070040f0251603140000c04000c4803c071001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 654487796 1250 654486546 654486557
    0xe0c0f0f09061819141c0b040f0b0c030f0a020d090611030105040b0a0f15090e0c0306100503190c0302041a13050a141903050f0d033608120a05010303031a03030a 71
    0x810841200c6c0e6042d000401403c124901c82c1803000f800b94500040c000366020300702c52100c1e55940d120884540c401660700d0300b00c4c8410b401c00214980c400303038043d00304c02d440b4400104141d03840e911801c051b40e002c060b03006501e1030004010881c03460607104030703010318405864121425180810041c080c0da0148030f02d0140b0500070704482a01480741030071030007508d07044440c3e10050500d00b004030030542046582e1401100042c180c540720f18064070a69100304c4101805032024104203565001a050100400041c150280008942c00b4409514050022030602c0e84a0303c1d4a05114091100c0740c4aa000728090303901403005004035094083d039502c0401c000c4d640c9058031030807481761076000f00103544044c0090296203882403a03103c0200d0540c4110700c041e03a0038032400d03121050f0581ca41c4072080e188d42d90100800c0d104102ca05506950804107801560280c0c1001d204030b01c09812000210b50030f90139190340314011300405425110301c4060080c0c65000c0001e0301360390800320b542d80c407c8100c070209004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 654489046 1250 654487796 654487819
    0xa0801140a0c050f0c011b0302180d0305190e03011406030a06090f06020d020304030906020d021f020d0e0304080706141c060b0d090209010e0c0f0f0906181914 70
    0x500a0342168007141e4000201a501c000c02c5c403d107030003007a8812140c1c800181442012010610a0003515031100584903603010518600c02000100d8180490403010708c603040c000018040d00003400c00e00c0c000d1030303912803552400120081508449040000c007640258440038071069031030008441885903400714002a0346002e60070203080d21038058000404131400000c84113000c00a40e0040c500480c42622414a02d40e1140816030720f030041080d1120060b400129000b2000c03000400b66501520541c00c01442c125514001c4000e40792100c01c0300005a10000d020401d41e0000c000400c000c150343d1601c16603541c83c000004140e40f05d00358869407205081c856140c00e04070340c2e030702410040c913007000c000755120745035400070f000340c59100340c117911454410000041d0f0688c4040c000740b2500b01940e0b00d038501000c0c0e07a0043c2580e00300039905440c51400740001e10b82038660034000c00f98166625540d402c5d0740000410080e491004140341080c0300481502040344141c240c222800c043d2040780c00c00c0190 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 654490296 1250 654489046 654489071
    0x13140d0917010f050411040b0906060904020d0f0c0c0309060f05030a0e15280e030306091003170d0608011b030c140706020702010905011e0806120102180a0801140a 72
    0x4100d25091055990f02d000280b01c1017201d20038081b20101021354082c0310000011080102401c4200c40194004004005250031860641d0041c070804000d01000200080d80241101c201c554603100500400c2545880c942450342103208030300144228a40440c1655082c08014407030302000d0489565191140400100c1600602c8588202a101550402207191404004140142641c83c00d60001c50310400a650f410355401626265140740000303601e1600e4050910039444002880d41015244940c404000183d14200038442d85800c8640140c544940304a0b000c110740c809d9206003204c4c0c0c54002001e000f11078131f40d4100c403411040d080018111080c034800b91004800314171285599200010500d040069581c00341032028000e0343c072038102548640042d240510200100e08044040d1003210f00024454204554008009061118204518003006081ea008040192442001c0130f40b180324500b82140f2840003028040020310540d012092090308101700039040218060322025401e803c1c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 654491546 1250 654490296 654490301
    0xa0f05090709150905040c0f0c14070b070302060403090609033903030914030c0901091a1203030a320604090f0804030b130210110a020913140d091701 66
    0x424442443c0d03c4001001200107202d00c005015080c441c40ca04900c4c070701006d00c2070081c04110310094550551200003619012160101003d51480d41e200c0d03410302140c44222400a410a031784690014459410030b81380150103d00756810500412090003020004504411980901101c071100d6000c0c1c601c0f00070b000c10400300e40c55400c001460260761000001c00d9403041805007103038840039240b10a001050109604c0e58820305407a43d104040400501241040c2d03407003071040280d82000d05426440110104405101102030040903420200800c045a02c0c980074031352440c4103031400c00030805900114441e1180180000c0904624203000103800b40c0c56661107a0803d41e000f00950740400c01d03c0c9041c00361540a404120790481c0c01002241002201e40b10710001c999000300300c0031070340700c0c0440b080300c486580d200000f07610702c2270290040242c1c0310180b0040c0a46030007002081200c5042c01e08542d141c030800003c4a80c0c2e8070010348402c0082d4080d030581c0503108502d41c0400079070b10f07281d0890701 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 654492796 1250 654491546 654491549
    0x507050a0c0b0408060a18032001110d05061005030a0c021513031206080703020108130b0c090a050609100e03030c0102030a1b030b0904150e0613050c0a0f05090709 72
    0x10420720740030a42c8901d5001602c102c07aa484115207080e501c032084441030768655480898050f01a00040f0006401510318a0700c1500c00d08002d0844003818101509440aa807e480740b01703071000070201aa0300881c0a01130f4003a00a50b902181401c04481c014540d1000400008400340d840030a106064802c0c4405401c20649600d060030a0408035505070a500c178100e01200440d54109290300414414040c2c2011185940081c0640624607001502c0e000b03c02450800d0581400c0300d4003001400c45064180245445074a00740c84844540c248a4142e41d81c2c0c12070f40c0b042805120080d410350b0b41118001c801d01d45860001c000140110109145025459003c2c1c1594000310800121812030790201502c1400e910010340d01c02c0480c4020f0381241c2c0711480b1242c101da18800080d01240b800300d48401201d070b420130001106074011700e6442c01c021040d2601103194a942d81c0307042c1401001c1201801e010f42c00c403101c01140e03180c01980100c0030a107110300c0340180c0d007807800685802e005a800d1320 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 654494046 1250 654492796 654492803
    0xc061506090301021b0114041104090c08060910050109020405090112080903100c03050f070c17160615060302030603100b0315040f0c0f0b0d0e0102251e0c060507050a 73
    0x644400d1140c44a4140030034024003074401c6c0d803814121a10640d042c0e074590b03000d1a0007000007103254100e8401d20001c0c00ca41a07040da4140c27421307500001c2600301084124418a00440034200040304145007900361181070340005d80841c01484288126075070fa440142c1151076940880d1204005490000307201e000762104543e05004102e9460440c1440342c110380f000c06a5540c003003149540e031003e2483d8940d001c3d200c9000040900d50084001034078100034003024a60030b00001d007040c1ca0342d0004800d00c00a41d404445072a12151944004203045034520003804181c2415400c500c0c100010983e162842140306407081e45540049401c0d45041c0012501160304c900718403403529180c208111001c507450012076100d03242c2d80c0009047c0c0d8864204a050f50019843382d460134880390420009001e413003000c2c0c101d5540c2000880c41030710804000200d9281054100841c80400f070402440703d1408484448004400c02c07030210004481850500c00d58003241805500c40005007091407070305823401d0005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 654495296 1250 654494046 654494051
    0x140a210509010e1201110331030c050f030a020f060a0204050d081804141603050603060a0b0f030a0b0105030708030c030f2115150711010c0203030d05100f06050c061506090301 77
    0x2c00d000349246004612401146010f2118603c88c804805c041080ba40d0044001003884442c00001a202d800c502051900030401c940c00b100020382c0c100c2c21540640031a4015900c5a100f80030070b41424404641d001c4001d807402c5081034a088085110044203c4e401480c510340051852a0f03484480e4014500d9040507008200e8014440241000800c050740e800f884e030000880f201c0c605610074044c2500c0383c08003070050295601d0b0f0300d1a607805000c00044441c0c2c807048464000000b51020042d080d100743c000e480846042d4500800d25060030950b070810002034000b080b0485030b5840c0081211042c0c8903c417641a651a031403002c0f80b500d4441030f0843c6207403010410501410070007401e036030019120103d07246e6043d0042265420322038821900000d014980500165a896001b03440400e5203074005010350380740c00c0c2030302c41c00e1007194001c50304840a0b08000d0024400240028030410140040b03040091800d6400400340d581e950b4014014070000e91050000c0d0070741d07201c80060f00c502c0030b400f0b4001d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 654496402 1106 654495296 654495311
    0x50117070e0f03011d0c0a050a1508060a05060a09090c0504081b030a1202011a121b0609120a061104050603010306050a09140a210509010e1201 63
    0x40da40f555a84d40b18480900c00402c1031100c19240b0340191444002c140204001404d007078020601a400d51780060094181a41303411001080c1420030f001c02d5658100050054481c94125940181c000f00707506c040d280c0c01002c02000d84004070414000c0920b000400c03a01d41c052880f601e040780c0d02c0403841c6801075241c481e21010880f005410b440c0741c000603803600340c0008800f003102c6005070754440200106103103019080c259500e007104d543c0305c0300c0b0840d10710940d0b520030010020042c0100002c40c100170360345c00b803c0768200000a00740030181500c00500b583c40303034009801640d030542049003a00560301c06038211001e840006210b0b90869095440340c200a100c01441c4040243e41c3c1c0300d101d000305100f640580c500c1c842c601d004028850f05803409500b1620200e50b4030203c0b494020242e07003a284c000302034035001142840c0c10000d070340001700017480303030300b140030000740503501c1d2000 = true := by decide +kernel

theorem cover : BRFrame.Cov 654316546 654496402 := by
  have h0 := BRFrame.cov_init 654316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 654316546 ≤ n) (h2 : n < 654496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
