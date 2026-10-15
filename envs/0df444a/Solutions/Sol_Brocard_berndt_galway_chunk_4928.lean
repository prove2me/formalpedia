-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4928
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:11:06.138018+00:00
-- url     : https://prove2.me/submissions/dc28c819-871b-4e04-9730-2eaa3511a129

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 886151079 ≤ n < 886330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 886152329 1250 886151079 886151111
    0xb010c170d0c02060c0405060d0e06040303141b0316090f082803020c040c030605120606030d0c0b04140c04021c0b03011a010e18090706180501090e0a1e 67
    0x2c01c004400710b4026000740078814030703480e083c5d506036503040302c043d5964060f0103803002c010460b043c0c110086029442c2003000381a0107a0080740da42c400c114a110141d81c80c10b80180010b100e50107059990b4000740040f80340b01310f1a0a0120108025047c004402511003a0074070082c9a2503003d03403041e40c030400c200f54250041201400e20754200001c0884405902e54001c1e4590007a0f252207805a43c0d02d0150403111846900141d0040c800644640100000c0b1800d841d20b50100f211043d00030300c00c03c3c04882078140f1403103440c10300c680c2065204120b5281e980d034103600c42c0c03020000385a1a100340002e1140d1382c1c0d03c0780300601c40340d080810119002c008640c01c0c0d5040d00c085c0312642d44664944610700c40d000c4140b0b000380700d05003024a080083d050307018000640645440740a0081c0750a58070820203403000000d0380c102038808036111240c0f10200c200c01d110078103405006160005080380020065506922100d03a0030085000000c00c18000001c0381d401c410f22382d020f030082c401707807100600b0b604034503c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 886153579 1250 886152329 886152341
    0x4030e030a0f1214040807030b012c1305060a062108040603180606060305091011120601120e01051f2d0803070317010b030f0601030b010c170d 63
    0x2095000e0250280d060322640380401505902070b20544100500b201950701c581001090070b84604100c0385c8560310340003d02d503100c00c140030442d071203c0950000f0a1504550080c19464506505169400a965181c1102d000c00103070400f200e1a001e001042d0015100703000d070f94415051402c1c002092031a10301c00161600d80150032403035180d50103107502c0104098808680640da458100032884000b821801c400001074100003074042c0d45016400b058155054202600035000402181d450034404580d02d4201e0b2455400e01a16010403c080030b8140c0d2500c1619522090505014580f01c0320203110314240d450701180302000b40d5484040011050001d80c841c050b103008440040c03006824085201460020100780c4680088903e49030300c102031003a00030034050120102036030f03140c410518011380350b032101d02449070700c0c2e44400e000803400b9224007042e00c1c40b400c40783c0d48602680c0c6421005400500b240f080080c10060b039841c01201044101482d500360200c10840e9580d40d0000c98001030403140703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 886154829 1250 886153579 886153607
    0x50f07181d0604030e030a050a0b0703110f1606090b102301020601091a0d050f0d0e030d0309020f03030403080910090303020a171215035a060403 64
    0x34000c00c00070801d103000600302d6482039142c21300441c440100e200217031a180006400804502c101c0d1070f4101001000c0c2d800700d00641c2680c03810301505e207008100407941d0042480403200c80300e0a12400d00e4590841000306802401000f0015020b11192a10000304100312120300100044110400180c10012814801802149100c5410f80381741700000b901c40c04180700700b81c0465201e40c03841c10722442d2000c0e1191400401800301b505801d191030215100e1340d41c400580100d0195046981300c0e14010042e01c01c0300c0d203005000c1c00c503c80c1c904005030001d044801c1c050342c00034070040820030640c40c104021b03c040c40c090002107403078088403c100020b2031024088441040305030802000003a4001525100039640b20b1810070050359020a450624010f9880000000317100d1024084002c8104c0d01901440c2800d5055403000309101100e00318052103100c2440340e4010510f00020721150304900000d800000b81d030310084492501d035605818088400b004100c5d508204148001c241d005074840c04909 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 886156079 1250 886154829 886154861
    0x1207140c0a110913111305093012070207030c080a020a05120727060e1806040507090e0106090219110715052d03011d01080a020409050f0718 62
    0x840c0001c3c40c0c40c4d9007525800c00400c0149512031149490ba50b0801507008580202c03801c2140d46044252256540d2050b070074540c1e460259540c8004200d441c44032003851341900c01c42e580c03070030300e054404560392074009203a1030450103400004030000b030441500c0002408404002d00c0e04413507d004100d641405a80701902c03401c064090781c1d1031038601194000407203074000e60b01110f1030400b41603003401000841030005124a002c001140a982003001640200c20071900003180d44200b001d403607583c100540b00541507038010001046090256080034213013a40360307000455629035071500da4003a030f000714184815080e0f8003c4086840c6074407500b00c202160ba80b1000780081850844003015155940d500d4400708200010040459450b403000107800d9600641d01c42c2e54001d9502048a260300b00380170f1145546110002400b80341068180705058901800c05048912140ea0800004141c459000c6416000e6000b000301010018080d9800910380c58507111000c0c10400321140444040300d494207101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 886157329 1250 886156079 886156081
    0x8070e06032814071a072604030f0b0f071806030203060604051306031e0c0e0406090b09010f0605040204060f08190c020c090106080108031207140c0a1109 68
    0xd5900000c0341100303120b0000825a040d0072a18034061008540360002d01030f00e00345650314040b01d8001803528111072810103468020f9107915100f401d03610038207801800e804080c6190154500c61135110111415800040615207562580c1c1c54805454405d001d0b80d40f0101e03182000100b0b820b403104e080e8000c8c4c1a20f0021080040302d562800c1a41060281804056010000039210348407501114040c0200401d01c4801c1c000c4c10340042c0280a481c0804c51b1280c00e840c0100d81454114249011196800341032004868280314025002580007442a00c1c02a01d03000240042049084001d01440380000045028031b1603800030360549183da80030381d010300e104000030402290300c24070b0722101040c180f8010a0382d888003003421009802802c0e4203034016260806015440d600090300384440c1c0380940b0085400c2ea0b80710000d5a40e242c0912607108a034004000e070441c1110440c64a41c0c0c4000701e07091000100304024654a01c03a0080d803583e1481c0da1205098030103000300c0c642203507122001201c02e2425 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 886158579 1250 886157329 886157341
    0x1091a011220040b03153c1801060206010608371a0909030a09150c0506010609090f05060303040b0901110328030b060a122408070e 58
    0x1541400d0340c000020303690b50b084182c1281d01c2254030404040803046242d51900d444001c010b20b030750720a482060058002022802c20b5007428940d4101d8110074564501040c0d088150b800303020759441c40d0790310640800d01300209243e40c0308511883c07240441c41043c9201e40c103110000c0e1504006822401c1031141c46000c1040315400881d000740c2481c19840c1900b0b0383c180d5100780c0f2600c400034041c5281d000f42024134040264840d10101030310300c0802c88003a185da0f01d60318841d81c3c41e481085c0e07140c0006000580244440d18891144810028442c646081080420b0700d83c1410584280c01c07410005044440810600c1c80174027848c0180200e0750310400c00c9041075000690f50780300c0e0317110b40c003c04800071070010a0307a070261030340c3e1101048450030b5079511600784c1c0210100ba01020811a4020111044010590300c04d20480412400140481d403900041c858181c0b80542d5400c5030346140e07500c81c58006540c00c5d6080704803103243d07a144070704801141481449410701381980c0141012103015010042 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 886159829 1250 886158579 886158587
    0x80d110a0201030b03030d240915060e0d060509030301090f0e0a021c060204080a060c020d0c020d0204090203100c09120804051207051e0103140601120f0605120601091a01 75
    0x2000d030307509080000c0c4504000c1c01007410360046014902010b40782012044d030040403101c1c0d1007401c000f007412290996840d40150011603000c1141d504400400b20390a0107910f014554102044500034020440c209172544ca9405843c02160100d501e40c20200040114010368054003440c001d00ea403040c8801c84441320b902e80e49044008011703100d01a156203190058100321980c0203e03076000182596619101c100e41641c4560110b0102d940a1900c03c1607401d0501c0800c808071510056503071940d42031210340030850f01c500301d440c0603640305545113801d10050b907040144410307200d0508408a80c0451010700079182d6600f42e4840902c0719001c3c080b0b0340c005840b54040b06c055030000c0302c2c408000407100280e1460598190022a0403900343d00c0500341002020002d0000d900c0241c0e170034804405952440486107070107541060107e0308840c2c20101c11030894003c0a200e200341c2c02c2c00106039a407000011080c0c01110000000b60300100c005001c40c0307105014007044a5090b080003190303040ca101c0028 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 886161079 1250 886159829 886159843
    0x30c1d0a02090f0f041e0b09011d0a0c2c12010c0e0105070501060906030c0801051b03180a0c060e120f2a1801080c0d11131410080d11 59
    0x7413092166090490b078a942c1c5500c049802d03441041070180c00110342d0340742d80c000c0910410103480b4800040002503201441513486104181240590180c0c1e11200c1c0e101c00900003a04895017444400d10303c101454034242c00d2440c0002410441c10210142034082c0080308044034402c0903540d0420340c0700b0030010f0b049401181170400c00e00c0e009584805030308000b8010f04464000000e59030414100109000c1801084805d45854400810107a01e038845410000a21902c5800b2042c9060001412081502850f8854603900b0421f4a080c08046e03a100d45c03421456421240110f280761013411058100041005000f5820600400b1085018840295030310202aa1880c445003a090703204c2901c25400c0c41d40780340c420042c010311003586e031210021551500c24000d510b00d51007030000d038120360b25122841010158101072170059001c2c05009011000500904a101890303c4144a240c100229034515206054903141400c03014140301c026818481f03076652400030450000381200e10820049640 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 886162329 1250 886161079 886161109
    0xb061e0603061c0503070c051302070f12211a03070f0e0402030715080708130f0215391501090207032d03050c0f030c0c0304030c1d0a0209 61
    0xc4107107a41c00c00e004503106520f8007001402800082a110700300301c003044100c0150751045a80c0c10501200c086440128085c201000d400d08400b40e45881c04500040c16040005005140c9420410300c0103070000d50706800803800680803a500c0214a031003000e01080e140643d08124040c000761450000800401400c0740a450046440500030908550301040039000034551049035000c44c2001950140185100321408030108100d24002000080500814900d107a8003080d201d4190000341c082c0103c2840310038000314440010058a004100040f1034444070141c00d01c4103034244c455120071158414520441c03030032147e00c01c0c2441500d0884240e00c050568800703000068842c10070b0304040700c981445646c04e1382d050740d881d02110300005400c00d0518040352285c0b01407015441d00c0c0b5864400d0311640c048c0700140f40c424004182e183c0f01d9840200142506000dc4a00f010f40726207a17803041d54151751141c200b411488200003400c0343c0c506140c40d4000c555481c00c40c1840c60b8032021416a100c0c0c0005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 886163579 1250 886162329 886162339
    0x3060603090f0703060510050406030210080c0c07080c04110a050d0c020304030609080318061608060a0506030903031801110d0504020a0b0d0606120b01051905070f0b061e060306 78
    0xc1c09600108050110050301c00c0c110394407150340381850f500900c410341b507401a90950200100325810300c2c0c02600103da60241c102640c2c0046072408131010080604200f0319040100070080c90200e0130030441010b00224406004640041001c1004640c0c04818403120480700f0300400d42c1c00d9811200380d503140030003100046600400031070b040342035110b80d81000b0803041c0b500c240c034000d200ca0600914400e81c40f0f404c103965420a02d6100654800d01260f9045002588040c40b1001e2445880d0309500800702801d240c40c06a02c500004106404c103e41000159002204006040003221181c0300c030002d049008116600c0f10f004800f40c203200f00b02c0c49610003500d44001c0307002c40d101c698858000340041e1080c29100c48460359240d002d000a0701c036010010b8012194074808501d144102180100141c45c1d55107410314020016a10011b002071070402d0103414840c48000c168400d2010b840d403072080c203940015242110400c91401d07000d01d4500758103040d01030ba40c8455100c0c1d004403508044100c0e1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 886164829 1250 886163579 886163581
    0x20f0c010c020d21030c0e12100e0c040204030303023001060c1506080d090e010e360a0b0702060f01061107210b1e060105160b1e10030803060603 64
    0x800301c1c40c0b01c0e00032030000c1e4003000340c00c4c1d0900f44030350591016009605030341d117000304550030404002c0084000c03000d00900d0740200b46102804d558580c0445040a0828141c6081c111218002004ca0f0043c1d441030b0082a00041c1604a0408c812448010100b04a0018910b0080c2c144508401c007014000c000c00e10640c95410024402c0c00d500c0c910541040d440e091020540b11050651189200003000020a000400210b242020240010305954845142034829550f00028414445a0b0311000445141e102d16400802118580181800c0d1208000703000030b0403645080414540010141b40171174020f2805d105000000c2c0290a04694880c40c2110745000048500ca0074121950302c10170841041c02d24515503045040301480086004185200490b074a03d10a2041d41c141e01007a130b8010511072000500d00e45c001d4001e0300200d211800a5000300401d45d490184012007a0b03403c20710840c02c0b4003840f130280c034103020082e84035083c0382c02c00d0400ca18654032a0b06901000d82018801c040200c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 886166079 1250 886164829 886164833
    0x304080607031112040f0302070b090105030c0901090305030403240207080304021905181b2506060308072105180913020910080d02011b030203130c08010c020f0c010c020d 75
    0x5040d2a000031a005032800c20341086c3ca40b902100b50030003000c40144c010200000790380401c040a642500006071943c510319964200e100c4a07590114107401d042c4110020084089881040984055803142c841781e10988070041c6e43e42ca6212181550b503138000d0040011100007400401a00d4100e036040e9483c1007891201c88030100c1d00c00f040d40207560020910119401e000c8010000e503030041c24824800c8201c1480340b56007501501c51a02038192036000c17103200b03092000b8601c603003211960245070001450384d100c0d900e000c210750040e18159843c107400c9e14007568001c5401c0c242d89101006041c82460800205004081c41c1071600c034252240c022070707001400740c030b01c41110541c10301e41c014002c620f00d20307050717000750b006550703c3c002c0102c1031081d000a00342040c01403050131000c00b540d030381180800c14101c038218041c0d07000030405c0c0702108841d00070310002202890094080c00f540300c000718246070011002840c00d60384110310b503a103502524102084c0c0e6045030040ca0205d80556450084480038 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 886167329 1250 886166079 886166111
    0x10903060519050702100e0f0c0105030702030c0703030c1217060411071401051006080903040b0904180503270603130f0803090a0b090a03022802030f0618030408060703 74
    0x50308a031024509200810413125030200f0038040f8075484000c00c200d00d00e00b4000e00c0d40d840c51150310300303280303a400481030a95642c014009954040c4042c0b0441e0714012130040c131300d400c04009034002c5010429504e1807104100c08109040407607046441c000c0504200720310b0203405181c0162030f182c040e1f03a95441c142c0c0000f000e60b08a131203494206401205081690071014002e02003220400d54445a0b444089132087c460003415004a1400005500b020b0420b0484001c0c1d600905605030300c2551748052035580c41c3e20a0f0a0407140f40144059038544aa44548103080c601c602640681044030310582d0100350368141c1566005070840d0200702881c4054602200240d560010240035150044100160907100040c06083c1c9440742005158940f03415010715554203042a004001d60421004d040c40400c5400703040f00b8040074144045c200303005a401007404c240c900031005030540c05c804200521040d0b5107e00700080c03402d0304000c500d803d03d1f1103043c907242d010203404d403010940c40703514030b00b00c2002e8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 886168579 1250 886167329 886167361
    0x7170f0601031511130305060603031204151413031d01140c01020405130b0411190309020609120f0c0d1a060d15021c06060917032b0b0405060109030605 67
    0x4c070403e034aa40e00c039444840504814248411102ea1081c80001600c1e81804000d98425000003507918580340c68644d2151980449020304850b10313036076407400004584030800028003801c1c118545c0400b400c040c7c180100302c00b14003000070500303918985424100d80d03886410f0002844807070700c08640f01c1d61205551070183c0319903030125500c461051348440000185500213003240004030340c00c00c201e144c212035002c0c89029172000709414081c0d0780e0260028502941055501d107100a215518055200340000c8e40044501910b00c04c9602034107010103170820400502d05962000c66003805250036568481c11307044500f402142101020070003103201a11944058043c00f43d1101e80036910140441c1004000d41240080b0358a0300c1604400021704541c80c800d42054030650750724500c1050902c0700c00e00b021030380041c00780401e2108010514a951201401c9041010800045051035200381846000d80303016071512840f0703138600400d1000c903a1300021582c0403240d000038082859a5070101c02085a51 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 886169829 1250 886168579 886168601
    0xb0f0904110409180201300507091a19050a09031e02012712020f040501240302040b03060d02060702280e0f01060c020310090507170f06010315 63
    0x810154030151440c11400074006840d42d0b0f030301c2080030100c41c02072581102018180a404208a01d00b00d000b54008081c41c20044601c002d401c90032154541241d204450007111001c0c00584490808c1c84155980304c7c41060540e034621032141082d590f0b005042c150a003c0d80d0f040188900003a0015402c0c2c000c0390203000940d0002c40f0001c000030308140d0142c1200801104900285c00c0c40e10a105003a402c240010b25401c07602c0104d40000d050521003042061000720983c5d110310000d01e1404a07503214040c4501821032818201e0f401d200600c42500e1581c903110341d040c01c1c0340c014407091141811407815668031200c21100c01c081ca079124000700e80c15118001001c0e4000411000303040e00d510103101c0110100e0288200000d00030783c0c4094004840780c00361245483c40b54403000400010f44120340034400d56000405039000c0c400010360410850360360100444039034100300b2080007442c0307440c44d0705c0d5410745014015200205038030072201e0f00c0d5101400004c25010340c500404841d058140d1215015003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 886171079 1250 886169829 886169831
    0x9171b040b03150903070b24040b03030904091412180f121005011518030f0c0f060e031506030a170c100501080106090204030b131a0a0e060603010c02070b0f0904 71
    0x2c1001300c451a12640010070070380f0070041e00e1020034070b0403070014502000c81611600304038411044008105c041d003000900c1030303410b01c030a00c00e01c41540d8543c4112240588240d10010f1808005140f96041c26800105000e140c101444058201c18505941880c581411100201012200300c00641d00c0c4050a00200b0544600b00006030340503901c1d0700950603036448034440c0d1506200d41402300e58002c1c008910b25540c40300301c14200005880a200010014410030715000002d03103c041403006d03d03000d54050800141c04103503070040c0b41001c1c800c83d141c11004c500202c90b503182000c04241d655880701001400071318029003c206000048058078004000001612040800d8668103000b400f02030040d001c15500e420300000700410035100301c03422298810345a0416030b662815086504400301c00940318004503680c84d1050390112a110341c030400d5407510004680e501c21f200c1625000c070050a4500a0b8500501c3c00d02c5150001020011036600b541455a1600b1212010307440c0d00411000d2a005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 886172329 1250 886171079 886171081
    0x4021c0f150b010306050a0f06030203180a0302071404050c0403020f03101d0606040c0e10030b060d230f1b07140c130606090302130e0d09171b040b0315 67
    0x20740c2503080b018a20500b60303030500c44181c8a804210105070103101d03048005540342d104001c07582c001c0c0c01a613030181c81030240b90420100a0021801c20301c51160450060b08118024450302e640407a20310f5001e20162400c100394903000b0754001c810f00c29070101a01c10321100c1c0a4101a82d406c210401e00304031094003d0000501e03240005c490305078810903003402030080c000003c80078149480365261403c41a6140c030744180000c024000554000340f01c43d03040541b90801c1ca2141d440d26030003000090064417000421404803020000203031001c02c89400c100000c1c1c414031480258110406401005980041154100c0e4050381c030f00350b11489034002c1c000340030401c900711003040c0030030850507944080d01d440c0307589060303290030000303d8003a4001e41d004120005003d1000d82451b04141040c075401600c00103041c03400121280c50300e00300c80004000141a52018441c0c202800008608410500b00070078000c6501450f4400001c00700c29024010782c1c0e1803c0d46200d40d0340421000c3d50582801d0810421 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 886173579 1250 886172329 886172363
    0x73006030809030705120615060d020403030e1f0e151605060108010e0a03021902010c051b0109140d02131509020703020601050d11040f0605060a03060f0e04021c0f 72
    0xa180c0051071024480c0c080c40304d0024a500348100c10001121240000e01050340c0c800d0146020186500d1195800200c14442036400954a10007000650700a489009043e5a640c08011f0a02a00d1895601d0382851203401200d45810141505140d041200c1448800c5240005115039004ea402040c40e00380042001034140100851558140c80c80d140c0244400c072a15050203030b4407004013030000c0040c0d000400e01c80034030901005400d0701610514041d000c113190381d01c0e850310b441c04c40034401000341f04800c4034491560f0002201001040b03130f0007405003071550903400520039218208001c1e02a00542e075440ca02c00001d036001a00d9064002d12810034a901c40200030001c0d0842c10044001d0700c2184000b040341d15206400c0e540c410380c84203240c0c1c009003040041c4000707000901c0038101c0c0e007038840402140c9a40da4001400c00d2442c241c0d000540d8500d8880c405a54190302e91110003d250400140800340c1c032031a225004014401c8a00b401207445450300c1c043c42c4031412006840c9181d65204054 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 886174829 1250 886173579 886173593
    0x7181a12150a061d040219050705150f1608010803161703070504030308010f030804090b031e0f061609031e02060a080f060103050105031c09050904140f0607300603 72
    0xc0707061300541d0020300340e142441800202c0c4102001322043d03240d0680c107581044c2c840c1f002000c505114505456043c9040080790482e408140c0e0b8111001c0e651800304000751407199015211110549440c0c201940f420100c0da40303c1c4106078982c00000c0303003520403074240009080040c00c10b085000e0030a03901c1c5000306008046400c42d0000f240003800c00c400000c0c085072042c0d2031000340da800c401264070301440c02176588010031901151035054000d007228a4280741c0c001e1540e403920002e04001d001d0b0034110742c0440c0d0400c0703c01011429100141c11a88519070b6110101009072940004521501107100c20071a4940103241002988441d00140c0d0408007a440100f007801841c88048011980d101c180040d001e460090042c1c3d5059840481002586044a000c02c1034641c414100680100d88801c0031442030042140e040d1200d8008004005500b941000451036040a03035024001134100032030024880b10954512020494892582048140c800e44d903da1002e1030b6054200329041c0da0b45442a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 886176079 1250 886174829 886174847
    0x1a1905030f0106050a0509062107060e030f150402060712020c040609180b0a09020405010902030906010e0108100c09080105041401180b01090c140307181a12150a06 72
    0x380a80101d0101c0d250700074050041c102960f10080101840c203003080280f1a03107903001003034154480000d10308003d40c1200700c2d5901d4403035000d11018150180c140900a081d00d10030642c0503000e42e00c007950340c0b01c11920104900c08102904481c1d5113550301c45000042d428060080c000d09420a04086001c3d06500050368840d42c070400e40701400940e40e80c05526003102c00311801510b00464903406540080c02c2c25000c10741c40103000000091032500e81e004602222000d803c4020103d0b400401d2003040082001410b0051900c0007041034558140607074140c0303d4818841582d900d5490311802000b81c0e001d01c003004060001c884c0204614509420416801303160403104000c00d5103004058040b002c8481e014500c1550065603070200d991a02039000c000b4030682c1c400c6d2040008013a0190340c2901c1d141c0c025406414181e40781d006420720310101340100c03500d81d03002c01075100b031170300c0c65129405400c403d9640143c41d00c180141d003585c909196010504d5402d03041ca501400326140800c0a41d0014416 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 886177329 1250 886176079 886176089
    0xc04060b0735041e0608041e020411040b070b090106051503061f05091002161208130609030512031e1e010b070308011403031b150a050a0c03051006031a19 68
    0x40d19001765100d100b51988442518040c189600382280700b900f13820560002007005201400008000f001d4030303082603198226030080c1404020005c0d08405200c445512079402c04039401c001c00400d446c020010b80d00641c6000e000b46406404400601c9941d0b8140c8115081c0740120050250302100c1d0780b0040c043c3e0701948070148201072510000840e5440007a10034071120081c507240c40c04a090042400140d440c14000303e4000000300808000c60319480e01440082607184c8810015905614103542044401161415608014000c002c0701700d041c9680641984a4007002c0c0b08141c07600c001c580c010918031140d01c040490341c00000240c0c41c800c14010040c0c2d50207555805000d90f2210341e42200b00b442d1031071081d81039006000315210400b14145029503603c08404071040c0c0054a10201507040013120410f4050790b03142b0402801c04914022050000410f10f8100f03c10719080e4209034092000340a19010965203a241c0040741d41c8181081f842854001d00c0300b16503a04175064540c10064030300030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 886178579 1250 886177329 886177379
    0x180f020a030b2701050d05120a02071a120103060207020613080303240d02010302030c042705072102210a0603021903030c080d0b060c0c04060b073504 66
    0xe42415258003003143c040c0e0341002d18040b485640f80404219109680706030a449034056860b01500001a50005000f06a465005000324925152603015a0151241820040c6100b0030000c44004582d045583c15a5446a00144c030b412050005c1071142c060300c02d008000b840030100105099800202451081881000040c42c14180303100c407041003407881d5181c0e904030813946426001076001c0e401542e44655000d040034180703551600456141c2840141100c541c0544c000c2d48800d028550040c581e1024540c14120682400b042502d081104035800d62100103a01003410028040008912075108102c800460041d0800c03041071001003190384412440307140030004080513141503441c24801c4903056180c07102e00c4581d54440003074a60052641e8540d56075221b004403115515100034040341c01d00c2c00000c1210890303407814401100d26a400199030184180460300000b090240810160544103002c88102103002d0300d0802920307150740c508111024089000f1a03400034414001e8003449003100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 886179829 1250 886178579 886178599
    0x313140409030c0f03051908011a03091b0103150303031d010e0d1214090f011d120d020403080f12010b0f09090618010b0405150c07180f020a030b 64
    0x20030002160111000240424410599000828000c05106204501908115290120100c0007a090034691010039000c251040014032800c098480e40b10404420385442500c0c600708424001e0340c800c0445c1007103c203549020ac0c440c115034822f4100c03c018401211000c2c2c500d5031640703800b4019010344526031418418004045100040c1406403030980c4840c0702c068070ba40200880304903018940401e1460f00c040d151a403000e41d0702c0d160807003184652560b801816800c819194450300f50f0703580e034151030f1500d0390002d202d41065401085003002d001020312405d07510f034600c01c06500a40104d5001800380f00c404690200211688801820b203100300d51000c1c2c3c0280c0c1c03643e5004815014003020040501024407000f505801c0110401c1e81040d401403001c11700c41c0504c06180d40f0341800f40c010301009040800c0400c00c034102002116410b00c81101e034a0700345a503c108003030382c13001e5a00c5484c003030000070303024150140301540c00114040e0301074805556a00041d80c1c00b801901904c45401e001d00d0302070b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 886181079 1250 886179829 886179869
    0x31813020403020634150c080c1c06051c02030d0c0804051c0f03090f0b0f0307080c0f1602010801060309110108150603040f03090609080d200313 64
    0x403080341e05503039000705100d0504072142c0c0b054000fa20407200d4410b01e20150b104410317a1559a00240c102d1074803034004800404090080314082c1c4000c2241d034018001103509000d14185d0002c150f034031030a8010000390048002d140e0f6100644016801590041d215100070210040a05c0310701c2d50031070003030f0101e031000703170241104a440544549000d000c51206104c2030000e4985800800302010400e4020b0322181da1030b440784042021410401c5020400c040400c20080b41c0d000b11640040c0002e4811a0070310341c007031a01c101584402403d5108200e410000210480282025201003020354a280e40d00d07510308080c0204420503402003a07020401060001030158424050201d21580c0b1810f80049162004015580304002824031a00e0014406164126855003c00b03540320707500948800c80541010308000d00000da00d074100301e007007041d83c100030300a030100040c07405000c0d07041d8581198410310042038449000d844d43c0080c0070a01000522503038402840a4a0080d1130115020260003040c903 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 886182329 1250 886181079 886181081
    0x10080c160507080f1615050d0f0e010614010804060504020301090510020706050a05090a060b010e12010203040618020a0618050a060512011418100b0316020d09030b0411040e031813 79
    0x2d0240c203075664402030014440803002140340341c0030b070640e410003230b0500b0380c0043c0840a4a000c81410f5602d5503480844185004003400780d20300812502c9a040c40403080180000d00c1c0f41d500800103421541c865012034210f490941c000102e054019040c0e400352103203610360002940c13100d5820b9500506200201d800c20b4410b200315802105000c0c0100461429070b561400039004031204107050202e00040e200a90710b03800414100d25036000001652807600307281080c00c5440081c4402505142410f01c2001070703c4144102040d00c06a0070000d014010600b0392b010a04d004d50400c40d0480ca9040c400180c1c0c0d6040000b61421814489001042d680c070344841907040b44c20003503040d034401034015143d26850440500366070094014814850107d450305030f01450760303000703860940d00740064411450505030305100f600b00d140068030b88465140d14644601c6102080038202406070b25407980250856a0b8a42c441c5a004481d03801752038070f4454005a00d520b0260340d180e00c0f405101b00c601a403441c1401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 886183579 1250 886182329 886182343
    0x90f04151a1908030a11070b0f04031b030f0f14060c04090b010201150312081815070c0c0e06030706030203160f020a0618030e0f10080c160507080f 65
    0x103401c0030010003060354020000358006220300c40514079022030010a20750014001030000d0a0640c6a43d14040156003409180c8800d6038408400d01000303020000c00388424808440131650411003090410ba81d43c140901c40c03040380d40c0000c190504c03100e445020824014040c040743d03030140c188a2652003035281000d03200c41013182c0d000c1074511700304001d01054006070712070015803006100000e020f82a4800144522045400c20341e030414008620b482000c3d0300414480d40207121060511002c1c41011816640b422030710000e604c034509840000d100e00e0f11894600380301310380140b01e229034143e840074922500003003955018005d01442c100812500c1c082e000b180d000d26104106194400007910302190b1518810010030114001c0e81071a0000c264540550126100b05801006050000e49401740900b5110042c0a000c0d46860900710f04075074440400c000318180034100f14405a0b11400504264810f88001c0c4614004042d949402d110000507440240c507288012500c45d0b0800004aa50b00c0c45 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 886184829 1250 886183579 886183601
    0x120109020f060a0c1407151d060d0216060e011113150c0b07080601090510020a06090615030c081e0d12090602040605090a090c05090d020a0302090f0415 67
    0x14481204045400c040c4003d01d10b50095142400b0281e10544e40c2d03d45086803c079003500341da4003c00c0140400d02c4c0010074100c0c6503143e4101303001c0f103a00381310540c0c0c8080300444400d8811600820944410004c3e9011208420320902103100c00c44110715000c002400341c500c00b42410740c070b0800079000315400c002c100c59540b0366100302050340514003050780d00900d000608003010000b04108080000b003c0310305441c014102038850011a16010000404e0403286034012489903041c0c401d43e80855070007141004078a60001c1022038040b10f0b07400c06c400070b400480120000c043e01890700006000043d0442c0c4240d6200d04107450040c10300750034200c0118468a1441095000203000001c0e0f41c0c0102c01c05590341e080d11102042c10845074079000c0480c2c05c10303406240442d00000e07003039803685411200c00001d0403110004100d08410044002c201c0d0281c0710055005030003140c2c0a030103560761908a44020350b4003c3c4104103510341000d46507449201500c2c129090301002d04070098180035409910b03001c2e5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 886186079 1250 886184829 886184839
    0xa14070339020904260304050f031309020a020f100606030f0203010e01052115040b070f12021b0a0501141005030a0624030b060a0603140a0b03070906060e12010902 72
    0x72903030350200003d048010708112140032181e01c0400d10b152090700c81d80f0507040d045503015201c0c582420f129060080207041190303240c10411011420480050700001904c0700c150f4010b0326880174110a91921901041405031407140020320b1801c1e0045070001c034150b842d0b613642400b0a0106070070040aa000a01540d00c41011000c018071540c2481c503105801c81d404003910034600d045a00703507a4140b10350f6104294001d040c0c0402c000c14008a00b0303290f80c0100d09860b0131060074a44000003044403800201c503544c0c40c4d80005440460301c070301e00a038180e540c20800546000300164540a4024001c000c00755030907141c10310004201414818611040300c401502502600e040c6a0781d03140180301c3e00307083c9010b1455080c5004400850b95002002031841404600d40717900b0960100404003a1a910003020103080000800030603500c044203581040484d500480c4001c2210700080c01c0c004150040310300180b40460008005600a480c81f502080c16600300000400d140b82c0c207420b980340600040c0d002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 886187329 1250 886186079 886186187
    0x504050d0e061209070317090d020f0a031a01080601120b0f060d120201060501110c0a0e0901060b0a021c050c19061104030b06090603010c02070306020a140703 70
    0x11a004901002000d030000b031032645442c0b0650314900c1c1010003500c04200d160300403c0144100820307507050250b44221108094100386e41500040c1070000a100028014248542d40f42041c0c0c0f11041c01e0f2000d9a0301c500d40c213000004c003261b0060442003d11684c2d086200b00c0000141b1800310340040440c0700c0c1c01c000303c113074940c0c1d0724200350f4240314001e040c460300241e030b6098040100c0c00e4103d00d400014259400801c403a0f1802d8001000070900b603040d054290030441902c1d100b5a51050a00d01b10f5100600d40c0321a81e0b12201214010900c03584204007a81d0000340c045080ca50204204250325a40ba0b1220000c07040500122403900131400c9280c0070360710081e100440c1c81c0c03901c090030148078801c62010a840d499941c0c1c40c2072682207a8002c1303452454001c02c0c0300461600140203503200c4004d40080210081c1518020760315219403002821a07035000864020303441c03040c00740c03a01ca034004030340856584040d864010445149900880c0000c03200f02c4c4404004240342c02c1c240c2030300801c80201c8100b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 886188579 1250 886187329 886187353
    0x90b0a0513030c090e0606122e050708041a0c04061b080f090111030705030901080a1413060f0b0f1309231006060f050c250f09050405 59
    0x2080d8080c1c00025014450003070000700081d034000501d4060403020350081020400819140c2c03a009000d010ba6114080040307041c00c0e84000003591008808194000d99141c03481205005c900322222100c0304803a50a240c2001038994000c1c0f2680e016a1140e08a494040c000c074045513032031038059030000d2a1002c01c100800416102c1e042e40030a02100001803112200d69544009655014100c0c1c2d00094001240325456581c00c480c0d07807402c030a80ca00c0036600d481700070b43c0c0741a16031140a42c0e540c1030004040101d80480c101768410010b81241d000c07020200e0624132042d241140024100f10f80e01c9090000541c24911036010704006900c0240a420340054140c003080b09181385a40711103c02c1d6668845100402c2c2c0880c0c40c03c01210591300b52045142c1084092400c00c1c00f020350083d041400c184040007110b50100c0c86444189081c9040c540f02c1041c1c0e0281801d000e08010298051000d02c014041ca4001103481c00c003c84607540d07401040700d0b5031800341c5016130300100d401600c207030845040000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 886189829 1250 886188579 886188587
    0xd0f1b0203030d0f06060e06040503030d110f030702010b09071b1101030f05010b03010815010f030b0604020c030c0c120d09090213050a0602010f050f010e150a0b0c0616090b0a 77
    0x20091004042d28107040001c581c80084664904400d00340380d88484c410410103800981d0360790b5000060341c1080c903140c00c10020950700c0c414501d0342802c0e90750702c1e20300c072405000e40f0044d030b100740c1c2840c10320070350703e05010381c00034086c0802d80445446901c07510041680c0c98020685001810107081c50300e60340b48004d40f10720100c0041404428103154485580e112220b02510a15019110804405884e5410034000c0e030318021810b001450301400110043c01071003403000c0300701c0440380d0000032034186945010100340680200f0381600e00500c0042840c450101d17000c01c107400c1c1e0320b4007074034030200600c1480c2c2055500c07203585030a40041069a5002c0c003d841540d0000c201e509011021000d015039954041020020720781e100d180140d540305508550140c00c1e00500390082c0010640702129410030b403401a07035400150100c0408181d1110148103504c0d502c800320001c0100c0d804c860784400b40703100110f4450a0843e0340001c2822502c40d0441e525001e84869802c0d124100c0496041c40d4440301e09507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 886191079 1250 886189829 886189877
    0x309020f041d1e060705030f1b0909040501050601030b1c060e01060e0c0408071509090b18070c05060c1810020109020303211024030920030d0f 63
    0xc2e00b28990550010020008101904a0f01c0551482ca01d0a0a05078526410594050301007010404100184600e60b0011600c1c260001164400e49590001307100807007800780b150609494022025900700000d008066125510a000c02c0e2414001400580c042001c00e03000c1d82c1d46030312007070145084200800c402d54015061048224000075000303844c0c0c0d80741019400100c0707405146860000b814803081c1c0c014010f10001b010148070b0003001d16980040a003040c19140520001c20741c0d074400281d0156203c0380012080c03003602902d40d00390f04121000030201e4044400030344040c451000414220080341040390350903c03201c011212084400010813004400c4030bd44202150349030321031800581c0c0d0600050040d0341c0120301c8000010303a00030043e024900000e1200358200443c1c031003004031620184181d01c13900714445c805100d01090520a80003810990800fa01c440c0544145041d01078400303181c1050305004030112203507003640803000c95800c1c8000c400c580018002c80ba452203c011000448 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 886192329 1250 886191079 886191101
    0xa060e1309120c02270714040f0b03131a06011b021302070812070309020906040c020c1005042402150420010306170109140a170d02070510060501030b010309020f04 72
    0x340180c0842da8170740303495400305820501441442c02e1015045d0000f1031403404c01803142c049401c1c10714281f8800c000c0d0040e803098030050040000080c000203146818001c4155001c90101c1c07120f1403117205500c1c4081c00300c84090108000418030800b0015010106d40072030b60080c1145000d000c4007001340c002e500f24200413641548140803a80d00b411160302440e100e034480e5600001c118810b80100028500043d0041c0e014900e0705444081c813550205255445c030700c05482a50940c0080541160284919800f4142002c6c011581000c640181400001284969030072660455800910110301c0c01041d40c0c0240607241c1c12100c40e500080304c3c601140c80f801705040001c0c0840d40c49404c050404c1000540480595540102100300503c2403a00c24840c0f901030014089003600d81c1d1200d840c800300320014021958045420161611107070100c6000d103074800c003a00c0240104840000c06022a4024107022a00744100106030794400c0c852110841d4004002c5502881d400c0140402019003000e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 886193579 1250 886192329 886192339
    0xc0302330c0c090906060a05060306010c02041104050d080415020316171309050906012c04051c02160801150b180619080c030403022503020a060e1309120c02 69
    0x5210351941c1c0d101d02c01032081900134060146446d01d8030410001501035007001d485800309105014041e40c0c0708030000c4200354180c8000805240006c801603d0307000d1540119031002c1c0c101d011104000b204c80141044501610942400414680050341c8a00818400d4055124001c0d41440400c800e24076500001b6503400e0f40c10324003880304024071000125030708001e401c142c56006000114000308000790040140445220f411501c1c0602911042000c0b00251119a204030200b424840184260710400842c607050404003400402c1c060744030409010f0155518461080001e180b80040c0205c0d0b0794264030740c040c4252075050915012154004505141010b1411840300015458160007000e49800c410198840c1240841c0014040e600c000d10307045814a0030703c10702c0006600010002250548046800d60700c1c86151341080c0d001049503c041e40c0811254030010320990803a035a0700e034440b401c0d61621804007200f607040c13007070b241e080b0b2009102c4d1a0320780100050510861161078440d1000340 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 886194829 1250 886193579 886193593
    0xc100e1b100903120309020117010612150e0f10090e06040213140c090a050a0308070f02060706020a03020414120a060b040f1109240f180d0c0302330c 66
    0x1a213000440c40d908000000c83e590b00d01150a40da040602700304c0c081032046041050f0360500800500c941303442d4102c00301c0d0b1510b074021b9a620301c02000014010b4858040141001d1900d0305141c1362002042e119204507001600c404a03c40d161402703030f05424071320100104040d4550f6420300c0303421801c2400c1a009260354040c6c05540e03c5000620f6402a000700f05d513140c071504913a0801002254031362295100f8291841e04000103240c05003902d404c103401c03260402182d0f4060007c03460700e201e19070b8005d0940e44000740125055415502820546030703100e1001c0591140007061004d41d94155520440c594414052100040c500d0340060411220240c800b0840401c52902c50080d20010340d61000d1448002c20301103640d00f0400401014801d1084180e422071500d041501d50a20400c1c03008004101d001818851061010140c404a104080d001d21040841c50602c4000b1400c1400100c0c0b1520100405040c265001d01c81032900e1800810400c405208038805900700d5031111149020034002c1c11 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 886196079 1250 886194829 886194833
    0xa03030f050a0e030d0804050f1b1c080a0804060b150726040603020c0c0301061d04020a030c0e04050724030509191202010c0c080306240c100e1b100903 67
    0x3c000c0f4205c00000351070344401800d251a0441c148400143c2c5211191f0040c003644c0d0019492169004101e24141e4880c910030103903042144001d2401000030304480b00c005440d40026900840b0b10344224000d0004014001c1c0d01c0c001c01c80c01c007000421044450301d041c4510703004281814412224140030051028241a61880d0384507903800030340c0300702d0201341e0208049103400301c1071013002c0d00c03400210300801500c1d082070035010740c100604482020760180356000404640702d9000c44c4000c5c42e0000c1b030200c0140c2ea1a0b5019001020440e4100d03603d002c1c5100006d1140c0d148075000190b00b02d0403d100c20b1031428407504400400d001031500e072a510401554518410042e00850005800340121015400d0f1906002c0d003900d100c1f10403d420440144280741c041408442030704c7e0000c0084400c60540c0340000340700d031440e0710003c0c3c50312080e0000058a030b2128900181c00b440d51404408280203000740c01d44882d032607011a1200c42d103446018404103419207003c04400c000b1040900f0254000e85c1c0703070307 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 886197329 1250 886196079 886196083
    0x10303110c2b140102131401090b0c03040b070c080f0d0e06180904030e01080906060a06120b0406081b060304170702031c09050a270b060702030109080d0b0a03030f050a0e03 76
    0x44500315210703135400140b41e86d0f4404c40303014600c06882040f203214492680000001d120380c1c81c61041e2480c110b0301165005507801c05008035002004001102a1591002d0a003503554001500c00c012540c8030f0004142134041d80490101d50011040e140d80201c11409803e20000e03522505010b03114070802d03100074010b03a84150344103004034043c2d07451904201203000007400500d809400c6880c1c40e400303e020030005a07590003882c4284d038003505d0400045405541c80f10054100c00c54090b42c4942040c201103564000018034201032840c06800d1075202c2900f10502041d41300c191006480100c450713100800c00460340d4010b054181c806001c488a5401e010a21110400782c0a14000020b0748448100b080340303416400800a030160484004986110905000403000400c1c0003d006030788525070001241d03260002d40e01899000780003070207920081c2c40c2810565203d009010707500e03031074a101e6204030b052061222041d83d17031603161003c0d60f051070310042c1c9a41d00994445405c0007201414101d40d0340742 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 886198579 1250 886197329 886197353
    0x60302090f062704020f010c0f03121b120c0c020d0b0702010605040203060d061d0304032a06020a080906070c090e010e03090d0f060f14010303110c2b 66
    0x30700c58000007a0600004000c10091001c280c907038030758143e24088a0800f12000b0503900154100c80d8003864800308001a1340c0400d0f210030107080e0f000f0000d1514103040e0061548518150180c00070010703140031100d40b80344007012408280000e0102d20b001d88080d1002d0744500b11030300407400d203006280425030019800751070050003240d820500806112200e0b8090048038040e00c801c45056082d4074019010031000c0440210207000c154880c00d003210350788002c481e0320007558081d00c02c1d65510358407421300c400803000f11800c101c08001e0a8200e05802d10140080a0980f005071703014044e05101d45c5c84995290700f041006541c414001c00415000403500020301004018100c804500d1030285a11a42154000c64288045410400140c00150303107140b402201594000d003508134160090034080010403030b031000f03802014585011000180e000d03002032812284260384031846002d00218054540a071041c051717811282543c0d81c0681c1c44501528882d8460034024010380344030f20b540725a41683c071 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 886199829 1250 886198579 886198591
    0x7080d06050a08030421080304110a05090a0c080603030c150903040b0a12150807090216080307081f060e0904020616060609060b030c09060c030c0105013f0809030106030209 76
    0x40001400c200006c44128080e6200038482c1c40c48110001c80c1c1c851081c039120090005140803034100d4609049d548004010010700000f91129143d49010a58807004040c0303060a0b802082d210070004245190002c01c6a003140e2141c0050605980300a5000940790130113803500b50786010900c0041000025840640207107885a61202070520010035010200d6003070000a402d11030101c0c006018100b40080c1017421229030344001646d80d035000001110399031985d031005280c03640000c02c0c00403e66004208034062144034004818004541540d42e41e80c09043c03007034802041400c0700e03819940c079000940a52003070024040701d15029001c808030036001c00380c0c601250040c2c3d95640070700025440e441820041c185910761280f8605105e01c1c0c050050060840c0b05101c1d000018405805880c00c0c01a146107008400081c0314550f110070f10500c0180d4001c1610f51000c100c00301c01081070703400b0f0845110b00c0c0350b5000140c68001e02d40c4c4504407540d0004503080d4041d03484100020050300e40740441c501c107070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 886201079 1250 886199829 886199833
    0x90203160c050a080d090b01050d0c210606080120120a09030903050f0616030e03030105090a0e070603020a080a0203070e01080a021c020d1109030601170a0f05030702012307080d06050a08 82
    0x1142610301f1120100381a0001401109881d445c0b2002410207240c6206540c60741200f80b5032408015440b8082e5044a007000300700c82d0520600042c0043c0540180070303549041204d850400c40245513150035401030311480414070350000c000c00d1716002d03207603c082c0400d0702034a00050090340300c2d25100d20702400d894141040b0f0744410108a030200d07841828241d00f0300a40341c140000000321411a40e1f0740010700406226481d00001f141d540082680b0000c9040c030080c0c140d807490ba98914014000f5040f00b45190089085200041d41e000a070307208980c854034007612407803c00c00140004441020006010844441d800c211241da04010340d100d25403041c2550b900503a030307482ca51a054050740c4410b0040820300509100705045a50003050aa0560300514204102d10030100681482d004600b000908083c009024a6091203004001011828000c4c1c8441c140c0c0300c0c10000580c0c01400f4651186580082406180b0005a0b1030000b041c030ec140300340001c20250b80701c0c000500f03421426800a141c503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 886202329 1250 886201079 886201091
    0x7031d060f070e01021b0307170d02060a02031b030711030310140d052a0d0f1b03030807031a120a030f030c020c010c020414100807090203160c050a080d 67
    0x1000c441c4040e41e5211001d841d00001e030500c45400070f55107607810a02075220034001e41100a03140c404120308002498030500c010800600c4070002600c400400c040e0000501900000510400950007100c1c0142c81044042e098540c841b0b00791045500054800b60421901040b40a010901000518040c01101d0090001c003454071035028811030580010a00544d031502202c00816000706030034035034819114115601c40f541030b42c5d8052190200740d0546c0d100d0b0312a1044028498004118a0342520034420444110308907c0703d105003000d00d20000740041c5400740002c4806209800054410920090114500040748000b400c0c90003c0004048a0b0703208944000c02d05900100502c805030140c21f0410112900c150001d40340e0a00c1e1207200d040c044000c1044085440350360200e0440b500707190581c1d4003401d1001c0400000c40081c41001d1581c842e046020421003983d2003282c0c00b40154580c084000d684140c07095800c4044800c0586803405050b00300000303c1d036200c00808114850103800111 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 886203579 1250 886202329 886202341
    0xc0801060504150317040308070c050406080f0d14090301090609030201181713031a04030f020c03031c02211006030b030d0c060b030d260c1207031d06 66
    0x8455065009502c500e0915464400500e100445002681d03000303840c1c0d499080449100300c80e54405d550004100c40c20006c5c40c0000c2c802222205400d4a00448060181c241c3e50245907688081005903005550405284601110300440c02e0380d02d41d0010a020070300300940c80e00040d0031907001c0c04040c4e41c20740e299420300e070825a080c8100400024005840d54080b00f40e42c0b00c0100041212141c0c03024511f00190700001c2d8141140250004d56021281b203008030082017603072445034402d44086002c120847c0b143c4051500102e000741c24054007070021828100b0301e080c00c1d140e899412400400d065802c102c20810016290b0055034070183c6842e0700082410700e100b0382c41d400e412660004c002c1600e070403031021f01d994000c00d01e10007070546494075001c0d07403e00c0c0c00e10380018940761000329418402c1503036241056811255000d0014481d108500e58202000c00c3c1d5180d408003298490300d03402c400c00c40351881c0011800200d802c19080e180001d80200780d0941e1405613000803004080680c81b203010003074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 886204829 1250 886203579 886203581
    0x3191e0512060402040b0d0507051902010c02060714120c04031704031104060e1611061e0a0e031b03040317030115020714010302070615090606020d020c030a0204090317040c0801 78
    0x240102d02902c0031460a4078040e0561045c3c042c02c0c503c0e026203034a83c004121441c0c4a00d0035240c003c3c2007230312f41c00900076001e20302a0007011580030b00c20150044400103a00035000312083c0e0081904681c00d180b0700305240300c4a411a540041003003600e00400e2202101040f0b1780703418500b001700e15440c401d94441c00c6040c60182000b464044038451410844140503010440d01000e800240340c8901c0d181800b09400152600707000c2da031460600340300342d00400418200c581c0c0d400c0030300301c10464038040300e840d5520814260760300a41d1001c4164410070500804001e506050f880b21010350702900d052503165907a59002c2c5c905088848405100032005101c890340b00420804c04034840d0005125613482c2c8440646401c926120b000c0c10302d580031a514086c04201e400100352044042c840090726502c40406074010003590090341c006100341149840344a0000403541d60140004000300fa804045d9800c00c0003800c1c101e04200c040019600610841020088103640100d1060004461190030104d003d8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 886206079 1250 886204829 886204831
    0x180a12051f09151d0d03022203171e0309060601090e060a0311061204150e060403021507050c0f0708010e1218010c0812070305100803191e0512 63
    0x10301024508090003002880d202060343c801c034109003001c924001c10403145081560fa03201c101e8603a01418000b180c86991580c010110780d0120b80b07540c3c2c51030001c4440d46402d4101c134040286403c205240311075000b10100c000c1d000545d210a5003031901030403000d44100c1ca400540701800c2562014003070210359a08045400090303d40300006212901d04000010801d0141c1d11002e0505200704d07a1000c05030316010304554003502c00070b20b0104a8186450600c00102e940c5141c000d01600d00001152200c4011825600540d05a8000c010604511310700c40c040d1007010703040c1c1051000400002800480900c0fa54440703041c03a078041c160f658a018a81403c0d500d004218140c0e0350440d64581174602004030503203c01c25100d40e00340244581c1d0100683d9140400c0030041c10618020441148801010002034420203007035805004076116020148441c04440c058070055400500100c0d2508841e500526088812807401900a281420000e0011089215144001000000d00b0103002e1421030b945 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 886207329 1250 886206079 886206133
    0x6061f0f090306022d04031a04321525020309030d17090604031707021e0607030e1906020702060c070b190302120402060c01060e0a0e190c0312050d020f040503060604050c180a1205 79
    0xd4984cbd8a0070301c070000c01817035180c8103410008580c007000b032004601c20002d480c4030b80f0b00a007c40300700d174012a03006000042d01039645480340c3c20340303000518801c17400303d8458013403689034032192441c0d41e00c40c2c158a0f9911f401010141103128040d070b410244105d400c03828078080032440140c000d9041000c0c00406461301c040174603080b940800082c1d82d0850b880250114041e80040005860762154070009034103100b070080190701c2e413160340000b00f1300104803030052120030b419420490f400d4685210070380aa015075107600d20780002200c0010050b042c81002000f11501c00c0000107492621504480602d6800380c800b0300b44a903803000c481882001c1001107a0201d054104000c0e60718010782c1e00d01c0c00420880c000180f44c241203a07040302c0c40c3c43c003543c00c1e54100400d0305019501c516a2854480180c0c00c0b03031140921038450302000c21024209807003a00d0045200d0a001031511600411004030600348034903540c1c000300b03020700002e0080c3c1c94041a00c0007a2003807020b000a240300400000f400f03248400d81c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 886208579 1250 886207329 886207363
    0xe0a0804060e04090308270f030415030606080a0506030102091201051503060606030a20070f0b0f1905070c0503160506061f0f090306022d04031a0432 66
    0x104d8010075007007800107a1010f034900000c50b49040000829040c45540c5400c00c002e44a0b0030b00c61810031034040090003d8440032000b404c0d540f40001000c8043e0790702440f079200443c03a00b8011403440c3d03001da009550b000001400161803d00184041800d01703464600040040c3d40d5203052000c5908440841d40586608400600240c00d1050000300781e8800900b041c2c0841c0d943d1b40b001c03070340806112000101d03854802000c64075104079090111a20304000310440b480c51003600042d0142451110b0035004030402d1901c070301c1c0c1c4000d441c00c1000a000c007901310014010000007103400030707a0800081c400c0b00c5502101d101c032452a8038240d07103000c5000e02410b04c5582d1100461002c194015080d0400d1026490003800c401c0c6003c00566501200f03410207042c460000520901400100b00c609003081803452006134100c00c0841c02501a020301c0c04000c01140c0c41401800d9014003600c541d641081c080c40111842c5540544c092140901c5d000004210b641c007012186009031040c00026040c4c801c40403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 886209829 1250 886208579 886208591
    0x3130b040b060120031204050a0c0314010609182303131505030727050d050307050d030e03040b0f0906121005101e09030209180601081c0f030e0a0804060e04 69
    0x10704c04e0722030140b41060008840b5940009080c0300c410450980850f400c02046190503480f0300b40f20601d81100c006003400b541c24510300007800394062007a246030103006070001c09094040c3d40c0702c161000c0030a05c1078883d450055030058a2503001e1004000e959101d000300c1c5055403810340b007040c40130f40100802c000d2120602c00c002109801024403182060880c0d0191041c1000d900301607003550709600441e400012410b1000d080120010003090418064000c80c0d4225030f84003012801c0d128040804013036904140020019100c901010380745d082c08003a40746040145841c0810400d4200c0440440004a00000d1080803130304502e01c100039001c10b5821840e00e01400c10068448400302e0100900540c007019488103403072148031041d014580c01014036080d8206110318161032001c101d902c0c00e0074004c44000050255002072442041d40010310300f040843c41040c400c6d10300c506450760f01d13800c4c1520388460301c4254109105030080b1502c45d000981d00c483c1001c00c014400201c801d0054001e0749024 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 886211079 1250 886209829 886209887
    0x1a03030c071e0f09020a031401060f030c0201020c2e1401170c030a0804050307290a0c0f030c030f0c0b0402121e060105010f0f1403130b040b0601 64
    0x7103081c100352010300b024000802d00410001d80d20005543c001c010401e01d0507404128881c0c0d9800401804075a03603818440180d5a1000d00c1202d0828031070740002c550303010707400b07038160780207400408004800d07000060620050240503410460095025100449407083d25600e40140130b103a00307110b0100403401c02c42c1c0e00c2080e40d500c0440e90306003c1c0b0b4030384104035081c40c0a2500c0801011084140150540301034000600c1c3c04038854200d401024803a0044006c0401c440c643c1d500340e011a0b0300845003c0044028006660030721384d000700441710801c440c1080030030200f415031a1045503607119507240c140400641c1002000819481410703001c201d100c3c800200412902810075400507011141900c0c21558010014a000e522004d0104110708500592119000c041001812180f0a8941c0c2d200702c074a040007101c00410b4041140c000c140400504c01d4004032060180d54016011040f170350341061591110445a00c088504551060300c1c40200901540d229207841e03a5808a8070848030061008 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 886212329 1250 886211079 886211083
    0x60405160609080d1b020d0b0f090c01020a06240602060a0f290102101a0a09050f04031407140115080304060219060204050d3f05090a0b0d1a03030c 65
    0x1300c10140304100200c0c0c51105041d501c441c00d06912640200541d00140283c80c0544440508513000d0709554903550001d05903400105249401c01c805901a012100e46a9105001000341610019450307600985003007801c081c041c00003000c0c000c07035000cd0005152030047da2040d5200d0800895025080000d500809120803848007040e2204c10400d032021151900104d00d480609150a044242007011110381d249120701080801007042d11a541040e449090a60030394005450704144d11034190002000301740b0030005003464880c0c6200c85403501c0e10f0340d03c404001c400d84980c845040d135500d803040b8070ba442400c1d4100300102084000b85051601e00140031b03464032102024820b1202d0b175001203030108038407075048401030301c0e00820100e0101d041d81407038442e49810840f0043d241120080e120300c00b44c45403000c8a603140c01c480d030410036003e461500320342e60740140d4100c0d9040b00d800c80011a8104003070f00035001a07440440c2c00245000c2480c0350728580c55415a07418041d40003001007403524480 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 886213579 1250 886212329 886212343
    0x15052707030803190f0203010f060809010507170a0b031b18010503060106050d060807090203060a06110304050d03030f0e21180613080f060711160501140c06040516060908 75
    0x303096030000d500400000d03070341c064007171340c0c58032100a0720000010400f0600c00148a0603503c0036a80d111540e51420001800c952055030080c0108214102405280c0170700303410741d40d0140000302c0118555100c0c801103841d203061002c0ba442228910030842110f0709021030009131300b0609414809103545400c02203501c401060255200300080080c1001d0140150341202c4014201d80048407800ca5541e8040c00094005903204e0381305001d580c00000344544507104401082d41400099450107141908000c0c402c0180c034001c0341419141da0106e03441c400a4031072411510028006000741a2901c80096120041501d2140481b4000d0085204004032900d006426070425a00035a03100541000a01e103c1030660181400c0c3c450042403130102400803a44501401e050b4540505414410203d6611440984050044084501c0040003650300c00d05400c0251540c9044580c0f0b0441c2c980340a500706071048034240c03815440702032044c4a21006c0c00300900141481c0c548032000c02d081140c078075107c0007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 886214829 1250 886213579 886213591
    0x1b0c02010509010e0307030b041b0b0a05130b03040b0411100207050f15030408041e03020f0d03030209130506130e07030308070207090507110d0206070c080715052707030803 76
    0x8080303010b866907401144812040b000040c1142c0d50aa580d24180ca00208204c81c12604803000a044c500803100040340301c01940c50000c2c40c1814810040800c94260300240b44211349540114000a46101d8140065001d01d00424501c03902d49050f061511040000304102c034019041e200c0d41c0c0d0090707580440d00c003003502c03000c0750050b06040c24100016000319550b10182e00042e0004180000c012014000f4011a005c40b82c5541c50321086580c1300d40700d90458031001e90040340380d107403860f194034000c82e203600013a1017424010b0615050b200441c8000722407070304200c00541d81d07038280b094600d401146200c034a414071070309005d02d5a542c8a02c0e5103030000740c400101400010808980054003d00c40013010b4640d42c1c000b0000380c540024003d0117240f20704034582107805038540b1500c451303101080e002d1061210b610380711000b190540d00c21032145d0004009840d51640c158403034410350058026240242c4c4c0010700c4140d42e030740c510442d002210601403083c0c0b4a50000c1d078200000f407090400d4950140d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 886216079 1250 886214829 886214837
    0xa0e0108060f0913171206060405060708030a0f0f09110406050d080703021f1d0d050306010e030102040e0a140a061a16021020060f04110a080d030f1b0c0201 69
    0x24891a400d000158440030b0000d00c00d103085e050840145807200f010701074001103058500e0300342d1501404e002480c480c40c003030310f90880002c1004c031000c9080c030720040d50446544100003495018200720541103603024012044d50940f10003000c400d0142094a03410f050604607020002d140c030788000501c1c441e204410080c405000410003034240750080c0500c0c007084401814000648100010315401032908603002c9015020114102686620000305450448403940710189180c85100041d1244288902c1441c2e25640810010030604868003040740110284500131444a00717400309801081d8000704040321891074020108030b211403482048180000e17040069503518100d42c1d184042d50904000603400000901c048156940c1c014850b4203070208081641d074400102c0380301e07681c41c5c000039100351440c40701410115000c40c2a91441c1211280c0007000d004205079120151030a1500c102080c0740400d0360784400c00803070541c80c0506028400d0b02c805171000740745a90300c060021000d10501074104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 886217329 1250 886216079 886216081
    0xf1f0e031305190e0103080a030609090c0504181401061401110601060806040e0d020604060c031503080a110f06060307210b100b040b131703030a1e0e030a0e0108060f09 74
    0x955401e08004080c101d03003a003140c41c4c0d43c1c40341041091503101d81c0308100001c0ca00030b0001030481c9540301d06095982c1c4040e410b5400d5107003c04000280c001092802c1c402d046031070746400040d01d4000304000f541440e40021440360b2a100303003100c240e29502087d5042c024040442050110301050395419105e0605090100f40c03070360310210f0010000380c0c91000300c0e44259403160000540000d0360511483c802c040601c118840d4090480694501080c07a40002404640a100164244001c1c0124109602e098091103541900b010714200301c03440d24200c1500848280552401d00b44103100240a4018095541030341420900003109441c80002e003102400d100070070298200848030400400c01c0d144100c1d110394035032050071210f60120700d0780030741081d8071400041d0890a0068190130274003924055401c42e55280040d002030407000102200701407034005039a543c1000c92040441e958070000c001c5031101c001b100c0240c10220120030340382c1405914000c01c60650740700c401c1c2d002100710640d1620b0075 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 886218579 1250 886217329 886217359
    0x6030c0301092c0c040f022d0c01151403010908090f0f03010c02101a01081303030e120306042412020f0414041b030809010c03020f1f0e031305 63
    0x1001d100c0070030807a001081e50361080c0104000245131050f9001103400f0807201043c0740c4400c00700e20800000d10100410100001c80c90600c0101c070000004c0c0401950b40b400360100e603030341d003110207802603900500703403560062124284506000070b01107010390003040903042039100c02d081806030001c0640f141d501c40c2c000c096030351510290000c1c0e200018000f03101c032080000c0041c1d1079030a1100c05078107040c074000c6e490100050fa840d40140c202c0040c0c440042a0322004000d04142c00050802d805142d03ca4841c0c00400da81003043c204c0034201c0c03010300c40d02c0b41001420401a45c243c44400200700181c4100d2056440980380c00c902141c55581229815401c107101046451140c20a01544079181043c2d40c0d41c04a100c0b00c0700c9104505c191080641060703c500d803030743c181e07405000c00b0308403c10500002d00e60b540288604010103000c0d00444070f04d00c1d101e0202500d41038443c030300b007000c2d0001e001d01c644c8003d409004184445501401460504560300d00e42d06081c22548241d41c801c2c0e04480401c03107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 886219829 1250 886218579 886218611
    0x120313020d1a1617130c0e04080904050a02180105030603011d1605060705030706180206190f020a080706050711030c0a0c0506030c270616060b06030c030109 69
    0x211860b840740c04600041180b900807401c1640458001c0c00e06010415001442032040b00003811141c3d0007005012580c039100000c0ca42c090340d4540844d032015641d280070400c50b0000f40c03c14810740c03291640c03654070740c1800c0600c01940c00c050003210000c0c0c01408001c4a003100d91400b240c504500703182003501c0395205c04c0000d0240941c60041280705031140d4404884280100b82c00912800c0f1420b02c07122195134006001c0d440c418840054025001408010700213040c42d0040044401070320300d221444c00031a00042c155030b1204c40b8101c5119211040b045026402c001103540d0347c840d80c005070110310126198020548a81c0c500105160380d120300240d6050b0050601c851500382440440c0e0301d40c03424000341035803400e00d0441680c0340d00c25081c0c001464038042c1c046a110f140302c0041c0e82e06000030f803202c80d000000308107003400d004111041c120302e450b222a40a05a400d003c2e2810b0300c0074140700e003825411101c80b02106801a0410401c200d580740040f011070b811645103140c0019102c07403905a0b98 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 886221079 1250 886219829 886219849
    0xe041211031b010504110111060a0e1c020607030b10090302011116080d080f060d060f0b100e04060b250f0f0602031801060302030c0111010b0a03061d12031302 70
    0x158140880c80d1a60702c602c0550150380b04a1161800c0240ca0a500740103540c1c007401c4404900650740304000007980c0300195004080059010011250341070000c44003828091140350006006911540c1000342156050003081e200000585d81c0c0c501ca00c1c400315000b00031032028000641449441c2109503a0712908100404100c0c141c03800f2000c240d5101d0229603103c4886a03400e01c0000d0750000401c4c010740254101e0b80c0548401489078280c19850b580701e401600c22070745c00043d510754401c0b20b04225222103145094020407640d8000c111488041004100c0740282c10108201c4403e200c440b07009000c0b0f60108515000c4500b138840c1c0b00281d85402c0300d51884041d030082c40c680124011108011464000c0c50140b00000705500d190420300b1485c5d400c890b11480080d6255000501501e03140d405108180c805410820001c04c89a00171400718045100326802140c40d0b5a4403002207080d6607450011020118014020345071484010034201c02d540030140c000a11410030184c072004540c1e84056503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 886222329 1250 886221079 886221097
    0x209011e090302030d08010509040f06020705070e0a1802031207080c0102040603050402010f081605030c041a0d0b06041a18040c020f061614090d0503040308040504060e04121103 78
    0x1030115010100006241680500c0304900030311031107401d2400d0074040c842c41816200082c2010b00075544984808070f0702c04510b4010b0714030310ba0802c000404107070140100070207041c010204228178108960301204484002c80c4421480c41c05280000c01650040707a0307000c0498641c4041922503030b01b424052510701c21a22150301543c4000b800140ba51740580042c0d219074000d0b01c0f041706034402104107807102e140c2250300e40302000580900c0814075006002860700446039a401a00307044d125451401061403000448560203004682d0840d40d004c0c1e406004440c40381a9212420300d480c0084032a84005402400c00c816840031134100d406004808400c841000000c0041c406d24146800180d1294144a074007034090040c0c00c0005c12001d081c100714500ca0f00c050340d40e0310200c0d0442020015a0300100441d550144c441a20b10703000c29820409480038500070020143e40c0c40c030344400c0204590242e03029040d4454003c08000c04030b440c40105901074902d9081c1a0044040320302c105081d40b08a0305d01c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 886223579 1250 886222329 886222367
    0x1602010b0a030609060b0a061e051303030804060f0608210706020304030e0405060a05032805060115091a0d0c0903020619030609050c0a0c0c1a0d1d10020901 69
    0x10020078031189070044803519004203800c00840421b5414800b004503540120008540c1c071030001c41820210f2002c188030a001440c0030360400101513083c4548526a40c400d038000344040c000d0000788040d40c0b00f0710810b00120002004035900d0000301c01d4649074003c85413071613810815042e440c141d0f0404c00302c95445070b1140d070841d501c4c98038ac50003810301001d03209080d00940ca0000000c5450500d2400c00c030958a00400909800400c4103e002c601000c4205200101e0080303a5694000b510410141c1d002c0c001c46003030032840700c07108000104055460362008144101130107098489004120495030780b805c0c030900c040740b18424000300340d48880f2503520003504031500040381c03e0f02d20590400c3c468540724070b87d801d0000030764034217808095600a40314881030305c404000e503c5155004907000c2408510a090140f40e6503a101800e00c51141c1d100102d1015000c006524000c140e401e10551280480385031440e040034004035490b81c2e82d4202e05120b5910180e0019400303000da070041e40310071720750401c3c001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 886224829 1250 886223579 886223599
    0x80408070c090203160903080d0209030c0d050a0203100908031902090909100c090f0e13050114010f120b011e0506070602210f0403030f0e01050a05060a0609030b1602010b 75
    0x25100b0b000794421030350104182604182da4050520507071490080780d03005540c1c00d08000c40070403ca002903204803156507051003000d5901c602d541340e0b042c805180038000c80280101c0c00050041c0760400500c9605d11403040e00d04081c54000942c0882525002840b00207045820010911860000e01c21901015485040c0380c082003545100018802d0218020035014090140c0030710081e25003800c1406a40b0f501054090b0910840c80486901c991001040b02c1955203034910342c480c0c50071100f00300d00401d010144e880051051070081102e400091422003001c418a1916448018940206000d4002d6214003607045841c00030303852810324060b0000030061a034440103840c00c1002507110404181c15a21210819003600041e15413a600c5820501c00b040c450f82c2e11641d0840051006084907121103980b01c030b42c0c0815031002d10070f4500c1240c800e18001a2402c24400b040f542c2060ba501c504200110400e00b0700001782c6101015422824580d0441c146081c264400c0c0c1c05030031444211908101010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 886226079 1250 886224829 886224839
    0xc072126010f0602030909240d0c050411031608040203070f08010f0f09050304030303200d0506090f070c0b1e0c030f100609050d02120f0c03060606040312080408070c 73
    0x460540c12140c1501042d4003043d51400d090b030b2240602c5d81c203141d0000460002a009490400380140100c200d4500541c004140740d0000307504100a0740c0941d4000c90300b44d014010345c10148194010001d011101504616201c0c01d07819500c5140b031742d90810059401e02280464404000ca40081c260100303640c083c2030b864804aa008000d2800006156401c2c02200c0381011018854400d4440e00917026501d070900303549040c0c01500da10317039001d03c40c1d400c4c440040c1c4440e1000000303040784010340e010100d0300d41010702c10083c40500103001e050080c00c10300f0070b1102094011000080869200b690741910f0358a442c4100411808541c45c2d05030800403004105841440300300452041084080c0c04c0b060303031901c080142e122080f0740a0300300400c40d001d109118518121000040840c4001d24035007400b5984160f040c00c00d41058010652036024200120a0f80740c04e102665100d841601c0745414540781da00c416228600c0c0700700e0314081c4070300c020124007402000c5003101c00c12508888864900d40c2d940b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 886227329 1250 886226079 886226147
    0xb0a23031005190f2c0c0d030c0506060108010501120b040603020301090f030914060d1d010903120f0203090607050a14070b0f010506071709061b06010603050c0721 72
    0xc1d410303401e0b42525112054000000301d204c0c103086080c2c05a41542d80d0040f8840700d0003c0850003141403206e2040c02c030321600c60b607160002451014440d945d100140050391a10f1403410b03001810790703818404c01000510040e43d012000d041e1030303500e800000c0780c0d4041240100d402041243c0002e5015400c0c00003201c148078440c44085912442650f07615a000d5652504006024148044a5100b81c04020b4243c060714590400b100b50380d05400540481c02181c880d00e400c40c4d04111044000c1401d4403040002c101680c411840c49401c0d0090940c50752500c5c50f005921100021300c5c890a100c400f040c100c1200e4801ca62034182c007561110882c3d6142d81509200060520494805400c0801d410000c141380c00c0000640d2885030b8000303030044500c08c0c180b4403205180c200a0440390008024014006a10341002540603512541005041c1a50400e003004080c0e41004060700140c0d00c08100413400a000003801e104c2128551040e001071040900301100c00c643d20240d00c52003040e004580e941a0444 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 886228579 1250 886227329 886227361
    0xd050304090212010806040b2a1615020a0c061a0913020f01050f120c091012050709050d030302090a0e010b1804050105030c010c0609170705010b0a23031005 69
    0x1e10715041c01c040c1c5e66150115502c241c1107130018482c0c1441004510b42d5013003200c10b11603c1c0c1418000c02011000c01c50460307c1e6030010840c002c05102060340c003005111025001c1510014940415440c20401c1701000e07182e0310354103e0041545948200000c58000001208075500130000c0901095041c2000302800000186501303910078550000c2e815141d60052046070f540c8410111210b0a0207030100c2e40314200d4500404403002c000c001c000801103903550444c103036070100c0329271200c0c1280b1442a0106045079401046141806694442800304d80c0c0c039803800c4018140d2601e8090f03500c86e4030342c0c045840361030260301500141040c04c0000c42d415105001411a0110b50b0b0394000c1341002590030002511804e11805070075030000500080c1c694030030041120b04500501001c18074000654407403101d180c995003204c0944101188110030801d081c001c03540c4d0b000040b0b50801405081141c03c4241e140b6040103c070001c076210b4554841c0d9207080c440300c002c85e02201000c100341e01d000f0b0946501d0b030030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 886229829 1250 886228579 886228597
    0xc080c0f030a1e0c0f0b071101020307090306050603070b04170c041d1b09010b0a0c080301090501150c081602030f010519150b090d0213091b14090a0b0d0503040902 72
    0x3e2000c01194140784a9001d1800c4030307030042c42c82c062500c2d0540342c50207010b401408031002c201c445001c04c0c3c030712102400114041c80702f542e1024401c0f441c60038083d04880010704010b12a4020010030005460038030141c1e001d07150a40c42413404a80c0c1c0c101c210745800100c04260303402504207a0920000a40142c0d070b140c642074002c0c1a50100f48440500e440c4400b2001d940c00d5020100c42e006010382030a0500ad040181e610741030481243c0c2d101d80b81c2c410182c000368891080107490710014044d00403014582d40d1004030742d0030220340c500b580341da0b181800d00030b0b50010109030300440200d605641d0104800e481000384038008104c0f0781082c00f1140700821410b982d00320354909100840c400c2e403624007038203001c5401006600d03041c42002c00c204148044415401c0e640301500110440661a06110700542144a851500e01c1c0000307440c4006456842c1d0b6009842d0b10341e4a43c0d0080103505c43d00300c030b01e41c0502120000a01c0c42d000300000b4050081a81002c0d010b440045808210f60110f6401840c40e02e03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 886231079 1250 886229829 886229867
    0x209031903094103070b0d02031008030a020d080411091f0f08060103080a0c15060602010f09020f011815080a0f02070320030913051906060c080c0f030a 67
    0x1c40694020402d501c4025510b428071001c6048080e600f4861001145007450080c10b9921182d0344005415658211818607142c6541c0007007070001c102c403140030310740040040c400030f1414034000c260003941b00c80c101802c0806000e042400a010001c952481c165890001001d440c1642844070040b07948600315a10500e2103600320001203404040007250100320f501290040419a0865840b45696041000c04d2014060000c125400042c0e8905e040c80c00c02c4440d1000188482c540400242515128084803907117914102c1480c01507201d03910b07107d842120070700b0800c0311201540b845050b04400f55001b0200203030320305e00312070607140d100d0b2810b07000e0524920184403c481d440c0c7c94804a1140a00080c00f0a20f00014200003840003581c03103030744c0b90000054a043c81d10400200d040c7d9248000021038080d5110100306190102460b24000c020f01d00c1400c1040d90b0600130042d00c8be100c20720000d0510780001c03031680407503901004500a8051a4030035640c44002021000e0092138032000c050481c030b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 886232329 1250 886231079 886231109
    0x1030e03031303110307211805060304060513080c1e0325030e0312030a050f01050105090f040207120e03061b09060c0a060504030908160b070204020903190309 70
    0x808000400e032405540382500c0c2d012841ea195030161001804421a10034602042c022500400c101610481182d00182c2e18401680340e07000c4020005070b00f80c0c9106200c8a1a07010070710203512850b040e00e03030255000c0000180da03200c0e004a124024004500103185400c00905000d5484c0c000c6605103400c1082c4a50004040790f2801d156107174001d03d03070090024000a00c0d00c0c6035552013640c0052070f584c06402c0481051510a0101c1e0400ca0940c0d02444140d03400420700c80107031303828414585d11504100200402e54141000205030b842103040c4c4074403e00c413000002c0b400740d42e203504a82c4d103640d0100c000d2162000c80d420242c0070104a0340624804e010385000614440c007606894104100c0000d0300350300d464200c00c2000102d8200c5a40a60144030f1140c41034005180d5200381400386001380c403800c6405c2c0c90030013010301c1d1446030a0790400201c07180d4800c00c149040700040d03c0301264111005a15483d160010910349130040c040303000902102d84954060603000070007031054448034100d080c05 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 886233579 1250 886232329 886232351
    0x150a02040513020c0606280806070e0303070f02012a0501050417040e07081b161506061b020f0306070c0515041110090b04031b050301052211040f02090103 68
    0x484c010301d5600507540c1c010000080091528252110318038000301d1031429022040c181d034541c0ca40d4183c11444880d0300007014085206d40000020074401012002103180000715a84c9a0340880c20100007414440310090005c21001142e90030001120352664032217540e450b1b401d0650203080f043e50150b45082c05a1004403002108100b03d0303043d01c80f001850074007925000070480b00340400030075040c02818100e0402523503113007503401000354110b04152064207070300a08205040401c200d07508945185403c00070001e043e00040d040046d001c892903100340300801d41c00411f0001c6441c1e0035141c1c0c5800f038841000030751600141303c82100c0d8040d00455401c2c55207002c120100d400d0644024101e502ca01d8081c0f01c061401451019044101c1e10b05800c0f44c681e5440703000d589800c1034000322118590a840c1a000300e00c9044090000d000c03c44c024041400d0444000300302c5440c82040d4108840340301080030900070324480742005100050020070802003540714010094000b0030950380003e090518280c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 886234829 1250 886233579 886233581
    0x16050d052a2a070e1302060d0e1507092612040e0f1512010f060b1b01111903020405031f0b01020705100302071a01030b0f0a05011a030405150a02040513 67
    0xa0a149484020303e00700d41089128885094000c0c4078020000c4030096080050f1942c0c8041c101c0074401c0040030510105100c18103042c403a000a00d40c4c04101c445040100709580300b89030b401140c412808100d0103240e411100c1c003c0e4640c880c400a024407441c044031001c0340c2c145c8020300c1100c4043d0400009510703002402036080000303a8540586c01c8044070108500d10b888c5050100042000f000064544072080d00f08091ba00da980c01881c00401c04100d004090510002e8480700e01310a80c001c110b60000003e80d41d80070b0041400c002d03102e4901d0455120180e009504980151400030126030040c011006003c031000144a004220b09050050b06059940001001303030130344500401034007441450f00400c400a40050b181a00d50b124440040164956002c100b1800703140202400d89407890050081c038682d0340090521070600d464040104510307800b00071f44414042044a0b220390720748542c2026440c08101811751042c0440307400600c003008800354010801c0b035038103a4046442c8000e03645400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 886236079 1250 886234829 886234897
    0x191b030203040b030c1603050a0e032103040227070e0405041109100b0d02070c050d050307290a0608060604060f170102070f050d030516050d052a 64
    0x80240e8400d00052000c08100341c06190300580c01001d81d8201003107080007800300c541241d02900450b800041c010390f5298440d000d040d10407400da0050060344074008110083c0d8061002c1100d40071404008501150390328800162030102c051081501181d03040c400b15564003003513403d2404214040781c865140d00b002c0c02514030454103c1c42c00a120040ea001f80312002e140200040c4d407403c41c11f100459110003c0d00544086241d50800685030b1180d032804210344542c1c1c0c0c11036031103403a021080c80c0005100008032000b644d40004140e050440c001071202e2965014846d803003140711103904002000c0120313030201e011242c8800817645a925000148002c81d409800303406c4800544050a21510382c00044440f40c0354405030006290012a85070080e0b01140350364200d9840d0044044519029458011a5044001070050200030305100e0340140480c0300743c8909840c0503440f03038001905455484103401981c0840480204400344002c2c40307110030307031040501d044440c050440c04480302e040d0034401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 886237329 1250 886236079 886236083
    0x180324070c05060f1906030c17120d020901022b020d0906050a030b131d0111161b0503060c04030b0a020412150204050613060e04052202030f03191b 65
    0xa044213031914040d040d0b1812000304032020302c4042810200611205200b80c070000c60040348014100f500f05100000305451209041344c01d0b91103000038041c00e4403100c0407031f41118140040140d4603040440142c0c100540c0492181d510600d5844440b40c85e4080c002c2d402030401660f09688052181200a86007802c0c0d9000d5400094130500180319a24042d03030224060107401808080156034200c03142c001c1c3c610301e2201214002d500900070030284000d0050f4800580487c180c2070501941403008111481c9200c00a080711683c01e05002403c0d281140c20409848090b084d603540345001c1d00e4203c03031070b4850300c811074055242d080010300d00d003250310944d01a280c13481840d0308007541030303102c04d410006410302c00c03020315070308210010721030766240e000301600e40503074003500c141c1c910704100501107050090b2464000c60400e010400d1491982001d040410444d440075601c1c02c3c041d001007440d01c0706a041008080c44000755401034240761520310103020080d030f91015a0528000c04d1030b40303408595000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 886238579 1250 886237329 886237333
    0x182406070308091c1e0c060c0c05071a070f15090809100905060301090905071e06120c140d0e03030f040203120742060306060902040b030a02180324070c05 68
    0x11040c00d00140c5ca580d00c641c4034180c64042c035a12200d8603540c040b10421034001f004146c8202c580700401809100c00f00003019810075904c603641120341103010b00d2080040c001e00302001200340e4010030001e03608841030f844006008206d011558a081c0c841c41d8002c42200384220407064407030300c0d071921501e40581990806041642107910341004040501134405c0300300c685000714080030400094030048d2071032103812505c4104581b440e00c080a4420034140714880700040c105403030b0209660304100e0b003480714101012680e0381c0320210f040d2803008220b00382071141c0c0c6000010074030010200c5000194000c60007102580d100d4a40c44507402130502c60800018491116041e0303088984503485085142080c007610005080c02501d000c0c940c0c102c4080780c3d104a0301d07950350000d02c11300580344107041c0034002d880c108615250a04a83c80c003036000080149d040d0340e400003980c040c9090000d0144141f1940034044070b42d507500c15441401c0001450403420307040b20301900010b80c80c80c46601106503060304140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 886239829 1250 886238579 886238597
    0x209030a020607060920211906060902040603060e07021c110a02060714070504200d0b120d17130209071e050a0e182406070308091c 58
    0x1080c002c1641141d0000e07505541d4610460010401d0a20201803800c81003849100d42134203242003200c120904c071140c1081c18141c54441c03250240000e410191042d2240e000d9800d50001d291103c00b074541500f000941c02c1c00440c00294050301030304202c050701c201000402d42c40d5079812040741c1e6402c0700d1400080e516618602e50400901400f46e00c4800c080d94010783e66020742c1130f000f19540340d00c40c290480d0085441400c042c00302106010400150800701c4042c81741c002c040200d08107416005500e0141d44070000741d050380783c0b030040d4444107103004080c2c0320401010350000607940380c3d40b130100340c00c0105e80c0c41000030403184807c0d0a181c0c03054035030700903410600c07030071317800f8001308038802000340b0140b020010006205891082c0103504c01080780e42c82a690700c110f500c0007800100e5008440b0b020300488800c007c4100d994a4895509c603503090390821001d082c110500100a03080c03504150403180001c1d24009056104001c07512030f90b034550454410300540c4040c03014503410050190006000e081e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 886241079 1250 886239829 886239833
    0xe07090b090c0705030c0303040b04060b12060c0f0d0f24050913020103140c13050111030a1821030e3a080c070608090609070b1b03030a09060509010209030a 69
    0x90301d0781c103000c4c00481c0e003070414402c89103181d0b901c11350b070a461084185040000300a1503009800190030b05540c404a140440085030740c0c2d810300540110185803012440d001c0360044842540d050700e8100000b44400a00000840014590070f2111030701c40414580c80a140b0740f403403c204040781c0000d08240b04c80e95070b56403602445402c030380040741015100c11803810344c1482c002c105402000550312030343d0380c0c0c401d401c0140a04207886d0300207414810303203101c0d000201c200803082c2c4c0c50602050810703103174074010064070f28001d00316608078818400705408904020581d520030600c08500c80c2d160802082c28040400950032180280002541c80140c1c8001020700314241c031078141c605d68054003418520607070f150b1711185c0044001a196a1024504005041d0304c0400b0a0708100c4950150030719041c42041c0644a042c0c9004800a140e80040e0034110ba00c00651265151401c03c1d007500d07260b0505200d10741c0988102001502c8040c00c1c480443c0314544107108135152550000d0007050744004035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 886242329 1250 886241079 886241101
    0x1b0311030c1e121f060309110925090f0e0103050c150904060e04050d141b0709060311010801080c2d03060c0a1d01142a010e07090b09 59
    0xb20111920000d2103a04400c0000841e4a8058a01411011090001444c801401e0203d41d0710460406042492090200d00c0d501070000761000c0030b03904103c9a40d20541000d807034452003003021808903049244e50321510f6100c0d042e4426614820600c03240242d82d0b03c41310307030748200070301010717246820001e0410694035144440c6008841c841740c007141052610800603003102c04a602030410050a00304010800101703020302401030b149810b100481c4208002d001041c0e00070341e0002205100c6c07145d250303180010100b20300d000512050205200b0070b41c0742d280c4aa00b41c00d201c80150301042046002144100c40441c507002000d44c082d0902c1d00d040c2e0404140e02c0d01d003400c650121017110160b074059510b0f4806102c2188030741c00183c6040c5c7d803804940402407500c800080d40490301c52a84030030b492140c0c0e1003403084110300c280480e00742c0c80704e06c0b07042e07001420f600403100150808424205410900d1042d0480c44249081c8415901d0281c1d031001e960043d105141c1001d40d0010300b9200107a0f0030011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 886243579 1250 886242329 886242367
    0x5071d0108061605030a2705010e030f121305241303020d03110c10051b04030b0105040209011e0207080c060315010c030c12020106050a0b0c0601030204020a0c0203011b0311030c 78
    0x1c02e40c0d01048045040d039119041080300c012440712011740307407d000c0502500f4050900b01665450003541303444070300c08e07040b0322500410301d10141c03548449000c104140048050103600381c1c2c00c542500d5054600d40704000628140d101414081254000010400441d0096403820300760190054030b02509055402c40c01403011040e02c24072100c1c00c1c04100c070b1005007040070542e0482034800004042c01c0030181c490020310b122401c400a86400c1000b40002514000c01604452084e40c0243e203c01c072280042c3c440508842d03168100780981006c1c0c0a03020343c0010041d0448409000b0349107205001010b0000b1032004813401070f58011000302c3e102095114050040406000f490141210100c60b030702c03100314003540209003005079103440040c8074a1620f201d1b110000c14100b80d0b80b900e4026404c061a8844005100c00303407050f94081124100c1600032050901c0b1507900a000304084444000914601ca802240345030000e45041680c8540340c01401c200c9000e170301414900d0b03007442680307103d60340b807400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 886244829 1250 886243579 886243591
    0xe040513140a060623010f050f03090604030e040e0a020f03030c1002040501120204180b010e04230708070915090b0a05030a0b03070f050103050a0905071d010806160503 74
    0x2100d455000d011441c00d40145408401d2a0040e21001c0600c3c100403064600b981c10105e040c64500b13111414150f11456654482c030b20a0800d0f4100c607504000c241c650340a04d5a10325146400001003241000b400300d25140b08901c20703215442c900903814240000c4a80900b181390300c550101c07607100054941a9074010000d040103080f0392406d12808182070400000841c03008102da00460f060000d0360f0403248040c03410200110850600e0b14041c0c1d480d8059005429a041c2603986050107490b0764400c0090500203030740500309004d8190480c0205291502ca0741942c2040210000410340162296160a016080d03e0f524200c0aa04058022141803099104a0300340401c2101c005800c0600002401101c0100e458031612450049401c2c001d58002d2903055120fa00300040178041c000d070188400c002d8840a1070009480c0c0c3e58600d07440000c001c840000391191048e20800214608010070340d0240589121030794039544da9404400755681001c0e51002d1002141040c550384543c130850103554004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 886246079 1250 886244829 886244851
    0x11a07020616080d0b0108070c0b0615040b04031704030506071b1209180504030801121103101e0c0c060b04140c09010f08060607020f0a081f0e0c010e0405 68
    0x42d803002d200d44820035812000c0319030a00100d0019078080d00c512803040f03600030a00b0700d000380f4580203030005c0540074141002403900018102241c0c8075280c0140d4005160800070081da5215140c90344071900b60032520089030181c410f440b0340400d031035400068801702c80d0300400802d40c64455110a41d03081c0d0140c80c030f1512012a149141c00400c100d1401c1c106c0c1319046440b17281c1039608060f8400740c491912080c8a500f982410148400607920518180c111158aa05c0c1e82103410340f480c204114019140c040d5030b16104606a0012008203640300f140010011000d030001001901c0b01e200c22756142115020120711200351100111710b1b182c000d14141e001c02000050400e54114580c1c0c0f00311415101100390350808030b014480e0b560825900d0081c400a0305000e00b00385080e20010b105441101c00c001e00980c6184020752443e104c406013000648180c90540700004c0340c0d08001c0c10203034500d640300000e0a007040303138022900b040440c00100340c0c038040e92955501c82014060002920018100030101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 886247329 1250 886246079 886246087
    0x90f1902060c21180301020a020a060b010908070f0e24060708071505090610120f0c1701020304170a020a0620070609051005130f151d070608011a070206 67
    0x200f1040601070002c1a00441c0d041d265650312007401c003455a0211010301aa104200c0200110380010311030110342e034000404188070b4001c00040b1020544c5034020401885044004070f0207082690703152050710300c00340000c440c2d44d0390b0350144e14003506000001c090019600140300b206d030510b20010030b034050043e02da8a01c1c042c10b03503851600595020310b00c1d40d081503072a0f043c06802c1e0740c144280342d00800c45840d60780400341000c8001d0f901d2580400001c1041c04851010780c00c1005c0400041c004050f203000321200441002482c9010351300c1114106ca0140b2281d0071550003103000001e4030710415880d0f000f040071200559680c4010a110316101c840c440c242d0080744c0707940a0440040c01140d202e410041092030031450000e2070564164104e400950411003000f080f03c18122074508142d41000b03042d598442d141c00e124400561009601074002d040101105070000c01401e0200741543d0303681150071403980e40d441100c807143c0a000d012803860080c04109a070117000b20241c16a9400148a81c0c0340c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 886248579 1250 886247329 886247353
    0x70c18060b041e6009050303030705030106030504051e03090f030106060e10111504022404060e041413050f1c0f021c08090f1902060c 59
    0x407580180e8032500b0030101d12001c03110a5805030318140c0080c2054000d056507115081c45041c008600040d45858941d2039650003159021844480304640d5a51048844020020841c1d04241a0078100a00100704802400035060a000048070310480103030341c0d25030441c1d003001000c4000d0070018009a5003413244440f000b0a10301d100c070880c0103048807003004640e108404000c2c8183c00840c4042248a0391503d90100400b54011100c0d45061340225100b0704240d02124080e03401c220840c1503080c0324032455404910b0b0310300403a50f0f18056402200c20a03110b6680a00300f4441c00a086020807501c10244410070140d4042c0d030807000003510090000c62003103039014503003000c0007044446212103040d20381400240602031000415044020000d40a550300074500401c0c207006107030510040012012440e0003036442400140740844060f12040ca0b103d28420000b041c252007928a02c81c03a0292030740310650701e100001c21000b10710080001941c80c501680030460203070880e090323002290281c10381443c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 886249829 1250 886248579 886248599
    0x90a0c050d0f061e080a0602070f141b03030c0c0f2202030103141606080a020403060c031509090209040210020c060c0a1506061b081605060912070c1806 67
    0x1d0800410b01001642e146003810001e03212440302166140e10550032028020780501140030066940c0146015988030304501e807540980c0076010015200d45481c291100c6840d20220f01700102800210141c80c0000440b01003507128880c0000301101944500c0d040c40441c00c00c01c1d00d00700005401401a03034100340c2035a60f41c1c801151072584070003841d800401842080300c9014042503040d5564002c10440044d4180d1034030405c007a0084c50244038400340050707012032090701214040c2d07a00001c04c1c0810718914030040c001c0c2c0b00252040380750000320700c008204030000303102d0b8484032a001483c41e0440d460303e0b000d004462411a54030b1003140038210011f02c3c84c0d200c10004280c0f40c203416004021864460400074488100c0484d4411a0307400d01e001080241d504c030418118900340100700401c101e5081c90f10300405c2c418888500b01114140d03028509000011035030902c1184003000741e50000d4101034000b41765116202c1c0007000f11050302002d028a600c1c4011071506031404041c0010f02640b91006a4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 886251079 1250 886249829 886249841
    0xf0102070b0906090106080714060d0903051206030d02030a0513050a060804060e010b01090510090e0c180901061710120b160822030e12010606020615090a0c050d 71
    0x2841c8180320409000708030b10100a40360b0b01c101098001c0122601b07050141d521030074075110300340d107200f00301d94400c1c850b6540b44112030708014841400c00c01c403aa00d241c00b801c01d4000d00c4400310b158616100040060030b022805c541900002d81c00703146000c0602c4810b90303040c0c01c51015010305001e02100401d1070741750020a040948040d0301c40025030302c2c20f0703e0918292807040030715031482e9040901101460b41c20510810503500f04807100380e0a102024002c448007490799002c1c0c6240d800c90800d000440c1c190100408402407c14075003846190341e0010301481d03034402e1040400240e0411140a085402c00400c11707004000119460b40155907282c00001109440c44141d55a521420a00c0091400705045119a040b02c0c107004060380740070320803d107075034401608140c51500030b5100d80040620904901815510061050805000301d00342c09001f80320034050107025204c0c0e140841c20418840c4690f40c2d407034400802ca5101e6541d006048005400c03803481201c00d010f014482e17400304998501544c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 886252329 1250 886251079 886251083
    0x14070f4109031b0d14010e15100b040e010e1e0103060b10080402030d030e01110408030a03050603060f0c0a09091406090c0c06041209080304120506070302030c18030f010207 76
    0x203140c03100304450800d8200030703248a0a10340120040c000a0458440540350000c1d1604601540811441051114003500c00c94580302d8981c050113009610310311204203603d004503c00c451003444561612a13030701092085000319104c0e230b000c2c070f00104240d0720108441d40c0d100128040ca100d201c0340780620010407140a8004649968407405a101ca42c206800450402d0010380381884480c20071b6001b190722fa10b01c07010100101511503044200040094000e131a107442d0540b031603a640c5540702d038030341d440e6000700480c000000d00300004100103150001d080c5004194510b0340038002d80b43c0340d145d5400755001d44240024003090150000e21440d80d48030300c104004131001940b28900c2e2000c1080841d0390010191a1411814048400b621720700240041d07119078080d12040324240301841c10343c3c00b0913140e400920240310000c0c0101c1c60642040440e0380882c410300c1156041d03203d44805605a01007240c2c58508050103100d1000d1401c04003005500c00100a42980d203014030303050744642641c0c40f074241 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 886253579 1250 886252329 886252457
    0x60301081510180c0207050307030305090406090e0613111806030609030412020d1106041502010f0902061c060e090a11040510050d050c09040614070f 66
    0x9010a001c0c00c04000039400780700504a105518240f2000d02e981003074588403039980070750340ca64a03030100d8020405100502001400c6a24440c0d491130014196440038142d01d0045040039000a980b00b00c0303014800310006c1150103003915646600b2111000101600140c0d007180e1202150f0b2010b803501c030341003007103440c809005008910f4441c060600e080e1000e08841101c0d4020001042150361661144480c242d0456a0b08004001403c0c4005000e000b00355150f80300600040004240030002840c5080811640080c40b4013021700031880112541044082e400c500c0030030079050030503541403041c40d1141480d01c0014803540c40b06460f451144085421781c0390741c0d02100c1c0c40c01c2401410030415010280c00c540910031483d02d02100304888001d4400d50b401789441d40c6c800d40821100703116281e901d6070049e00041c0c130b81c6041e0130464090400060500101c0f13000f0307070108001511a0344102012081519507111076a48007e0a0742006030413400d18a26500d2800d804114661140003a1454000400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 886254829 1250 886253579 886253593
    0x10f02100c0c1407030201020601120807020402120711070e0712200a0e270907080303090607170609160504030c1418130f030302160b04050c03071802030c0906030108 73
    0x1401d402d980c0740d44200440c3c207074061801000141e80c0011030505580444003d031400550602c3c11481d14003031914001d500900102c1d403a05c111020781d00d90740c0b00d641c103543c540c1c0206140310510390704c2e07046a02039980c0d620440e200160140e80170b0030081a41703000b80348001499036400c00100740c201a030050a1034590f00d000030a80da1880d40b010786040c00030000c649001d44076001070100c0343e01202128180072451040f81c0003981d80035003400544020b0480b502a2941c0f458083c2400b5180c4204a40c0c0c1d0b400326070001c0034034400707407004401342c0e00c62440503192102984a04201003842698043d00d00200300040102000060071080784000038a110501c0360f1081b80e00b4410441d81c40e5a1302005501d805c0104100544013920500c214a15078000c0207201c40c01186007004c50184c03203103000c0b030091081e00755191400c1020550302035110324042c405982ca00c1c91220304040e00c500c0503200d41c101d0110410418503000c0e02940c02540c010040c08455880e080340c070345c08200035030403da202d0310507a04404 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 886256079 1250 886254829 886254833
    0x10050c06101a180d0f0c03060e060c030609060f04110d020c011a010516060225060b091006080907050405010617060d02060d050a0e0105010f050f0f010905010f02100c0c 74
    0x42070101000c040c01503075040100b101030f0b5030703100340d090007920b4801c00403c642c0c00c05014000301030052881d045030340c00b840644c036030500c0400f41020010f403840a02c82e80f00003524106000055a0040d0f02c001d007030080030340b41d2404005000540c85104c80d0700503540e0907036082190410000b0070240304c545102503210b600d074039090340c00c50f0300a5900c070141100c030724000c114581c4e00c0422105000d46005504044580c0f50500790000e01070740201700d280340351a44080080c81c5514200d1449680b01e03540610584040400344080140c050b510468aa0344204062081a000d40348840e0300c507003164101d560541d59000042c003503030400c1e030020020a0740c04a014042603103441a00d03a01500685500c0038030304095001c00d14610403030803000c00c0c82c0e82d140045034034002c0703036003090841024a0000b03003e075503100c620600c5084003501c209403092010809858860030030070413061960313005031034074400d4629080043d035800006585620850186d040340740b284808900c600305240107581d9842402400324 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 886257329 1250 886256079 886256099
    0xf0f02040b0a080f060f16080a0b030706120f060e01050609030c06070602030103170f19200d020d090302060405040e03210105010f03090b0a11070503040b2505060610050c0610 77
    0x10700a5142140250200948036032031046071440c407c041d1174020171030b5945488003001884040b00c05641070107506000a10b06502003011a040b0682104c104044565071030b441c0c0840b100740c46046140c00100700100003520300200640000c44020302540e0a4810010014000c0e90241100f01c58041d4040014001c0c0008010b0343c50501c1c41307900f4100e10300040805588910302500d44e880c60034003001803400d0b034454031070581041903065285503201c0503266507120340d4a884420084000500c50f004411052a1281840d0011a90043c14a91400c2c0c1084d0502014248002c4840001c2c4420444071032a50100a1841e5a00580321540c5001d03505240c001004400038000e204c0406062002707000c02310340540c00e0240c1007280070400140481c130080380d107107280c0580007003c0c010b40000300300041ca102200d001841060280e0a0124041141da1000308041d14007440c05040d6034060380c0010703014200725920a2591600303040040c100503902d91820311342a0201d481100800f4840c1c07040100e030240c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 886258579 1250 886257329 886257331
    0x403050a06060915080c040906090b130302062d0402010306030b040c030c0608061c1b03030306090b01050c060a05060d0c060f031116030c080d022709040f0f02040b0a080f06 76
    0x2d4032076084d02c40303407400581070340e02c1100300c901e544519a17401d0b040003044a154004003074264005144611440c2004104640700c02c6002c050f4050302030700740000c1c0a0300311694803115115403100d05905495501c0e9841401940040c4228141562010007102143c0540034261042e4418013104c0b6070790b411898110380701441c680c4114103001f082c909000c0640d65140904240c443e810810041c0b0070528241141401d0030f84105285d412191200441459410b8000a06480a0a005010780101200111482d01c26038402c44210303085800032460400541c1c1160390050300040204107648480e4640c4100100c4a600c1100400c1419143c1d001c1540c02d4014a02e000044040c07940c10020329078551310301e400c0f43d240000c04001c050300100c010449414241d95803280000c40c2151074100d1110425550704064003062048140b40001c8415440c1079940c4911075944034040c001d915409548070350b4100e8492000326070003500c03400100b81c81d803200c0704550003e007081402802c800507003088080c100300c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 886259829 1250 886258579 886258601
    0x507090b130507021c0509030c090405060f09010603060c030b090a0e0d0c0f05030a020a050715020c040236040b0901030503040b030415060e040c1706070f02030403050a060609 77
    0x1050546521240d56100741c0032000301a12080461580e44401c4201d050606198604035074460400c881103941c0c0e4880c018041c2100140d04840d00c101e071410030001011070803500101aa070040002481014640c003509410072090000480c40a45075500c0d4015200d0424603900002d55990900c1c1701490210840d03900070408400c100302c501d6034102400c0d103d41c40c100801c8144015803503204200100c0c01207038405035800c6002d480c3c4800e04c0240080d01d031040042e0a2b20300307105400c070101b03c0074a0030100030111491600201803800d500c1e803c1c030029400076100c42629080708491180c080c104051b48003000307200e92007151060f220000420080356641c0034164024a0000011300009000104480548408211058885d035851800c0c21013205a180703001900780c10000c00240c1440c440d209940128450780c04050a2a1504101c81400e10707451201000350340702001050701c5030b01540c0d4546030b8103007520580e460a912602c0e168604045100304aa200e50342d12410003544805100e4410099 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 886261079 1250 886259829 886259831
    0xf09060c021315090e070306050108030a02060a0b2d040509011e020906040f030b06091806070c0507080f0c03010c0207030b1915230a053708030403050709 68
    0x28440750003080001d10321540d2810b14903901c0c02c0f40e1840001250900d00104442007060201c3e00e040d0200b951103907494441151418142800810381542c04002c1d07960030302256005105603594005c40e04090202e40b104a50050340c0c95000d0b940700f03c007074174640050312218112528100c03c040140408c540c0024416086645001603611704ca505000103922150509100961120605800500644116400101a00c440c40c80000410800e49000c603c11201112240301a0b5104911040d6682001106001d40d8000000094401d070284210240060040040720310145d2203c0601d031802d0300105482d080c0d84c0c0803004082451809004c1d071104580d440c0b006d01242483d543c1c0d61100da00d0041c0c0340d90008815800481c40310100c0745d00110507202a110411105035481c4034a039014101c0c0c0740000c240800c8081601c00340d052030f10000003100e102908100c0255988a074440c0e01f80c81c50355200d8210703040650100d1015914211480241c1001c3c1c0286689a15510380316251070440c0d48142012 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 886262329 1250 886261079 886261097
    0x30402090f011a1c0e0a031206050d08070311070927030206070819140414060c0313021f2d050a0e010513060e12060c0d0b01110d0f0906 60
    0xa0004203d6108151038000b07007507100c001a0210308042590324094508140c940305090f06040300c00130700c01c042d03a40240c07146a64045111a040305a80d00c600a150f08081104801000655050007d00400340a07140c407402c0000a03040079414150242c1c804c0d0007031500c601411800c0540a0300550f0700c404219000521800c0640d000b94076900d00503c1d14007427089140004500004081500070000c4908404001c40c50b90030924012101d019503095030411100d440d012001c54000881c54064803440080e90f0455440b00d40382c1100c101d111038102e811422880300030500c6068242620b03035914054640a48440080c5028400c19100c01a0990082500b10418440642100c101c40c104856072a02510480907440140c2d0a40b00752211100d40d40ca05010000c1c4850b0700c030010092103041142c1e401d240b43e400000340351380d0715001d0b20070a5403540d08000b404480a0079601403110f0b14810305003809040078175002e9a0800c0301d1400c0f00c0d00428506c084540c11550f00441410180256091017406 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 886263579 1250 886262329 886262339
    0x304061d0a1806092f0f0a020318040c0221162d030e0108250e120706052d0c030a1b110d030908010f0902030c03010606080a020a23030402090f01 64
    0x8000c40c1030200c0c55040d5150f000d080e009183c5c088981410b41c5542d9a640d5071601c10000355658407100e00f090440c0c45004c0744485a203054003840316405513950084c001d03d00044406c100d905d000c03806010b441207042010561500368604c045131302c24001c26102402c08150038800d0541d4a1182d41103c941902d510002e001130f410032110402a0700038600411241e850120506406842c2a01603a010f240f20380001c21042e8020302d910700d03519041c0e500c48003a03081c0141540c2e031079009000da02c0100340240020301c2c900e1010030350040e22a1450464043c0b88401010703c001c1c552000301d0010381074200040c4401c01c07540000c80c506c00c45030b5200d06026004982e854100d41d105012401c0b51060310305060715403c1c9489412560050301c000402000440c0e40b030a8500700405030303208102c0c02801041070070710b014070b010300c00d100407100e40351a20000c0b999464120350080d4407a05848045c4107140024000e1311500c0c041000c0e80c0340141e00c2017941c900b010700402c81c417508014450613640c0203050040c08 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 886264829 1250 886263579 886263611
    0xe0c0609060f07022b0203120f04170709050903071b030b06010309020d0203070b0901090f0f05010c050109170301030b0906090d030c1e030c1407050304061d0a180609 73
    0x500b040307100b09503150b884910011703d01c0405091200e1140040340c40b0000017002d101e2800700003e01c00c41c12111086403540c3e040e0300da070245440300c1a500805100400000240300040e10318112007109840e00c268035403055404403001074030201c050b0341c4041120000c2101c0400300040060201d9000d142083c90342d45ca40c10401e80c0100741c41e04154580da54a800c41d11080b07100d0350390650083c1642d43d415101c0140410b150041100c0c0ca0020b001020001018408071b140d100030744001202c8050540e0601d0010340b2641190304040b078582d03603200b0035100881d410000c01c1403500001281103a9951544c1006005194050710106044c0c00074818031200b800001040d20035002207042c0400e04560341c02094801c00c049501d411200c1783b0003030828501c0d550540c03007420501c840383c50b107101c0004070681115041c040e0300c800502540c0200014001036024400f45120038481d10f1a400892543c040801c20311003d9a00c0864031445a0380d0f075035280c0400e4007420b406000c080300100809621146c80d03030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 886266079 1250 886264829 886264837
    0xf1415180d0305180a03021f02100212012c01061d041107051e07031506170106060e0409020604030b07051204120f090506181908010e0c060906 63
    0x218619600140400050900195069040c0d4008162094000c82400c1c00380041d403104100101070b00caa644150102d140007040c41c8142c0e500546003405849001520070309100f0f40d91030200a41c424002540140780303160009100c112411104c440155160070080e0f586400c07001e501801804142041044119005440a044a51a103041455244103412041c8402c0c0d59032a002d4005041c210116021000d41e0010007100e48507604403100d054101d0311202c0b0080300b9407a0040c858001940c00c0020941c038074041c400d01c1048510003e452075a5486d8080d403508070b04c018500ea41d4541808101a540101d095030800342c080e00c0601040c1015800141188030728000240003842c15801b0030403181c490802c2d602d81e0325481c403041415092504142700070051100c0383c040054800c040040300d29102c3e01c0342c80120350000e0300490500c0d08070680014a00e0040003140d40104840d07201000c0c1c0454000f03030394014201d170000001e56040c2d0140701400d18088207001c40c027440342040180d40d980c886134225 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 886267329 1250 886266079 886266109
    0x20c12060f190e011d030f0403060c090e13020907020601180f0e0304120611040617070e0306010b0d0609150303081306020d0b0f0904050615011b05070f14 68
    0x801c00030340d01e545070040c8a604944690308a02e28000c0d409000010540c060304c488180301c000e03000560300b00c2c600140d42e0702c2139080d205c4400c070080c001040003c1c101c0d0010401c1c02c01c18104542c2c415240e000f694540c2c00102d5014003200c400d20202d000b58100003e0081e080452440940310311760510f0458004003e03100c400e591000d544160086001065034003a44a8003810406d070f03940d603582c582c9040c00c810066002990b41c20703d0b02d40e80342c03c281d600100321411070300c00d0303100c241c00445070140120240b140140004c0030f101040d650307154103076400d209507400303000d010284940340c0c8880c8a05a040b43d019030414405245008008106551003604080c200da330f240c6802c000683d1a18030b000e98918407a00010083c0b400401c0700d411044540e0001140c1d000d065038400f80c0c44021030200038105c541998094070640000c40031580081c0030f1000b01404110605081003850400900c40741a0300c2e24034010b588070f421120301031004213103130481c0000070801d1b580030301d180507007080004400b81d02200321 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 886268579 1250 886267329 886267351
    0x9030309031d1e01050f0c0106030515060102060609091009080c070f0b2b090c090b06070201080c1602030f070614030c0d020a03060503010c0201050f1803071e0c15020c1206 76
    0x143ca442c0e10a00c21102e18611700036810303468003041e1140a003c0c10403800116001d011705075626410141e9400c8031445044164020983c075198981030201c0050080c1004003180641441d030010701f41d85000f006040d9105032030056440e42e54085407070529410350044e12490041c40c2040200981d0300047c0c0f5001800150300c0c400d019142c0307042000c02e031801d0007441d40302c5042c40c0300c25041c000c10039003600c00c4413003000003030048985000810403188213080d4000e01196603100450895000d181c06480d0348400161901303500c10301600080d1420543d07030042d2034250301951040c007401f40d114440c05001126140b402e070550504860b140214010504464215540070a0f0111f00d81d10a812078030007041e0141c020003908404000081c00380004451000c1d0319040b010110301040311a2010603030031041e42c005036060a99941e01d25488000c22003510f14201294020a000700b80c0c90101c410003032120305041d0500c0c4500c850081d082021100f409440388074800204003076004c010a0042d8070030304082d0303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 886269829 1250 886268579 886268629
    0x31c111e0a0c02091602070e0f2419090f0507022505090108011407110d03020f12090a030306060302090d0318170c0301241a040909030309031d 63
    0x71200c2e200d0001019602c00c100c54140700c0c0040c0702d20b40c2009000140d500b0b07180200e8490894106600c0141c51403180101c0210024801c02d0b0019a031b4420594501d14100d03003468040001411422000000180c403144108204541c01140c4660815030100ca5030610107860000d44c00b03905ca1103c20b050307000900310071491070395000142100d140900001082d000340c0e5611409240c1c0201015402000c480f071105000c900300f540110401102c15003400000c01c0308054464049020350010356031420290402d0184010f10000071005c94813440030500103080000e5681001020b0b90b5160f80b051051600c10080e103810354840483c1c0e0840781d505414617000500c0f04811010403101e139070b4808030703038502e031701413034081815010803000030180c412002400060360b66462402c3d60305003062144107540745610108003400d1080c0c03006420180d91910b079400c02e42d1707421510040d501180001c8002a6a032a9503504140d0000120a880341010350b001114a8500300403d0100941204c49039410002070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 886271079 1250 886269829 886269847
    0x50a03050c15070501050a0504020f040e03271f0f0504050d111c061b0206010b0a080601022515030e12030603011d0d27050f04060305031c111e 63
    0x60100e95031941c0c07041c004c01075460b215248100421080c0d402b00e100d40d144091041680c540f40c010358541d98041406545481c00b441d250520f210005402207403103250142c0c3c00d03521643ca4000303c25840c18020803d03040800f16400080803665080075001c00d21a05001c2800551614502c4024040d030050010b00040402c80000322a80420b841505e4201b00134261202004106e4020b9201290325903640c40d681d0075000400c0c6d855410900480100c66000e0100c4880c141c0b0440610b5046a810b0069540e20752012405042019191b9528075008418000400114010030401c08003590b1524080100001518107152200d41c00320398035450b0321003c00425042d541c00c0d440b92070003021b41c0388040c0764404030120450b00e8642c2c0c2c42200012500e940b00ca4444000384400c0420381d00e0324040030500d49400c000401103800c02005449401030390b10440440001d41c104024604040c07001d800080d8140006144015942020b400c6038424030305111410082d800c03940f240b00168000742456854107015 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 886272329 1250 886271079 886271119
    0x309141c0516061e09030e0f01021216060b0a0e01150c050c0d110d0605160c210e10180609050319082209050609070f080601091a090a050a03050c 64
    0x40300c075013109290043d5001050303001000c46060708400c0c1c07000381c00000c040300160b80355181c40c24500402c0404216200d460141e0600401003184100b0001030889c4580b008070724256081d0304198080b00280c07005103c0c0e84c100c50448600504c0504d80141c940ca100c0c3d83e015121804001c0c90341c0030b0510640101c042140b810145c00541001401078400d812090408034007418081d1500e505080c108060089903900c0b42c18840c81c0c03180c1202514a00780c88041002000500c0300103010200078540b030410a0940d1b903100d41c154508110740d503900740105074804810828940b644048107004649000f00245e480106601c0b001440300302000e0036265045c1413050f12882441d41c1100320100c0c02100002d60041e902030712068980a01040007182e0300d0318217000e00d4110658100010502a0010240151041ca00a544004185041800a59244000121590202c0030081116804a9801d2243c100492540c008003021600c4200141ca03644456854060161215000358204e0204409094034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 886273579 1250 886272329 886272371
    0xc0708070b070f0321230705040b18040213051e030616030603021005030123090c07030c0b040506061903081b0a0c0801021305031515010309141c051606 67
    0x103402c051000440c40245c100e0018500d010340b01b40703c103030021411030f090107a100d103c6110744880d8513228602802c2c48c940c80f406400101c4c00b0303440004243c51030440c0340c490340081e00000204100c1d20101904000410140c1015904803201a01d00714008408035580061019040800004450203615500f4800c80142100780c0001e500070403a0b03441d45000e1a4410000c45c101c84002d9054840300305408911210013220000c215408800d440114182c9070308200181308980c401c3c20704100d407010399982c928003a00c0c1224103448941001d020400c039400d0004040c1d4a044214883d10407403030540c0e035290464005d85009051403800903054a800c2c030820800c68403c0f50300445a00e410540c0c500025010b90300c41c001c0c42903040b01110b0001864180013074140c2d54806c0304070b18005595140300c12040001015500740341015240c021143c00305544640007448170003100050310b010002c602011008040100d0002e041110410074014021404c2120340340150b80541c0200d1000a140741c00c40311020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 886274829 1250 886273579 886273607
    0x4020a17180312010602070e10150c0f142104090509190501060f0b07030e10051608070b060906011407061d0303060301060608060d03031e0606050c0708070b070f03 72
    0x720001c2c0d843e0340b0480d010f07440d034100c60b034aa080750f4007aa1103041c1d8100f54501034407201c03800381c104403040c40549564a000b00d4128440d1412404070115034071003139400e4120b030300d0548007a171a00c0107207804280c0030320a074600c0c03048210700c82140308a2500103040030302c11032281000044c0c2d03590121305611410310914081300a43c5990042c0c002c0c96040160003058035100c3c1150400d104e5000003a002c200800391907100c0c2d09a01ea24400c0c541c80702c00c0c00404000382401d441002410403500e2403512036810200142402038100c903880b90401e20b00004000b50103444580b25101810421560781c1e80310344490303401030200c45407640f81c030881c1c0781500c040c013000805896001d60901ca0041c00283c000051442080110000d00c01d096445209440908096900b030b034018500e20119400319000b50440302d0308580c0310070f07000507107120b11031800110f929030f030071900c00a140060b400c40316810400140c4060103501c00500103c518003019203100c1e00c00c281c0000d019005910a0205042c01070b0041900c1c25 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 886276079 1250 886274829 886274833
    0x60e15070812070806030c0a03031107080d021014161103090901410d03090b070b040c0f060f08180105040b0604112d07050106090902090604020a1718 66
    0x801e0107080a81d020b02250702400184040000402d2443c00287d0718151000190011640d03d00310745084556540000d003ca004d403150080c00203100c2070400010303006c21003c1c2e001c1c0c900030a05400c0b41c1d003500d2503009401d085241a0080c090b03031420711048c51021109074148101c4200300d4030320144c01c6001c2c009516500c46612400000c02005661102140c807495842100c1c0700015044142c0c00310030140360540201a84071101049400c0080203001858001c2c1005005c4640c0d4910f02c12969000200c11a0007041c0303902800304001c4042251405481c42e1400c0c85442800c00c100201948000160081009101e40c041070264500c50210b0201c4c000100003405603140c1410710140703410003620078a000d1031800304902480002c0c2420303214105010080c107215110004030360010382e100c0d44400d04800b2020095240011002d2007030031300400b020840880c00744500e0040202c0002c00a0200d8003480c010010054800e80c070942c92803103013a0005000302152500c02d481009100040c07030801540c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 886277329 1250 886276079 886276087
    0x1e01181e0218090f131e05012c0706020307080306040b03010e0d0f0201061409090f1915060501080f090c0315041506080709020c01110a0f021006060e150708 69
    0x2d240d041910300b295901541d400966444035054024183c50855841001d1014510b0610000c1d80031508141d4a48803074a02550541c1184c40e12802c40b06040402c16107200c1446c0c2e00c010b641080061550320f26010809841014a44880a501c921400500400c0d1007000000103146940c3d0758004071038008060001c00c440d10145a50541c0c400c076044400000c9200b1544085007035105000709030948145051605244454409124103003030043c010f03043c1405020081086a1010019100386601c282d03044c001c06905401c0000f58980700c8440700008a007060420b03c8540d0300146199004205600580304540c0c03051b61231410034143c000c241b0f40c1801040c400c02041a00d401c0105d01880c01014800c2c021540088001e08444a510842a0540140c10100a200c0f41c5a014186c0c4842c40000071a074449a1442d40c0c2c4c2035444002d402c0081001020b0095400da410807900c40e0440e142d050400c005804c101d0058103d040c41915541308086032080c03440e440d1f00e008103131130300a40d001d403541b610703 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 886278579 1250 886277329 886277347
    0x907140d1803030b041b05030402040b030d180905010b03010501210c0e1305040b010308181504091a030705121c171005010c06021605060f1e01181e02 66
    0x71003000410140c000078204800c1c107003240740521590032408030540c224005240c44180564030341d04002c00580e807007035a031030240c14141c500b84681e402024140d81c5000e0720700340e200b000754007814050f00b28a038024544001031005640c024201d030b05444003400c201807900040000106d2603045400880302141c1409440d4140340e4006015500d00d8100700e800203c48144071404200b1104126000b501c0511420010804240c0700303402401441881c4080320b07803443d0240085280305600c003940340001180002c040100304420301c10741e8000c446d2090842c000e482d52100280e40c9407814001c5d9031007184046048018861701b0400c034600036900780c00e00d0a032000690809800907030210700310003e00b5920703400103801c03080702c10f0603600f03540058462520250464490300000d4112010301c1c00f0043c154480b04e404910104000c43c0300d0340d024500d03c0d101d40390299200745d05900c03c4085003912004c400044c031100205050360520700140400018115000360030310441c0e952450744201c404d910008000380 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 886279829 1250 886278579 886278611
    0xc21030e010b061215010c1b061d090c0a022d0c060a0c290f04020a080a02010c020603070e09070c110d031b0309170106080105010509060907140d 64
    0x4100e4100c00c0c000c01110481d541440a1071054220540c139020350080000c5982c201c0200c2900210010b140c02d10b401141591501c10310000028864100180f100e01040050b9100c1010740315110001006801e41c090034000ca540300b940a003900c03004880c08a501e61559108000c2c03084030744214100a1520041d150f404040506001c40c0c200b124010004030818131300b059021100e12050642d1481c1c001c90303050b00d845884209039a443c901c43c08080000075640140d10340b2481c007481120b030605505060038410401d064495610084894008841a0340584c3c1c114800070100340d01654030503500d40e12000c0898040994580d0168425151004c0c0200c00f6445100081000e1045512051031007440c010890b21240e80c0b40018009064020301010111420200c0c1c041680700e42021104180c8542c00c0c4070100003140c6502c02e0f10b84d518941042150001d014180c01064260740c00e4442c0e04141000c1038550300000c0241046c00301c0c900c820f848010f0814111107694104840801c1451070b0074417030f08 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 886281079 1250 886279829 886279841
    0xe240f13050c222406090b0a08090304030204060e0f1b0a08100f0e1605090f130608010203130c0e0103080f03090a0503040f0312030b1e0f0a0b0a110d020307030c2103 73
    0x1461a0180a0108171140079860010a41e8002c891017400e21100300c0d41160384040040240801c2c2c041400008010785503801540068941d2078044030903854001d440c08150900101403425001c0399070780f100e00e40441c000881d81c840142d45843c1c604d940da0480007192400c2c0d180e0005005100030040003036000401d03002140151001924086400100c2000300d0742c50044070340155014180a04841071482e00d1a403605041c001280081603050f6500c15450032031300b040301c40342112000002c440003004500d2544a001e0010200e407441a5411911140a40c1c05180880805020000042001e10384100800d07030a00d84c0c003004599849441d02900c8112803c00d12044850660101c03045001c140070303009a810402d8050480c030310410300700e43d48007400038841c2255074004440700d611000d25201c42910744047e01e6400501644c03408048001810300404000e232001541165007103000c0158080103c0f601da64142c90034800220f298100300140c1002800c070300260b024015260300c6150b030580c20038 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 886282329 1250 886281079 886281131
    0x261c150501031a100503060312070c050d050f070f140603150d020604240908010c0c03080c0903060411090c040e0c030402060906030a0501030507080a0c090e240f13050c22 75
    0x24400307000510140c12700720b0141500c010058401060144014240070000712480390084040b19a0408a81c0c0d200d81800c10503040312040c14070000e42440b0f034031401800e1426818090f80c240c4c2c41c52620411400041244002003480780b0010180841950b84071019503000c1d1401e00b01c6164000300801121031b0b0001c514265102090807840700081090041c0f00d2a20603440b240c840508600069404644142009016404c0700b5000d21500080780c404001d50791246105001d801e0020407002c0400004d12030090084845a00c208002d1001b43c60072a41da60b0000c441912003601c03615a07200061803030261a800980141000c010081034140640005040324060b0094840b01512211219194644884003400202c040f0008003c04502e07903001580020400047d82c60b50030540c001a011a80c000c05900300d403071916800c0c0001e6015810303810340c004030310000c204001c0c07245036600364594403c0080705220705c2c1c0c4404074590a4210242c4410000c0e40b1301c000300101141500d0070460780350f030351400d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 886283579 1250 886282329 886282333
    0x6130807031104110901111c0917010c1e05070b0a0209120708031b010e0601120b0a0513060b04091b0f0812040e04261c150501031a1005030603 63
    0x44408141458491510140130310200d407131030428814010350725100000780118191003048040b60741c8292260302107442400d0343e82c3d00c0a050b1b01e001003002e5220110045008241d247c10685207440c1d40104055545050840d00d5840d207640406040c0e86902038080043c10240c0e045007080b51074030319a4000d016110081350007564000440f00256501e1b9800c0c02030340d0443c0e00410001c3c003600c0c510500d6042c0402400008030700c0c1401c1040ca03d007081c00a07804402d4102940300e40b001000025403c00c3d80c00003010b00d040000e860500043c05d4141c035040700c09445540c2e100c08188154030740790003904000e608070a0555241c101c24048114040440c0f00741d904034240c5280118207240701240f018500e00c000a03a05d410305040c000c0007101e2510103002140c1495142c200302c038501c0c00c040e03c03c2d5014451030300299141d102c00341441464081440958424a2a003d542040c0c0c03800b13440101c05940b004e207400140d07602500c03108030080800712840ca60041e0452002d509441d4400003c3d031155005400b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 886284829 1250 886283579 886283603
    0x70b010f060f090807051504030f060203060a0e060904030c03030e07030309050123070821150405180a06240e0402040c1409060f09100c020307080f0c0f0613080703 72
    0x300c116a9203e85014040039600107203020071041c03034000400320303d140400e003003285440e540c0d41c2c42d8218603000c840211083c03600801008254900500550000e0006c1c211400040c84c041d00010412031009000a0500c1000b62105081c180720794031100311b055494003114806034490a0250448040303108240c0081c0003040051007400e0410741c0c120f1540308001495040c0300c0141e071210b8003900701e4200720100e051890380b2180488104c1c90710500805045450342520032039070f4103010541d0001415822903a000b10b1f0b40c82052040041c0d60013130a0b400550003d1003151003071801400303c1d0080800b2180a10b24074000c1040792003200350b2405144202d4041103440c07280c501c180e401c003d100d1070200340e00c5424003c490050401c4c0303000340f000050920071945010b0110001402890a41141c0340c001104a0a144214101000150050005840205012400e40d81c42581d9800c0c005010303405041c01009041c1c8a44414040e10402034900928080c804e8985a401e50b0340c120714441901c402030701c07034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 886286079 1250 886284829 886284857
    0xe0411091305010c1227060b01050f040b0c0c1e09042108010e15010903030f1b060c02060612030d1109030d230708070303020310050a080d031506020a1403070b010f06 73
    0x881e1b02c181c907507008141c0e0400d202502c91100074800307203034101c0c14004100a01c80203c402100200040c0010440b901d848508070a420b52810044030341c00340c058803142c895849400b6200500b842c03940e004451138000c9545610b010014080d0303010428284080b0600f5400c01c40c0d8101c0c02413416506069080300315680c40241d4411810220030b5154081b900106050000c40e01c607100d107403c040c020703051002c0c80c409148524190324070104010b1b9980d9568404c40154168107004440e040001103923612411003e62180c2d80e164401e442607000c003035950b1071010318080300f0041950084c00e00201030707501d00c900c0d00c080070f0b01030304040d80d055140c0b108401c40485240e041d4000d440c07600da081580c1508100465805500079400030b803000c8804001c507070001401743c0c1c2d203100030f00c058510b41e00940080751200402a0694082451030030280946d00320901c642540002d03c9401c45800038004100750002c070703007914114401d00d50042d080d81200e40012402440c451840740440b1040d64542d50040d81c21 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 886287329 1250 886286079 886286111
    0x7060f060e0606030703020f1809152803050d0305012115050705093a0f0204091703101805070f0302030a06170105010603060e0411091305010c12 64
    0x740100325901c1600400b00e21542070007806581e100c021400c00502d000001c2004d1000e075000300348040c00b1844100d648054509010440942005403140c1007661041d0a40c00240d0312900b02020b4503180a02d18030825190001d01c1c01d0340d00039a0403406680018000d0039004003d0a801d0042981340d0582d50403880320312028144500b042608402804080084a091031000d4040a40210200001030007405400c0d5118243c500103e615580800b000c04030a403103e615000d84442d0880c0c02c881141c5440340070803281c032440321217198100d8001460b207150749080c02004601000540c0703080c0000c0304003c1e19403484055002a1041c42111035000504100e030a010760700304980f554005130002d8042d03c0014046e802464001080907804540c0c20741707446e444100c40c101a0002a10342e03440328010810607425216210291400c00341001040c034040c0c5641d1980b06080d41045d00403011070000a8294030030383c0000380c4556104000703010030b001c0b0a00046c07095040d4500450310b5440d02c480941d8030516 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 886288579 1250 886287329 886287341
    0x120109051f0b07080d110d1b0c11060f2704050105060a020a020f12011e061401090b07380a020c0c060304080403050706050703020708070e190f1107060f 67
    0x365442d80c5203082000d41d114007680c1c000d41002c40d401a01c1d400301e54148095200070f01082c42003000001341009490500d601040204080c0ba000d00a10310f4080000c2851500c1041c1c41000c02e60300d540e03039200c040050240034811441030300c5003900ca0384102c5a4625061310708015482044401b0710040e601d4804000e83c0d0f2048426550169001010320030050030911140700310008002c02a1200011518425007994403052110f46820040d68107076004003982c0c40382c0d50250500c41000c001394000580042e180e00d6560081c2107030082c003c5410f004008842551020350045201402c1c0c5803011b140d40c45014400c8080398441d0100c8100c0068882c00a510030707a0462407080c001000c5482080381405038603400a042601c1d9500d0401022010410070400c0b00020b0440f66521583c0b00340c0e6080003828281c0366000f011450700301e1310040050006000e002130704103040716101c039004014920840c00410050352141e5440782041c8034202200c240e080034004450146506001c240c1c0320050900480350 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 886289829 1250 886288579 886288589
    0x1606121b0806100c06020d02041a090d081b011401031112060a0207080d021204050f03031605090409020411090103110c030f0304020102190c051011060a0e03120109051f 74
    0x141d210010319546009182d07200c40e41c4480c140055104481d40364281664000c403c42c5040e039030005010031961020514401001c0c44480c00c01d400c1243c00800a0021004580094016007021420743c0c1c110140c1009000060406d0300200903034824600e0058014100744019500ca8200b0004000c2501309110b805100906000150003551ba03004600402034026034020b0b101e840d420312042d4444c120034401032000030900421840d9501c1e061600760701c3d010320101290703541c6d0010720610549901e95541e01606102900b000c0740c6030826540420020303d05030501a6009003040700d0407078842c00d1300000f400049002c0c1d030f050000115078880c03504248202c60403a009036204022a91601e03940d07102642e04280b0501c1a6241a160070010f83c11000c003240d01500c080110440c1004186041d80ea55000203185080010044410355009516204001e0030143d095850321140389204105000b103456003082a5601486540c40d0408040100821542e820311004003d445a030340c142d402a0401c1110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 886291079 1250 886289829 886289837
    0x712060b061c2301230105070f06050c0705030d0f0c05090603040f02010c0b0702011e0c0c1101121e15030203030418180f02040b0a060207030605091606121b 69
    0x101d8041c10400420740d4883c0c0c800051444080c2164050320300d2140f40c000e02031090485220038020301041c82200c0d0201902d0706010040214000044281504299803600501c0c0080c4a40d44c94a1501241c07240300300080c03050100141c5032401001c181e2100301c1700200c141c1c013040030170721b0b10000303860f20f10641c0034003170780b14000780001400034409246115a06106240490341001e840c1e071129980381041d03c1a2025035103030307503070b40d003810211391000c090345004000300f40941008007101500454041001420208a43e05501c000340d008014038070850702140310404c00555480110301211a640400c060713024201203400f44c400740104440c1040c0c80c1c00030050b42c6411319101800342034080d20f50700030841a44079505c102000c0303400090a100d10380581d80207900c0c0d2900b03104210403180e091010030312400711100300744a021b6000850b442529072101000130b00307803107200016103840006554000da210340e400020443c40c1e03004800c0e03840c0c5c2c0c418050a116009900c290030345210b0312602c0b108001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 886292329 1250 886291079 886291117
    0xd1407081b0f0903160b1827060102120a090e0a06151805060a0e1c0503040501110c10020c0118060e1e090f060a060329120712060b06 59
    0x1142c070341c0281440140201103c82e0b03080308070341140303d081c601e40c491503041401050030179003009583c0d4900c130310703d070f08607001064084442641c0c600d032980e25003842503150181001030341c541d00801c5440c3d03248410540464660302d4034140140504054080e541310151154041504481903001d0b11781070f90000150344402c5c141d05001165004103220b20401008030302c07034001580341c590340e009084545203680e840c4004440d41b814002550804034811584a0f00d0f6000f60000c00d60100c01d40b402d503142440c10b43d11a001c1141281e181104411400d98401001c1d8460501c00d0780000c1e8040d0904002e894546103801e08010b40500c4811901c603d03000300da681900707942c5d03d160100c0400340e4404070024403c0c0300e022090100d00c25071403c845046c1e0a10040c428000070707240103803c150040c0410324050055064280b02102070b080d18501d101a00060802c4410342aa0380403106445201e5041c100c40c000780d61010f0000928442e9007040c1c42203807400004c4500f07401c01904407040281c044c4120018 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 886293579 1250 886292329 886292347
    0xb0a0c090e0f16020304030804080105070e060702030604060f0b030102120618070e0d0804090c11160303210b0619030614100c030201061a070c05010801061e050d1407081b 75
    0x46690044040f0450200f0400400019a140302803c060204d54000040b035141c811006001c416402281c0b5201d84000e021410040e80d00180c508d0340303e5440307c00841c0071000c0b10b89040280c4813006200e50301d9400410102000003084608074403030081219140e11a515104842100c81000c0e100740f800515450102d00d0603040503040030917424800d1081d140340c26135403085041100c8601c6444000549440441c2089580420072540072101c07261600303e86da403941da40074040d0300015425011480210225141c040420b03480030203510005010a80d075801d0250154001c5c407250701801c0040703440c000001c658407400913503c6a0001019080c00b0840c80782013070507110b040324428124115921581c001c1130036950007400e01c81d1448105a25611012146000440103005411403810460003100400ca855400082c8200c4461400031a540c00c2c1070b8100e085813035106104001d0318550520075401101703031030024a40e124030515917460180d40c50340d000c42485041c10103d03030f0802030b009002681d5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 886294829 1250 886293579 886293601
    0x3020a0b0915040602011a01050f04050904050307050a032102040b1b01061a07060f1401032a0e0103050d0c240608150f15030d050a0c0b0a0c090e0f 65
    0x940c58400800040b41420a21041c030210340c05a0840070041c1d45400342054400c020001d0116140c41c2401c101c0d0908101c0a4000058000c034442c4512a0f6541c101203018803109008907840e640d00002078440e503241e14103014110040c910f0911500c14045250070011103900e10a0b1010f8601c42d0314818603201d000180c081c055080c029415405541e6090000360451003507041184401103540b0f041d03152922410702d0f000710f82840f40648481c034204031550200c031054142c4641542d6008000c240c1c07041c27801103000d6051095210710a40c0403c07103c0c001c56003126015034141240e220310221295903e00030300485154111a00081049504401020004101c0810f1904c115075211000a03451f07601c041072841c2c50300c1009211303055846c000c00d210110706201c0070280c1c0030800c541c88168496070340021a50340c90400e5241c03070800901082d4040000e10030340304804015042100104035040000000004003130f510040c9012591410000071003100c3c02d8440351140c001503454000365038841075071003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 886296079 1250 886294829 886294837
    0x42402100903050d0e0d0e030304030f14031207080a061403101d070b07030f09060806310e0601053a0b0901020409050c16030e041b0c021903020a0b 65
    0x7014420144403088084c881c40c0704458121145c0c8004150301c035100e080c003410071a81d00c25007a0103038104100a0020800050304403801580c00f074010840003100304100350850051420400c140e0300b4010070b00c00a6988524900e0080d01480010021207a480038262980da80805410ba00340e084440c80e03c04407982c6034080100000c07140400d420011000041c581001941c2d002140c2845000c0b500b0001d065020100c07200151103800d10082181c200070019003070b002d000701824469441c03445018082d10b4204040101082400c0104d11b15890003041d02015042030740104c4468801d0074000102880e1280e03590400324180581e81702d412240c0340c041440140080401c209884011020400094003034045030320440c12080011b8451703090021000c02d85c3c40140c400303010310000380404941a4200b44a08049542c9800c04d455004002000f040240401d400703185800b090300007031f56030010740100003801414070840c2d00c0003501200a9030b4038a42f55490102039000403a5010500128082800030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 886297329 1250 886296079 886296083
    0x90804050301060605040e011703030a09030c0c080f011a0f040207062403050724030b01031b030c08012103050d0f02031e06031c18050607080424021009 67
    0x9240036290400710b400d4499542c040b000103100001c080002000d0301001c0b601602d80511a00d01c1d95500c1407940d0740ea0300000e40f6211490b035607800c0c40b01c00c15003320308001017243d210440c0d010300360307941e2240c0fa103c01c5940b2510206508107405440c0000d1499100045007a00400d82001c034050503081c0300007034100043c210b849990f546485610002500110030605500c04500d1400c142549451810300c0340590007440002078680c1840d20340c0d00e4101c00013030910154507001038100703032200c0103d02518259551041d044d001103010500a40d0640042c0c1740400541c85410059aa43e19420084088a82c02c50780d0308808000769400280700e08020304060340d01520200360450a08105000c0380e00a880d040c1003840040000c0300103a00b4560000d034440d07400c41c00340c50605d000c03e96210300c02c07454014801c10002440e032441c1042c4c143c0c0076810060140500015120351381850583d1013a409805401503058960624040b66444000342d8081c4104550140910340580c05160300500128102 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 886298579 1250 886297329 886297343
    0x50a030e031603020f06090601031121010b04180209060405091507090510030207150b040204080f01150509013005160e0106140301030b0601020312040609031407120309 74
    0xa180140d550400241c18251020b00641c03001118524000e8944003103024001004d4200c00d0400c141c550000c110181103e4200320b5a01d03c0c01803040010300d0180d03808815040148400340c1a01c2c00000c15401030701262815075040010305800c207402e081f10810500d00a40c00369820000481d02c0c2060f82009412600f44412500a805615441c0ca021041180c07828000381d400c000800c21480c0c07201a800940d00039003011445c010303258a03002d464944103828800003a844c0c1c00c07508001e4840d0342c1181d00900305542603c548244150646018291114612104c2005014003160300d00d80800c1c403038102c44500240107180110122070010340d220211618159400005c1e4403000b2400600c03030114188030841c5241c20031800c122260114100607040101003101448c903d50422100f00100ea040d01d4020b0b000024039501c0c000100e28500c10080b00420a11543c0240300800001d9040001814840e0f03c1e02001d000b083c0301100c4181c090128050103d5511500000700c00b03000e48d108400701c17030080107 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 886299829 1250 886298579 886298591
    0x804030f031115040b010f0e1b0d1107060b01020f0d110a080307020105040c0807080c0f19170c01020c06070201030513080c070e13080405130f06060305071107060f050a03 75
    0x107450504000c111021610003400003000100201a5505c0d400740c000c0d031200450550400f038604001040c020705d003100324495a1106c20f440344401040d100d50102d0540184030086440c00c03240c5864004020840d406802d000ca01c803582d6001050030458400420020040014070040c00c5522103130000100c03800c0d0191420440200b41810000c5124150540010640381054980380c551004903a100180360780083e0800d00141001192205e071140c8200c07841100f01e102e0300c0004000c600c001c8020002e07404040310010f0a400f2101c400b8100c4104602030700c0c500b008000042ea150010000303601d90246040101030010741c005e0340020b0300248003a401c5144500c5a5907001e5903030f8481141895540e10400c000c00415440c52005540310045c0d01d44c14141281d581e443c41c017a8011809203920454030b140c1c041e10340c00041e80c45a5035920180c1c0e01402441d90720500540102010307120310001529103c0781210322100041e0320030455400e41c0d60f414070905001c1c02100c072900481d0344c034020503480d06 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 886301079 1250 886299829 886299857
    0x23040302030d081e040b240303030a0c08010614030c07050307150e0c0f090106030c0c0501090308391b060916170615040902030303100603060b070804030f03 69
    0x800c0c001c82c1540d4a070b108040c1072801110840c040114110f44440312800c0800001965011500e600b01780c2c0b02c4c80c044130490601921501c800c21010340746030144404010050307204c80303c0c1c01c00c00005020ba1180f219590300c0c1d0004031409815030104d0958204100b000c0b0781c40403201d1000748003260095013641d0404c6541c1d0340d0382030000403000c0040b42c0d0030b071100b22900c040078003030180180d002e00848200c1010014000800c102400511980b028150342e4800b0302031803402480303410343c0641e008000b04105503240c500542210310694540703603a030041c81a00008000454411140d1070206240071080d4184551031402d00e500400c0644c61500a000c41c0c800f907038008104803402440c101c0c001c0d180c03d8107011410041b465199200380c26002440c009034004200200b1401e4005201411030b0140114000219014150780d00e0025014480002003050814026220000341c418554040c040ea95442401001c18050744001402445007044100000341d1421415910181f003401c000040c0d80101c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 886302329 1250 886301079 886301083
    0x10812070f02060d2004050127030f08070506070c020d0f231b0d0201080106080403020a0c2409180b19030f0b0901021201060f021006090914010209012304030203 71
    0x1d03075210100c0c4e0341c54180c02194800d20b01d0700c80c030782d500800520a05081c68000000c2c5015008808441d00c0c402901003140c4551884204101035a00a0020a026401e170b28001881e603000013802e41e0917000f42c00115815510644200e4001900141040368800c074944900d01d0002d03500c04d00f240d280d850000360072070980f00b18944a980564500142c0f002c039614110700fa109100000344580f00b10058040040103030703048042181075a8441c5024005541c0f640b1b816460100c0c05400503128002000000403407030000d400304480d07000e4819002c58a00034500c4281c0b18000c241c05101034401c060050909040c69503070080002410081110600c0d1600a155031040c400540090340d900c8281814030040c40b817115840e030b800c084a80c008518110341d088280c10000780602502007040320752010401c901d4800c001484051340e10080410600350346044140040c821150b00300c0d5a00142168652942018429a400001d0684491607081d0714013183d80d25810500980441c41d00702480088003580301 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 886303579 1250 886302329 886302337
    0x705030721060801050a09080712030b19091503031d030703060c080105030d0507050a03030506030a0b0f010501020d1110110d061e140307051005091e0a0e010812070f0206 75
    0x30303004002882d508101035542568402011810740a040032071000000d40b480003203585c0c072904240d008841c5007014404034080e00d800b40c0310541c0981c03107010115800020300c01c0300302110701481007040b0440c468980003595070614031014020510912070200c0000d4807009203030340200000c05481074641c90355145005c4408030307150309002480d8040144007500742048140d0341c40509050440c1440310301e50320103a03035414114004041580303078000308555480400c071100007154031590034003151500035190203065100b4491103005200b6000a030325a24016504c502c1d021502502400c7e00012410840026040b40840520644010000c00208051038800d07007004c0c250440c4c004012001c125410714003d04c05070001042e40c02c2c01002d10426941c0020110304941c420346000d0b16882d00514195100c6c022260982d41007001202e11004030056000a0540000b0803241d11391110303101c840c451881c20003405a503085a01100c02c07503540304088000f401e01c0c00d05c215a03080b84408580d01080103900 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 886304829 1250 886303579 886303637
    0x3020d030e01140c130f0f05040b0402091e092d040c150207050109211121011e020a091202060f040909021002010b010e0409140a120f1707050307 64
    0x28000c1005955605585d407010000c00320004001b2841d81803a4041030401a14400c50340700380c1d90f501032010300c1d44564050700c0b00000000c024040d0603521045643e511451001c009100702d92220009000c002c03554a01130740d02e01c407842c00b1807000c0e11170055610750503405882603440988981e400902c2c0caa00505a110460b150350290101900c2c040c0094107008142c1c03c940f01e0405d10340700d500c140a480890f610b00064000758000c0c038481ca01ca005c10b4084045607025050342d2000c0b041c00b101070740c0c15040003031401900003902d8402c1000160140c202c2c0105500034000681403a0100880c600e10180c40191a0000700341ca4a025075420003180079030320507403140c180741d51140203c0041d0b1605003000142240c03a40001e0003c0001900001c04210745140b200e0f00c242c4d80c813038588052102c0c2362040101610384508840b5446580c1c10b209403e6051142c07407000056070000c0340c000c014842d14030120b050416822a45554540440a46075504000c0403c0100f1600e00c2c1e4a00e0508500c013000c0071b000d1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 886306079 1250 886304829 886304851
    0x52209020622150e13020d0617070815090d0f030e011d0618191a0f06120706020616020102160821060603070c020a03060f050f1303020d030e0114 64
    0x16141104641903d02840c07080e5007030040100c41e03d891500c0d19150740c00d03155049500182e4811a00383d48900424098000c00f60b0048400300360b058410300012900d082e6090310003202d0042c090041c1c050441c11044486001680040c800140440d0042c400b142800400e42000f040c2200c00a08450840b014a8094400718803071210b141048242405003940040100d8000c1014000c10354082d55075032050081d004030445203440c800203104100040c01d844030383c00c000c1d2074810305003020680d4075190700f074480324815582c8a0512122090000b0541d00701d81d01c0341c001c0c1c1030a80d02c02c89025030501140d81010f0655400b0050f01d4030307421880604560310740c4500300b00d9881d03070f413903214107a01c0001ca101d9044400403460280410f80e6101000c0c0d03584101585464081089180302145951200c0c1d0700c01080c1c1410080100b95000c0a42c0085101d900c00044042c0305076100d885d46020b29803248400780250300980f02c54001e1314842e400810358540ba5000100300001d0b888641c10200d04110341c02d031003007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 886307329 1250 886306079 886306147
    0x21030c1b0714030a1109070c0209011d16172502010c0305060307060c02270702010c0f0e060d0b0406050a0909061b02072705150a0522090206 62
    0x191142c1c079503151488040c0e00a050241e07482d80c1d0f02a078955010380741841291100c0c00194600d100300e0707101c00201e601500e1031303070310b540e5613054100301d1441e0045140403d4010700000f00010301894841103e90125540e08071865008018010903600c0074140440341031708030304003901407001d42001c07269400c840d034000103070120364000007030807500040c020034440d400c000c400b0003042c0d501c041080c0320160110b0303016548207140c0f200250f0300e4036140403580d20300b14580d0030080000e0f010351100c4803c4217686c079008030784202100c0840e01d042846054a500090912241b40801c109502c8200504005080007400c00d803600c000580c0c8440c1d50303004926051b100e068000400141d0301507190b02c403840f030265400c80440d4000103174a0388114002c1901601030f101000e00001c1d8601060a00680401c408000c42e0a080410121140c16040001d00511804000103540d00304281e00510003000d00124440c4d01e8200f815070f1700a48a404400e0b40d12010600220051f044034005110001c0740b00c004540c62 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 886308579 1250 886307329 886307339
    0xa03022b0c0305100b0d021315020c06040e07080a06091b03060b040b03070807020102090d032d1b0302030705060a050405070b0711060a03090c0603060f0821030c1b07 73
    0x3510481c00c0e40d182094107040a124444039250710440c1078900c00c00000d034a40000c2602100203018019446103481c00b81603001444440640034140c2e02d1744254240c6065906000078003446100d203102c2c920103102c4481c0040d881030310400010343c006c0301011010913110340d46d0701e41d0b100b07450240d0710303880304407145881c03030081c658040c82641d0041c0a04030189062074680303003203405140002441141400214000259402e10030342c11100e00001c01408001074401500f002044207002d0100c02040c5940b914011508080700c4142d03403090380d65a501d01c54803160101000205d841847c02c11001d601c02482000e0008100348402c6118480e050000922132605040503442c2080c0741d0b00c458041c906c20418075011031403007103e0114041098440c69520311500c50110010400e0000141c10019000408950585d141e0080c0e421268000b13440c44505850340401c0b82c9030034018144001175030306420444808120740002d154810075050003d070030075a16629139102c4000300c41c0c181800e41c0014a003440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 886309829 1250 886308579 886308581
    0x5093001110c0c010306051c030c0b0708060f040e070605090111011b170103030903110a12050607020609010c02070e04060b0603040c05010f030b01050d0510090e06091c080c0a03022b 80
    0x4001c142441d0601006d8076003000315400380000c4042c0711a4a8620080c0c2d0181401050030300d02c1c0076440341ca044442e28001e0b00081800d0300568440f44100309100e002c0101e440c050040c00391040e0300c40e0150840c640b4207074080d222644803154485c18001200601c034102d800038468503d52200c090011488800f00f100010030f24154002c400c040524500014004603030311545180c103595202003d00300c0075031110000744d59404c0e9031380521500c200d52007106003044030110b403050140c081070302118059203420304040e082c2c84501c042400160b004104c01c105445881146941117801a03900285a6a01c1c80209803280c1c0101c406840109002e40104880d50b8030080401e9a4003d5140c10002000c40b04002095440740d40908510241c03a0030108454003514107040c401040103030001c0142001440d0b0035502c410049440030074901500c0e20315140d5948842d110340c07103c0c185650748441c55840040181c480c6d0001203038101015800c0c07002e50794000d0800c0c004050707040c42c421a40502d0940c105140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 886311079 1250 886309829 886309843
    0x10090b01090905330412080f01080a020108060d020a4104020d06080d11011d0d0f0c0506240a06020c04020c01090b2505093001110c 58
    0x1d1641da2400c0764150204501040010704a804018280e1094121100103011450001c0118006508490a10081001001c2d2007142092217403a0300043ea6910b450403c4841804d104101181c0c0022200c800150711409a60b80c0c0105c0003442800a03841580125440c80000e4100c240000203401c0c6007070754030182080c444010b00f0380080302c600d8944641d035441020303409116994000c40d00450580c075841000d40210b006000720408564143c034402c00c00030030500200d01c5550103940b0f040c0b2107041c0300140501150300b00001c5401403403020520901103819503072083d281020031401601d41170018000381304050240383d082e5401164a05110b8000e42140300c9112100d10801040c2c0c410482c0d107401050500307028500b01c400585400e4240d9149000d1702031151700074482034615040000c0f083e030600b20a81d020344a038080312580e804010301514640f04404505501030507101159840c00b0070b0412050048405451030000244080c09060940d44c65101101a400001c0350050010f602003101c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 886312329 1250 886311079 886311089
    0xf080408100902010c030503181204050415080a11030f060c07200d02040c0302092e1403060409060e0d020106030203162909060a02060f0106171302030c0310090b01 72
    0x8010710182c507400a441c0a80b0300d40001c052000201c0041c0c03440302e169080c14520000d10041d60034244d1411809203103584240901c9104038135100400c800b0080da46902001d5803003500c020000b0450980320500141103802260768188182018100e143c0002e0041d035010b8046129240c0d00c5001500e09200d04030030104400250180102108055a49034554048115010383c0c001400040c01d0000720040c0c812040110f4000d01000400417001d210f465400c110003186200141d00e003d900c00c030881314100b00741e0055031414824804074200785000d601500105116020008403424142c000c036042c48000c60080d40541d560300010415802c05020784176030a9071844c903480c206c900f4040f02c42070304109084002e01c03070012051f80840305031002040360903650006000c56114500003d009588102c201c80e158a142141c03c00051184d00901c4207a41e036640b006d480701015500e41d4200c0c15501c00f402010383c0e061107450b511100a4509000b10410060b05150100d0881164181919100c806a000b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 886313579 1250 886312329 886312331
    0x31109010510051e1b030c161a0f09090403030902090601030506060f090a0305060126160b0304051e0d03060506090105031b0c120306120c09060613030f08040810 71
    0xb10303000c01540101114105141110b0300200f1015201036529030b40283c9040e661052000461603c0d00300d030000140c40c1c24284202101d0302200c00d180c6013080d09246202d04005090102d02c060b13442c08451015203140d00b40c42c581c40c3d0038500c0c40400a040d18a003903605801003595040c006c015800c0a801e025800301007030134240020708000011409038407440000c0340c406d24010030440100c1c1e0740c029801c401560170404403a96540c50340002d44d1140080e1901e4000300191035000b02202c0c1c2d02264140000ca041e44c103001045141624800640d84014002c0381c503070094056514450001250596031646402d008140300380b841e44d4054100ca4054211a100b4501031041140d1680d00c81d080743d5110800c101141d10b414600c03107050340c050103905100c108a001e01a40e2540280040c40034512a94084030f01003018510361510948403100c916060303070041c0c02000054802c4c10000c00130309602c0f040311a180c408907925160081e4080410030210346503035000904000301d400400203c1c29071050050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 886314829 1250 886313579 886313599
    0x60f1815110105091e1204032a0b07080a031b0e0a0605181011010c2c010804060209011b0b0601140c030306093408100e010e0a090c0311090105 63
    0x90015624140012100d07201650401d610954107000d06c03a01403802d04800381d0688880d224940840d140c0c10f01c0c04100e0218502c01d40d09406141ca406010b0201c0d4916001c4078901541c646031061694081ca02d0795040c951113039115100c80c0090100000b104016503102074452a80604120f4008040d902c800c0c10040180400c8000000c480c444036a00f80c2d0884400080340100340c8151002d002400c6102148d510f0428030540c9640c108125032105080c01480005680c1a0707081d01480320780c1080301324001901d4400140c00609664020500201d05042c407108080345003400c1114000a50300485605a800052060a50700301201040450b401c03110030303040150401103d9075a00004200d00d101d00807034800726038004c40c11590340398501c0b82101040c0d0b58602e80d10014958620b00c060340c900103040d000005d60035a9235000800195554034044d80c14903441c00003110304528028012a038007559070928000003c40d040d9407480118854203040c500503040108000d81d80c071050780410b0240116103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 886316079 1250 886314829 886314841
    0x822080d030c0e0d060e0d180e0c03040b090c151902030903121305060409150e06030a1b050405090715020a0b061e0301020c010f1a0109060f1815110105 67
    0x50014200c0000940c0d2620613500c480c14080d003d04194114821140142c45800349460350040b921038075040d02c0078048400075a240038031065840d084504141c4d0035414400304001904400b025900241540304650040c180d60b800560b92a4900c6556080d485000401e02d050007040c0c00446070640e80c60002e54109031321440400d0300c0e000c800c5500f254518002401c12428180d011041024050140c0a2610390783c8880102c030040c405225618119003200c1000290241e48500311031044001501405c1c00c050140e43c3c50081c40d607a400c0140d910304c4040b41c0401c0d15201c41c81414450081035000307004a84c41d00780c0f10070340400c07000002d400b15001000c420b00440c1034190010b4012405440d042d150030b500f1642403049214421505515500020f81283d43d6501500710400d00c0b655808100454412041260250010fa40707a02c3c3c0464824007080064034040d070b06043c4560200d050690880c2c0d074102c186449000550054030040c8151414141440d42c040504550b0f0b090341c10003000302d41080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 886317329 1250 886316079 886316087
    0x705060a060501080106050c1501090605011b030509062a1509160608060301020d09060204090b0a050f010f120606080f0f070801140432060d0b040209040822080d030c 73
    0x1401b9140a00c13200050329070302058100101401c401041210304059611050a240030340a94400e80e0700044020b1700003010300c2005607106c80300700e40c513441d000d140c414501c00b4001e541c2c0105c40d0f04418a100310001c02a103c0c40041c0313200d1101611400f84c249130f02c690245040e044800707851151603500290362440514000c101c41e40c00da41490902e0296555a200020f01900c070303001e0680580c500b0003801404011031a0060000d84203000018824000d401c0244108042c4600c1225807103201070000440c1c5501035420094440310500d0102da98200034102041580c40c1030340507800280f083d400b0842d00c049010f0f02a504049078407828600c90801610090204806001c3c200c015000910b044805994540c880804482084c007909005c049809403a04014449805d014400b4111000a0202c2ca00f40720b401404a0740900840702d50303221502400ba5040004000722101d190410030f9044d0926200014408480041c00e4921058142501d0a09041004444000349410300341d0307150000e031708 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 886318579 1250 886317329 886317331
    0x9030a1a25120b03030703020706020f010c0c0b150d080a021b01052a070608100b0903061501120905010506040b100c0f05101d01060e0705071b09060b0705060a06050108 74
    0x120b8605110b004802140020007000f03510a1554184400103c21040680201302d040440b2101d40a41e400c0906200b80ca81c00c0e0b403440704001e00042c141917551000600325030709135500003000012401900305014041802e0b01345440c030994110300d0200e03500c480703180d0420802c60324010f114200d401c0340e5801400a0700a0042100309084141303500d06a00344444038510f05001010340c84201d8441c203503900c40181c18144282c40e814000303c040040030030440ea160003210341d1080050000d080d160707114031420991045945200c0d04200100b00e41001405890040031002402140002800d050280030402295582840e6600441035001540100e90f0000c1c0613021340341e00001450003155140c503110b400c0c1000c084142003170310301c0d0503d00c000944040180c0c1b0403040554008201464441280c4a2411412a800f100283e410015400011000c0c048440e2095840c845404020303200c5600c2001e485961704400002c2c0c40120f102000d000303042100c1740c5c001e01038060801c01c0b541031800082c0034a42c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 886319829 1250 886318579 886318651
    0x7080405100c12110111120f07020a050304060f0210090206180102010902060c0a03121514010c05072d1409060a030b040b0106110c0906040b0609030a1a 67
    0x5225640d45524500410690100950100c2c03c41845407403401c02804403000007140501c150f19007140e0718034410b00c0404407903035000c191070001102d07964108400d5403500c00904000440c020001c03480d000030000c101403c0500300589510340b18107a0243c00078a4440c908040002150174501680d0150b1581c0303003103640c0c0d41e85401920b04006945001030b400340010f900d00940000300010001d0004034041011b83da401d109541d451166072610a40c18156498003448500b0126030b21800c000900c081e504100e9148018148130b8803880d1952580c60504a569000e80f0f140300107902c0e16030080c402485241008004821040c0b2045c0c208012030700c5222a0444190140009402256645e6200c0303407240e000b141d00c05102e020902e0680b0b411301c8030301c00038401d410114170920020000540c02094244040c030001d4121a1555509000c0001800c2e10050450b080402003109004680301400850400c40c02148c141c10001d09002d0411140c003070017403c2c400e4020303c21480f00d855038401e03145080c5c019 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 886321079 1250 886319829 886319839
    0xd1103041205160f0b041a04030806010c1e1a24090a0204080a080a1b0218040c08010c020109120c050a0605040503040e071205090c06090d0516061e0507080405 70
    0x1d5980c11021210024203c0090401640d8400301e004000c50801c803188070b541301c0c4100c01000c44407000c2c0100101c600f9a0000c02013680c4c40b0004075194072404881e80c0d030324091003402441c020404800d0b09900c02141c41980c80401d40c000c0701813200040884070390006040700340d04845042d036203800210000141c02107881101c004004c40c410400680541e00508182001d48542002c180340c003111546c89804440040303400580c0d4100d008043c10181403d15401504d10b0ba03c084800541c0c040002c0002d200300c2c1c200c1846800030808001c01d103e03120101d0850b400008880080b030600351482402c0001610400043d20709110000d000403d800707094580c042c2001c110707601c0318a0810b0079402550855000d0302d0b0504104007189902071041009802d1410301002141c0b02c007001c664a415040242c250003840800800101d070500e41e416400c0240240b059860200100c0c8821020001c0755004000048280102d80d4510500046982c007e280318148180350078110b9854190a000758440c00b4422 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 886322329 1250 886321079 886321087
    0x1109042a20010e0d0906180308091206010815060607030519020f0a030e120606030c1302090a151103091f0c0501060308130902042d0810020d1103041205 67
    0x30701d021007501840414004000d000624620716500c0c2c0d104c0000c0c5401c4000303044200c0c006400e85c00b52403000103206070491003141460840c0c66120055001d183c0203a003280d1410b0068914071001d021345c03800b80503c00c01500880900b11450110000064131092081d0f80c100144c10010342c0040c01c40d010b4100752603940c0030255019000760b00705032507681c0400d140d0040c0089041007540c420620302007240b04031002442c807024004101e030345500c1114103641507031010f01d4a1146181ca4a5203040c0e04158420151034013504101054100d1403982c4010904581070007440226508003001004d900220170080d03040000d0b143c0003030320604802c4403400181c008500c101c061039200c1c00c035010481741c003c0000d1001c40c1e035a2604080340e610500000a012210b0500411a02158001c690440d1903202040611a640c0c0803d4000805104400040800382c1c0100180301d00044c443d040650140340f60041e280d00d02c050888094804400135a945020b00304200800180c800140d00c00c083c0c81480c1045d11 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 886323579 1250 886322329 886322357
    0x10c02030a05071508131109150d080a0f183b04020a0803070215090a21031805130e2d01061401120b03030702041109042a 54
    0x40c411050400ba01900440601041c0c40829120303090380c0d85800c3d960050141d840b40b07800001ca003940000104524104c1c1c0e46001c141c41d00b44103458002d0280b800d0400485001e800040304200208800c460300a40414881401900002c001100d8415410204070801140901000204d00b5014481602c03e401c1c0d0010000f81e000212951400c40501c0701d0768900d014401c0f5030484400484d0200c1c4035040c0d205012485a60100542e1801507025002c41c0644034000d0b50241140c211119481c1c002100342d0000034100309040380758840c11148000c010203007000f400d009104c08180c1c0e10015000e85920307020001c03600c0c0d401e0b203401c1190315a08002540f0508032085404c0005150102e0207a6001c03a00e0b0310150f460000352181c02c032612a008000b00d690301c000c0d045035603940c0d07800580402e541004c110110340094000e441c2e8032800400f524074004444d4002000c43c1c003c0c1d0b400c031040a101142454003400c0c81e100308159180901922018410a074404500c600703409080c04081000180a00301 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 886324829 1250 886323579 886323583
    0x901090225060f0e010b0307080d0f030b1c0b0406050f04170d06150504060810080309150f070c0e060306090303070e03010e070603150e0c120411090a020a0311090f010c0203 76
    0x80c40825008203100c4d0980040322607028220351284a4824080d81c41300140022001888a081c100c0076125400580d0b00340304103400130458555155002084c0d014591541d038646407540404a00c28a1145001d00b010b0802c6800c4582c020002d8645070603400034440468031000c00c2c00900500c2420950791000714440c01d070013404055100c0300400d1540303050504200d8110020b8804d41e0001d550351b0b080c0707503102e00c00f81164076040d1081205030740041100c001031341070010712000da10011040d201c0ca04589101c000e100ea81c4034540c00d54a103440f54400f0320030700c00c0070005641c006104400600746814043c03070840e16448081d2450050285100b090300705524207401407140c01c010f003401c1c3c074556a035541d0050090709502c0790644200354075400216503000c1e0002103a008551100e4142d0601801c0c9481c400140f901800c25541e103501083e0202e403e640b0203070882d103d03c03044000075840f02c06114018090326085131418110640900c1001303c00d4540d8454442400401d180c44100e020848c00424 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 886326079 1250 886324829 886324841
    0x100b07051b061e0a02010f09021507021909060501030b0303090a06030203060d050a06050603060711030d0c0509041e0e0a021c0311030307020703030806060a0c0b180318090109022506 80
    0x2d41c4401c004100803c110340c4602034075240490b50000d01048003100201c0c01101c4004000a40c010902109101c9080400e40a400c1c8031f40b000d8210004902d4180c146005103130b880d0f100d01d1300c06440341014031a5590501403041058810f41c01141421100400154041d285010396400c055001c800519036542c0c01041c50740da503070483c0687d81d0304c0360181001c5028040c11100070f0701a100e10404658a0b1784141890042d12282ea0082c1d403d0070354100030340d00503100c810706420820070107100c046c0c42a95503220380b09010302c042201c001c20a8010f040581a035442042c0c0c4661a005802a0780c00350722400e0249814170340b40b0680b107164443c0c914050700d42081d02400b9185c42c0c8804010411521340002d0141c0549000c0d4848503a20741e41e40301000200d00c580f26145000415500c103401c00500b42e514000e821a0000c490300303084403480310849103560090f414000300017002002944c1641880000c0c80e02400410b14258644043c13a080780c214455048030003002c45800341408000d2002541c004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 886327329 1250 886326079 886326097
    0x12071703090633130b1206010f32010228170f0913020708130311060f09040c030917040e01050307031101080a0920120d1b0f050d0206100b07051b06 65
    0x9041b035080c10700c07030aa0341c1ea0303024020b4020700c40302a0700210310340c0c11681144440382c2c40c40003106070342201c2c004d4000e4021903040c0b074030f810f5200715075100700840c45010303000021040301c0c90480c04060741d90600c440c0c0b140951540130007400040110408100c540b00450300340290989407803039001c002e104481d00922848001402018010404081c5607000c945040100c9000d503400c8080e102060040050920801c40400b160280401800c0c00398140b07908003082051890030001080c00b0720b61610240310b0b036070248480b03050310001400d000c1001c85600f40c2c0e0140400340d00070011141180ea41603509541002918148144040001c2403a00d250708110710103075102040484070003850504607815200001c019100703071402404802038420014012b0000203140c3d892250b00000c1d60360240d8041d041000070781e01d0b000d6003a82d10001c2081001410855030311640100140d140c0010a030000310056003001050707c2003044848086200019940d201c410300449014200828000003040e603c515061 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 886328579 1250 886327329 886327339
    0x71203120501140a0f0b0702090604020c25121211030d0f06060305060108150906043315120c0504030f14060109060812071703090633130b 61
    0x21580c004244641d0000000a40b80d03d24129207500d43c2d0117084401340604c48116a0a105075009842c00c0c02020340c22900240c0010b2030600c2111085007444400d4021504550140d40c6481030b0405007400a0010300d038406484102011551360b0b405002101e540b800c04000c0c007c00d01c40303964035043c8122540c104100e00e08001c413000c00c1c20404080c160358821341c00824070b0500021a40c1d40a00c00291060314108690700008203a0380070400100385c0500500c0d000b40c1c1e40c01105405040030000409907228801da81e1800c440032111810401440b41c12851503030124030600c00c0e4458201c8220380074000d480c8404a44669071501c1100c45001e00c0c0d202800070403e2a480324148242103400303a040c2480c4030241c0d22282c1c1c8410280c8240e503030703512074120164011151003815880140181c401d00388a007220490321000e454032a010b9401c140c4060480c0d4100d40140010400b650300c0503482c1d21b102c80c82d0101c2a0700c2800b08070714603543e031400b00c500030340c1c81c000c44d40204403040e48022410940245 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 886329829 1250 886328579 886328581
    0x2012304081516080712151a1b0705090f042607030306170a1104061706010617040c030f030c0203010f0209120a050705100908010203010311031b030712031205 70
    0x10341001a08050390880f0a840140165800103032007481d0880c0310348850345800e00c1c4020b1228494000701450b007003445000c40080c0000c28210140326002407a0740b081c89603d603d80048540b036604c14140340c005502950311002c801c01c111784a1920495001100c65540320103640c2e00d041c03080410308188600d484601408122100d0b0702d4102028185250280d070b81000b10640b20058140c2031070080d41c0215080d071040a10724002289041003804202001d840807848940e0b4140c960b240311401c090051250700540e0040c42401c1c0c0c00000b104e2030038460045c008036030525846d107403120350090002030080c0303907035160703010902d030141080d201e00c3c07a0701074020001c0744030485c035050013500b210211394428103590311900c040810014180312010380050242c428540f800b41004003400707000283c0707402e0040c5213800051004080c4003850003140501c0c1c081e0000c00501d010103041c00700308549021001c0428030044003503100011941d041d03644d030b0304100c0c26424440c241610070504100c0f2402c203640c2004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 886330935 1106 886329829 886329853
    0x7111c1e05090409030f0f080609011412120d0e060906150a08030a1806050c0616270303020c0915010807110303040f031b0201230408 59
    0x20414034545082c180128094a184004c00c1d00460000400c5512103500107000c007102c0521b030f10301a03200d80b410b00002204080107001d0070060840030341c00640142c43c2c0d40020010007a080c0110790303090b000c0d040181c1031a485140c225a041c1d0410b8183d0300c41d16800610a40910004001351403217954008072444407102554200740d008208141c00592600d080c4000d0400d104140e40d410800544124252000e10207940701030100901004469058500410000e400c8000301c07869040281c02c0c10400c0b01c0340c445000d2950b0078403c030303601c85540c4a10350700044c00840f8070070b80039619848501401c1140403039044071305204520010440c60740941c0b007072030308075405601820001d000c01010201c691450b00125001c9850050f50384464040c07541040f1150740e0003030081a1618030b40c0007a800203140c58543e108850700329004015200804000c1d005590180040c441203d10402e201 = true := by decide +kernel

theorem cover : BRFrame.Cov 886151079 886330935 := by
  have h0 := BRFrame.cov_init 886151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 886151079 ≤ n) (h2 : n < 886330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
