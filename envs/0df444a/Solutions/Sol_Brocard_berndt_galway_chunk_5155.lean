-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5155
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:55:41.411216+00:00
-- url     : https://prove2.me/submissions/dbfdb472-2419-463a-8542-e9ce76ff8a91

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 926978417 ≤ n < 927158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 926979667 1250 926978417 926978443
    0x90b180105010806220c0602210a0e01050f04080a080403050f120a080a0b030d090e0c0406020c04020d090206070c080106140f0922031205090d1e0c080304110102 71
    0x50030004000703c0d100400e440380c00200650a00e140140120101e46202c2090403000c0c1c50a021410300143c1141c0018081c514451030883c130b060400c510900710310841c003900e000203000c2110b0b030300007048542c8907a00520440c501d051000741171030740700c001803880c00500aa0482d00c05800103400e00034018104004032520343d03010020b0100b4001030098919900417006c0420600c518075000c91191050b42e009180032020280807613003c4064140003e05907400c034412000100006c201043c064081c00d000c03142603807143c0d002006050150020b000c02588044000c640240c4d50b050201c1c0140d5506005001d41d9010b041e4103280c00381800c80c01803c48401e036000e00709090600501c030042d6150103c20500400f000c440946199441c030f04200040d0345e61200068103100445440e40425420211216401001c054204127039500d0203e255501e6103170541382000b01d03c00b0082c000d08071030310030941e00c044030040c94502844000e60341c41002d940c04c140d8045401030b070781202c004010759040050f8417a00d02c07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 926980917 1250 926979667 926979671
    0x11215080a0501110307050406030203090106150201090b0603190b040c0e1f050108060d0f02220c02150f041412070c1d011410030b0d05060906010b1905030613090b1801 74
    0x5000401510070300c190f2040c0400e040c0c020000dd11200d20030740c8484000c2c5000c260200000400342d000134001c00c03015400302d03801001400802e03620b00300001d107284100b040c181d4150744240740746c071110174544000304100c0e040301f8810808140010303482405805403d914045207681107004591983c207000503041030741000300c1c003810002c07156a16508608000d420614601081c123240c008500715100d00c51100c0c441090340c2c0107008104506034050026070301e1035420749407489110350f000001c2c079030159082460143c02c040030802041c404080341d01c504032010101c482c00ea0f441040d8454540005801341c8a940000104000340d9600c4c4000440c42640f80c982502c056041c03d130052250f440407581c05003c1d60003030303607045051802070780000d14401009108010707918640c0703490b036644c800480c0c182041d80103810000540c82c1c0c0d000300744c400100784402071040c021010a022205604020121070344403001400501c511840d81c801c81e4045801800d03060140c0c03a207905000280e40070100c1c095081d138 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 926982167 1250 926980917 926980921
    0x9030d1106060d060e0610170703050303060108130c03032a050d0503061305010b0d0605090c220915080606030f06151206071e05090f011215080a05011103 68
    0x30201080c8598404000c45840c52402d445040500c001c3c421411002543d120720000d20414410a02c040350440301c864805034410040416071603160112484003d2403580180301194880d800b0f40421548030658002c03058503110103445042e0662801c2e8000d8000c110f41c0181179480001d291449825020608560090b18965694013035949422100607410004003001181c0c0342d54a076041d01000300003070701c021301035941c44280b510790303603031101c0b5103d1707215841c0850010f060301f0807158480c41480c0841c0d119040601700ae40000302c1400165606036800355615003c144c1200314450207002d4003500100003041410161b450786442009050107109501c00780d100040e01c400059010303881071513440760520840304880843d107106111542801a0301920041014080e0720105020800586048842d00400c04030b40c1580d0740d00c1039100840e0030100e081516085540204940c02c840c03032003528009441e0464051071038a8240940082010307400918041c014400d09005c0c1101e2000188402c0e0310758 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 926983417 1250 926982167 926982197
    0x612040b180a14030408010c2c090c0906070f0b04030f0516030513030602071406010504111911010e0f070b03010b04061407020603040b1f0303090b1b0d0509030d 71
    0x1071401ea40b40101440036000c00403048541c02c3c4240c034000c00d001e800034407540007800c1029008519070820000340944e803140e858454084070044901c044400b07821500030380c40b808070011042c0d118180058000c0d2042103150001440405403046441c0074030309408240c1842e2800803c0e80c0003c4801400f000700c10310200300000a420004940d440d03141c1011030340c8068500707403514150602c0e407024000e64804035004043c855a8141c0c00f04044108060f42d200d61b889008010850781c005440d80b075003410501220141400002c0704100a81c05414612030303c0c0790038103102d42580c086500b0f45620f504000c4098000358000c11460380a801c100c18050f0031907040c900300c04120b00403031180c04104132400c000a07004154000445600c02d401410090343ca1600b03003440c8103000c4050341c02c4403030401030ba0f580b089807186401c041000d584e41075641550b40e0786042402c1c246d0741c020b9219960344c81803d0548504041c07041100c542440358603110292140202c004060800244852050901102180042e0780d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 926984667 1250 926983417 926983423
    0xc0901210201170916080f43261903111203060a21060515060c0c040506030703050604080a050f030a0b120309060403061107020612040b18 61
    0xa4114540c01415102690004907403001045044401c2c024050040c00000207020661180c0404c0401c400c0000c9036868001554420171441d41c150107402501e84a1580b040300c1d19084402d281540009504908460359a0031288504080107550100e0140810003100c072824021275844c82c000c2d98651500c1c100d41081d807140310410a1100c0e081111030082e0405005c1d4010324449501041216a0031440041101c115071040d55a144101d1011a0000e0114030f000c00d172000d1060f43d0110602090041d65680d4060040070380b440c600e0076460104890103032640c85c01b60400400020007000205883d4080c801154005800c190080e002040d06001284c00042c16a41003540008001d6803004106422101170290390040b03202c1507000002e100c61110560410602060100c0300c0c4990a041074900310364034440c40b41c26580240d010300040003c200d403640245023161080951920b00002a80082c00a51003c2c500491040c000c000380014090f104181990140e070500030354005171600c2280700d039 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 926985917 1250 926984667 926984699
    0x902090d02060c1e06070306170a120e03030a030504020a29180402030717060105270607061103010f2106020a02011b0c1a06010c150204051008090c0901 67
    0x1c0107200000e810700f041d0034200100c41a000100c20510074401d080600603449201c19140c1e07100190900401140700c0410040c0c140001c5041e200a0180c0038460352a4042c600c10060a00d060041c0000c41076400d440500040410720125079000682d490148100003207407500b50000d204200d5640020140c2c3c1c101c04807100401a5070403461621881c030b1140c0c4240e0350401540f4150014000300074041019003048c81320711244880329008103903035104401181e81e4061801c1241039003143c000c21b0361441c0c4821011295010f4094071a91500d1242e0704c84070242d070702ca07a02a00741c505d0300000400110703031035a024101402070352001481c54080c01000f901065281e01002d030000781d00040c0c042c2200d000354401c0e02c188403c40042100040c45003000fa10846540c042611203540007000f003220360000380000c602c10032050711000c070140031380d480c0c014580310810181d802c400d40c2084045095a2403c1c5c50030752220442c3e8858425290042c80c4a040c0a9a9010076003d4095a00180522640284030320 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 926987167 1250 926985917 926985919
    0x7080906030c04030c030b0906090a0506070e0f0d0c15020a11011407020a03080c1002131401021204080607120507080a02030c070f1b0e01030305090d11060c070f0902090d02 76
    0x1076102c1e1203510024030300e8071403948014101c00c1014800000c024088002138861500c04040d035840380e980f5142d407616602c0185005000340c00c003d00180c1964002e0b11400c44501001e0300c964240d401d2100400c0308080c0e0700c0720981d40d8401d043c000700310444074200c91400001c1184040c00760704007680e40341c1010700d080044541c14025401c3c481018882034000751800150014041c002340b5549080400e803035407001008210f1402600a81e050f003c403180205c40c0c60140d00c0e805210081d1500384401e5030303244454003a034114010b003903c010103030305481e0181c8054183c07030014010790700b40300c0e402a000c07020100d030710074a681c01e10040105464210807160384c440c03035180001d43d40340d5458854100c0c520910304c0050042c0c1400c01c03a4428448461042840040c000b00301c086243d071190004410b050302407100400284d810850103000303090290148004610581080800110b00340000307115400154100001d40c1c44080c0410000c49103001d541c005001c0004114681041c043c0490b099480031a806 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 926988417 1250 926987167 926987179
    0xb061908071110050106020c010c050604060903140703090f06210b04020c07060315080a0b15030a0b010b120c09030706030e15010f0f050307050913050f160602010f02070809 76
    0x180e5034502982032000042c48103015100a51240d65010303000302001c1c09840c00501c9111114102540a5040138032010741020003840c09503156600d010282043d44021010011000b000a44403072650020f011454440d865042e69079041198008214200764444400c104640242402d108030f8032241c20401200044003081d41c03242c120125019100e075505e001e145209440d80011042e9140c0e118201d0a803d102400c91003507030301d15041c0d540d0b900ba4000500800725200101f9400c00c3c41a500d02d01c1800058107846603004540c43c0e142a00e50264040710003510000340700300030390a240b0b408550000b0605540b40c14454042d002c01d555440600942c0d050566030600d210301400f080000481c40c1d480780d4031003452503848102103a900082e910800f0203080070b410f00441c1515006c58190305482d006030004003243e03282480d080d9000122001520303c1d000c2c138400c126503490113200140080702c82910006202c2c2c6490002400c4810100e80b182c010740c814040d080c00916500c0868060ba1070440ea1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 926989667 1250 926988417 926988421
    0x3060901050d140708070501110703051c092601050a0c0e06070609080f13060302040302010f1b051b0f030c0f100207092c0c0a09150305011d010b061908 67
    0x709160902c0f4203504078100340b00b400e40005030801c00041e580c045da042070340d40c07124020700500400e94440311400002c006800c08151595001400088100c1c510a1850010459665468250031460341d035122404500b00361104459985400d000b0550030949014041060440241d0003c12140515201c184106400203100013484131035000029140e400c025038569a1144c104070b21141d5000520305404410314210014a81d4002d10944007181e4040c0c44030441d9489440084403003101c81203103860308004456604e00406c030200100c0642d0058078052900140c01036041103042c1c1c400201c45840307a44418901c0d555130b00c03441c080100542c0e080d1303858150744108440c26400d001c4103810442031240b034012020030b00c000f451600410b50360502c2502607000e640080c15510b90b000354444a801244560f400c008040180c0d000c413403a0802903400d03034101501d84d0f40703103800e4070401040c0d0300d2010f8440420b076408440a22038034180d00021541c0c1b80c0340c105450b0645401c181000d038a1018444041c0c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 926990917 1250 926989667 926989673
    0x913150b0d0212060f06100504060f0903060903030b090604060b04091a0312041805400c0503100605330424030e03041703121003120503060901050d 65
    0xd12062031540186800001d85003c0365181d90340000f00c3d541e10f904185000400c4484c1840b400e0340b44071f00e1190344d440d4981030414000f41c5084d081d800f840010058070080c00404500148550700000c0d21a50380400c24502c040100110080c014003a5445540b800c401002400c00000458088604d00000480d14049103480300c1d141d40e85c626400342e0540182c819004000a02c80020002e8942d00c00e031201c2c041c209034080d1400c450781200d1803a10200000c0e0007030411003071041c1d0b1a210482010307010f955401c1040f010110f000f81100c04660701040c0e1541406146024840401c1040e242c042c01c000b40340c6840002040031003400c02c400202d0106080a85060328410101c00d00d0081c0c118080c1e076100d90750034038012094508018045400010403845503403030720a01400140d42c0c4058000c60800d424000083c598401c1e0300007100036480304020045c1c000f0321504215100d001c0e0034030b00c1081d5a165080c8442a11001001c0b502080400c00070003d250791101c0f03915040d10b82c15a46074800e000c06103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 926992167 1250 926990917 926990929
    0x30c060203160f030209100c060e06090607030507021501051903060e030c10020c12030406060b07030507060c020c061b0c0909070527130302150c0a030e030c150c0d06060c020913150b 80
    0x3045a54140030740c0d400c204433a41f0010f903042c007440036a41c040180b82d950640490311400711400c0e100c0e031064150010000c9107040200c004003034840844d00d4072100c3c2d0f03a42d0b412044a000d4081000c40d9000810304c0706000b1070a0008090850122a05514248013280c1091305da600c45084035407800c60105c00715007844955031204025008800c01684e0f60000b908014080307401030641100c0b95400c00c050080703a90f20224000d1400b2001030202030600c68180002400310089035456401d500ca51011300c21142c2e05e08503030038051141c12000d07013891800c1c0002c0c407a02001c40310010803510304c0340600d801c1402c02c1442c0240d2010004100151022003454100e0900d1003400d941000d46220310301b80050100c03c0802031a195070540c800304890030688000c16100c0c0580c1d40d0501c000d4000040030416001e0070340c6d56640c0b000c079000b041407505070302060190444159401440004486240c0d41003103090000c59507401075003200400080181d656180c205203841d02909800c6240c55615030030301a1141 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 926993417 1250 926992167 926992181
    0x1e0f2107061505041d060c09033c0d09140a09020d05240108040b04030c080a03050403020d0908190302070506040b03100b09010813030c060203160f030209100c06 71
    0x7001082c001e0280d04001200500c0702802000e2080f8030300031809a040030705201180000c20703c4d202501d01c99681460414503a044807584039014060109440f02c0c12142c1c030446540d640c103221241000140b0032039100321120080701c030160b1a0b400507504003012904050040100e800700c6250302c404010301c20104410b03c7c40d60307021040e001e0010444c03151242a54000758800c075001c110b87c110720300c1a5074006051a50700b01c040c0780807a64500200e0b01240941b549694814001c5c02c5c002034284040d0780b641e0803603000003070365400203540d9001d0000301603061041070140202490840140c03030a040c455a2920f041c292600705c030301d43c08990701d41014000e2010100801004007041c0d101c956620403012964000c4641203d0302c2c0c50804c011524102280c155101410180e4910f400c07540e4410a42c1e94404800206609200d0741c500580005009800114400c0889591201113065102d030050105150107450400381030040c44407904a442d00d0366000c0080405150564406590303042400007402d02d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 926994667 1250 926993417 926993423
    0xc070b0f0d0609091b15030902030309090f04140a0201080606220605180301020f0909131e020103050610052d070506092a01110f0106081e0f2107 64
    0xe000c0c000502081584c001d406540c0140526604480c11406202001d50b4a00540c051000350101c0850b1141c441c0d408039805038405401c172131070704035540300003005000f0450718100040105c1c810001041032b0021004c0c1281d825000903c00000c207540040c1011000400d040c4c02400e02155000c11400444c070302d189402c2c1c150f600c10504544030440104543d11205030901c2c3c0022000b01d07102181414803c507035400b458400c03a18200040a800c21000c8400070308072110302403080ca284000705003031066102d154035030f40403084420201d620014003500e50090416115850041018201541042c1103030703140c084860890081e44404501d80084021210302140c10000105443c4100300002030001c0c09084c80f40308031041c0905451220350080300e01e4080c0c4d603441340010f41c0683d455002c1c85c0e0b5001000c5000307082d81c45403030078408038508461403a402050240e010b410200d181c031a0800c11300c0c04005244001d415601e00c011041595280400e50b03d50007007070010f030090940b42200b02558280340e4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 926995917 1250 926994667 926994671
    0x60d03050d060803041508190c050c150a0e01020a0c1b1a130b13050d020402220f050f09040b0612030a030c021e1005071b0807050c04020c070b0f0d 65
    0x511511440d07130326003207801205030250a00a0f02802207000d40b1486101d030350310070030454100ba0601001400750641d00500021300000f4000706890000a0000c0a50000664010310340c40c50030489100a17580350ba80018507591040201e80c95459200c1c6c1c118083e181c000e41c54001d101480c0d1800600040315503c4119a401800f42c400110034940380101605014481c41444680c0c0300c070b201c014603101c2c1004561200a60b86820052800c02e0741c104d00c0305900060005080100302141d03644804d2004010650030040d0a034140140404c0341074440c00b41400313a44000ea50520900801c7c050400a440a4288410200040c0712650750605a003901c80d0030b030081c0c1c0e03103403000b80340c016000e01120a81000075024581c0169480002204251985840d40008100300700390306841e07070024079024040384200300d8403c0d4801e604190b040c48000740d15100704c001c141c0d40c0609003030482c102aa44014940f1450041200c2250b8050004420007600e00e40200f00f0f5680048001c2402d181c840c40c40071008041c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 926997167 1250 926995917 926995919
    0x6050705030306240403140706080603030a030c0512070e091006170c04030501090c090e12031609051509040f050c030402130b0d0c03030e0d0510020d02161113020909060d03050d06 79
    0x4420404070300315407078103031f81101c240c1c5407944070540e000201111b100350550320a1100c180711500c41d400030000000c080c10304520380607008441c1c1110b86000c9501101082d90b0607400d15040c103143c4031066000203110302400300c6a00f020b80082030b00492a03c60200c44500c070012800407100306080700c006680c440001c02100505141c00c4004000c14401d07040790718a4409119824a404503014444081c0c0642c144c0c0ba5507603180e6103124441c44415280200300800a001c100742d01c50b045071801501c2e902407101e071101307208002c000641d070341944104102c5040c881031000a000040036203400c2541110740895103140490b4550080032040300301540824080c80c46000d010121005a007500c1c02a038a07011220280760900c40302c00c5135101d00410030740c0314900c03000c82104140d02a2190040c1004054a80210720031082224a60300d1000d07501c080c200083e41d5103500e03201d045800040e2900e43c2c01d41c1016070007000220b2040e8020007641c0114030b0703c544001014460703011100d0f500300e0000c08000391 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 926998417 1250 926997167 926997173
    0x18060f04151e0e07260709050106140304140609030d1503050a03230d15080d17090c15030a060501020a05101503060c110c03070e063606040606050705030306240403 72
    0xc6024005c0c01203160042c44804039a20a00b8003a40d816920305441c1c103001d07140302c201e5107034096000034803e0350410b0310090b188640200a02201380510605801551650310060480c000c840103e20010203030b480507542003000450204078010041d4160802c8240780c01c20b1124030090003c110700d80c102c58100014030241c2010760380c0c88505a601d0f1040d980500c0c035240d00b036403035a45040343e49010115014190710b201c0d0b08402d901c02640510004140c80380030204034042044080044e42c4455070010100c00c00c80c0109191040c0b90040900f48001e1190240300c0d101c07261507410041c4512551501e43c800d64a008241100d96802103a200c1e00410101c268510020b0429502e0b140000c600d004542c2c1c09031451030001002000d65124101e44005526250108503052582400034868400410040c00142e40044030081500c4200c0403540d069150900401044034a0f079000541031040c2403080e0700120394000203481d40004c003519820f030750608181d00c90110380001c644012054500080100c20 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 926999667 1250 926998417 926998469
    0xb040609030b01322d18070c151112040302120f04140f030303100e07080c09010507140f0a02040b0a0b03070818060f04151e0e07 57
    0x11207000b5454500300b0b90f2512282c480d0800003480c01040080c40111541403000080c001c80341c00c0c03400400603c507001c2c455540030340081075a0400e40d80344a0001820303600d404c001e152440089000f12640c5458988030070064041c1760324000c06015030607001402004a0340b07980c010203081424400c0c45482d00c00c44c007030140720841c080b901140180680d8100030b60300014001502c20003d0864035003030400c0e0034813401901c01900210340c141e00c0094500c0d15800c1e91030500040d40103414858003204001d040070000444030307034050b040c0410040c18074100035008045409071081c6210074642156210110304000414078500400d9030414060950301086100f000a10904102d1007078505008481c0b8500030010141c040e4840c60030601001c20004915500c22410781e13030310031040c842e40b000441c0b0004845c0c0c50400216103010401d5110414030080c04660464254201290401401510414440e943e41ca545403940380409a4a0b03004100600701c043c40301344081d00ca03014950101c14001422641c0e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 927000917 1250 926999667 926999669
    0x1d0c071506030c090e210901050a030f062c090a020906010203070b010603020d1a03030313170d05072a0201082a070201180e1302060403020409110a090b010e060a090b040609 76
    0x104922803007443d440300c0f00180e001b0507003e00e0b1001c3e0503030504207048019181a030101c0c1160781055a2003000c3d1070350b182e0034418070002c0d007203000c160402a50100c0e400c00064030200c998071080c110040820a102c0400240030800c543d058400020b035481c3e12006034650b00400c2402424000c59070008150140c0c551301070900401068070074448090350f41c85040142c2d00c00c0d803d00e42c043d0400c000240240030202800c615051050300c084917044900e0022040c1600840e081c00c00e215103a030b05100426502c001d94040d5540c2451100450031480a0000b4015461810003410f01c0a6038000814140403124009a41805001e00364041c041807030340461036500200c1c0c1203002c02d0f511007411741c0301221808040141c490031002c0a016440d0000010031401294004a0341701c00104004801030b115800381c0c1009502c100786000e64510302c0750030080d40d64050342154100740e02c2c2920320703d160307a4002e00f0b0754181d80d801d503101590b031110704c842100d00300c0c05078001030f078540000103000032a0b80d80310078004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 927002167 1250 927000917 927000941
    0x412171b0d0c050601140f1302070b0105060405031e0c030a1412040806010b090d02040f050f1605090d0602090d0f120201060e041b0513061d0c071506030c09 69
    0x150010010760040d501010510400380055102000601010004080b96880c078480100302c0001c0603030520025155004071382401200035000715104041060381c1603842c0c007400c0c00b00c1c2c850341468101800b00e5682c10144221480d88004c0d102110040d050a00441d60018405419944681c070701c0e00701070100d40386000010b4a144030784400d04501320114026107080d40d030f184000c0c00720f0744d20301000e09289821050045a00c015003504100060303445d480703062100140954086070341d20303184031180b201c014000c00551880810a01d140c0195074000100c942c2000c08a1754500700e220142440c030000e020707003d0b010b5000300c030281400c1d0500c25480c03d030a1003c0d200300c0320100c45040d540022404d840503441034040780d001d010081000202d0262014400400c0d01f000c1081c0e035031b40d807000980c00c1a030507440c003040e0568550080c000111100c880b68200c8400071401e041c1402c103540190700728071a60201400c14004503881980000d6250001c1d0000c58100d11200320140e01c2c2c3c2e094100405600b8061 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 927003417 1250 927002167 927002173
    0x1140408010c0e1801170309040203070e090703090206031b09090109021e0703080402010f2f0118080a0e0303070f030201020a0e0301140a050c04050303032a0f0412171b 74
    0x946650b10b04280e2013000e18610402a03a50340c2d2a200c1641559548031100001500042c04001c6d90b6072183e1020f54403d565650758400c500c0862410300c855a14058503c03010503040c41d18640140e1644002c480c0c104081c2c0d078000303401b00c071980358001c0d0707078052002d815a115440000004000100d5005002c5008541c1c3c00110b1609031400b1b0070440344607034403005000c0384214001401540c0682402c5124181c035007132030305040305003060b01002c42213108508000c0d080c01003103c0355000400d129000500c000340d41c0d02290144652240c030040c0c01003100500070081c6007440c5503101d407010b00943c0c00441c0c1c400304400c24040b840c0b034040c0c040d4101004060005400d124580350a00d8140986030101b40c10340d1128030b46496100c0302d603002d058000c21150050400700310018068900700015072003504000c4210203041c3c10705010700f41000500b11110341113007050000e941036407070803001c0720120307078003509200341d940c1d0313503103880d941d13801400c2c910703288443c7c002c40c252403082804080070103284851002d0f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 927004667 1250 927003417 927003437
    0x30d0908070b130c06050706020f0c070609061412071b03020c240904270b0402030706140f0d0f06061e02190b04060e060c071b03080f030601140408010c 67
    0x100100010f070b00e0000f42c00c1300b0888030204060344c0a0f100070047e46020710405443d01646040c955841da20107035180815510144040003115402020100a00741c5407800300e0401010500b046201d0245104104001c07a945010643d42130107444103074140c03a4000c5840b80860740e84d04002e5120f541c42014140204035091000c41c600d0880d2a0f840c910010300100127080403070072001e000003081c3c0100301c00340c92000219006860160401c030411513602c0b07800628101e00d4580705141c01c10b65035074400c0c6d061200d1001410124030000d402e5031642c0c441d118481c0e884040b083c01e55400b6252941080480900d0181c01040080d0f03c401403026407000804075000420b6040130407070343c405149502000c4c0b407400030780f0900001c802907006500203000302808503064288080080c02c100c0151001d1031b00c4200080c0001c02c00103610045a221301c01e26024142442c5036440301d0015108254a0402507000000000d00742e038003810407541c0803e203c0e21002d45507601c0f1645603008007485660301c8041020100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 927005917 1250 927004667 927004681
    0x120c2d040c120218090127050412050307090902040f0303020d08010b16060f14040b0702060f3d05030c040603110f22090201142a030d0908070b 63
    0x1011555941c5035070b0a0311030b081c0c10640354025040f403001d40e43e010040240350081c3e50350709000d26018203590006207020940c07512114080340004003080c1c034614103010801011900141c440d280d41c5446081c400d03502d42da00c5008850080301c0d0340100070040d2000c07401088000c030301d4912030240c138443c0c0c0864005001d03842003507a061009220740d80a00720200011f41d04107041042070300740703144180c1c00030540700c80d0201d0502c151454803a6014000c3d011804010500c042802c2258000c002d50014000ea03007000322031800d280d040100007500610585580140001c0c2110f0710b0010040c00255149110343c0008403210a00d0151103244d01c00d200d01c43c4601c0d42d6241c00c0c030811003281d9101094080c080158410b10030143c5c2c9000c0b40c02c0d0b1121601200c04591400b41c0b00b4526030380c000c100d002490040c00d00c000b5190100000780f041e440034042c40b88400302c03072010300d1300c041007210350040b002c0386d484201c2114650b10401e00c10780d007030303a0030220900208040c0c0c0c40501002445205524041d0791119 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 927007167 1250 927005917 927005921
    0x903120d1b170a020a09090608240708010b070c05041a01030510052b02090a0b04050708040b0711160e101208250204051f0501031a120c2d04 62
    0x480c1c02c040490601264801400e5030017454028424204103c2c00b990300c03010380381182c0441e4002902500448400c0c01b2945900c0250603003031800340b11f9144a4188074030b004090403014020760b10b0100000551000340300180181d01d0040c40014003d00283c880020710300300314030840c4e02c0d0034007190411000c60300101c2d40c0c0340260195a0302800c403005180140000758100b14030215228003c546a002442c0541c40c0c140c0d5451040c1d0040781c010a076502901c00b07020440d040100300100700070f1a241844009541580c010703800c644180741c14004420022606414104c000b4220100d0250070840065040c0742080b099110380080103100c1c0b2060b540f801c01c4824621300c07c07401014803104120032040c0342400c0f0920800d0910240c1c160b056001140c4c04a411034078141d0701d00d402034054005840100240d40d1081001d42428a0103020b00d186140d043c41c0d41c10004811648205540201c102c0101b0b410840c5a4000400510140700a0403101520036010490040c0c0700c8600099400282c10f41054 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 927008417 1250 927007167 927007187
    0xe120414010c0221060405101808070c0f080a050c030a0209010515192007030b0c0a110303150307061701151e08011d011a0903120d1b 59
    0x61046114840360004642280005604a9100304022454141041c0208010081520400c010052410181041c603e440038140d1400b00f010b00b000940701d103807400d080c07503c044994401700007510381060307141a400208690300900810941c04200150590002a141101a00400c01d07107081c500d00406140d1139a0103004c0103500104450010011820003401c4280343d035602c00e007502d04081d56044a400420309840c0000005840c03181d0600e104108055010032070b004200003404c2c1d00e45940d882c1c0001d103100038010314201c0f00c00305010340d0b4640145c283c2c000c42944032054030703600c1c17414441041c0d1490701421610b019108030b140206500b40202009a112008040040d41c0c0c3c3c1e107001040d0b1405802d54210208001819400000309030b82c9625000850200307460302d4050f0760400e61403101213003800886a00c0c107100c0c0d8004200c4402e280b00303821414180700352100c1da90000c035008030340340030224800e60144200010340c15214410551250208149512041841c0002c490040f1100041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 927009667 1250 927008417 927008429
    0x180405070506130e0c0a080a290414040c080c0108070e060a1b150506030d12050a15080d08160807082e0e1605030c03061c03030e1204 59
    0x2024a0601403860140043c1180c15110420400042d440e400d4138603070541e050b40c46100519010032502c02d03258020049a911000200c0c040000f09c91500d4040f419030000811092098080760b420001511544c0009403000001084101e1a0605182100407048213101e2404140507881c005819503205401c03031806a8203c0da20015561031250420825a010450480c1485524050205440141c10500551500694580e51131411010035607055480080241e8801c0e0040700c7c4880b40541c010328090300ca103801803c0064950381c0e03040031800924030864403038280c0032b440702c002643d000c00041208400c80716035204801a240c0c06d0b0108418000102508080303006000001e031158030a2040b560701035040d5880342924841d515800311503403100480711840b11a040310a01080d08000b101c690410701c003682041080015800c01400c5020103083c090544400001143d455924070b4401003d0003080041507842045a180240061820175000780190180340080c00c40c20106000356421108 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 927010917 1250 927009667 927009673
    0xb040b0c01060b03070206010618050d0609050705190e19061205190305040902031b0a0906090b040302101202071b030b0709180f110c2b021e031c0506180405 69
    0x42001410782b8045a0410001c00b2a58105400511543c3e00c880292800d80180703800942d910305400c00500b4001207070000742c0203410681101c404401004103040c12211440141007083c3c48080862078024805203001610b070b420010003040c14000d2a076601150352150040b0380004409140385052140440805000f0440900013003100700100e40086600c003030300e240c20080172548884c14888680050040c0c4d0000f404684040c00103e070404007131406400041062400c2c949154000342070341e000140b0704030410140b5105030b81c02e143c968041d84c0101c4d900071f0444140b4603444031130010100c507910048da400c0341d6105c0461103180c000c0313803034000340c40800c000c80034100c25442001011b0a0b1040301c50740c006075100300d00329455400f0710180c00603203242005000b01503041c400c4d00c08408901818101c0305502c0c000c032807004da43c000032130321660396086031558190f502e02070185085000f59105214289003000d01030380c0c0d90800394419441558201c646002e03101c00e1540f0f01c4115001107400500541c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 927012167 1250 927010917 927010919
    0x120c0a1a010518250c0f11040e0f06040615150305150904050a02060f04050d0b0702011b05070b13060203041b091103010b2a070e070c0203061303090b040b0c01060b0307020601 77
    0x190001c000c0c00c80038981c02d20b4022040d440c0d582c84050111b4001c250750b0481c400e2070900c1c0d149024000e002218085400400204015071195510f458015000070500d5070f513103003074040070340c101d0803018000c00e142c11300386448980d0400090064241224442490346001080381d03090b24000c0d004034000c54220004200d00000750f0b080c441c860307000c988400d8000805000008003a40d540448011042c41040c0d4242d050a0190010b030a44820450000c0101c107108140c00d140d940c01400c1d11220380e080300b00c1100381d0710b84020320608900390130740c0074080a0001082200348250a1103e148486c182815035180e81c1d594081c64007190f0710304841c0440380c0380410040001e02c1c055000340c0300780056842e03038240041c900358070724901c02c0e812025038005403c040f90800c4240c0c180701943d9400341040c109894402c181e0360010380c4441c1e0081140d2001d070550621081803500c21213100c400707000f0180001f540c85403140c218144640214428600640c20440c000c0303040b0b19031000740c074042c0c00b00e50028442d0b6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 927013417 1250 927012167 927012211
    0x5150a031515030c140a05040302100825050403060c0528050403060209040b0d0b0103050c01030216081605030301120c170717190803150909120c0a1a010518 69
    0xe0704c120340c0c2010401003c0d5003600d0001e184440100000750294462513076603403440c81070221084140075001c061004510400c000103890003842d0107040541001c0c420300c01c070104020750740c40c01507400141001d8541045104480d4100c001458980489480e0380d61200c01d8902400003d01c4070380c02d90000910a0200b000001e042e50040d142183e0000d00200c0c806c0d0919000c10040b0031102000e882c1e640b044e80c0100140a420301200040107000e2030190701e04440c00403240c181c0246810b00501c000c4000461904000d00e481a0a0303907594000e003901c1da00d59560b0001e540340c0d40e005400792591130b58030b400040c5800254a4810b018a807a07805421020303d0246150060201009841e545000d142d140051500052808440c07440c414544552641031123030801e4404510040e0803800740c02070105002032071200003030310031000390b405a249964451074000b807414040303e50801402500e80d03400b07108802d91105000d90680720141c8107030140403c2100305800001042c1c0e010982035013101c82c84410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 927014667 1250 927013417 927013421
    0xf01120b01090e040501020a0f02030304081903140103060c120510030b06181f05010215160e030601030506010e0705030403081614160c0605040503100e010605150a03151503 76
    0x4105040100b8030964506419030324040444003202c099600144440da01c1e60000c54404d428a10b5200850541c607007a56014580e05c0360301c665262502c078003600c080ea594802c2c0c010084d6800d0700100480340d543d40e80340c02c3c40941034403860600480c044611100895510b482454861143c88441c614014916144c00302e06100c00340031701390421a8590200f520080c07208109019184e82e010301c5480d620300380e58920300b40c521600201d0454100e05044c0c040e44c075403100f9660b000313403030600e80c40340d0622400c4042e60107004148019416000795070002090100c041040c50483c2d01d5013501c0100c0c3d9544140c1120144003c4900802203603100020a003c0800d0022043d807407001810081c601d10340c0740c00080d4031078110403844684015100b800e1030030020080f1301080102400e00309241054145000079445840921018600c107030741d00e0152407015403d401140c020b020213800d1014004102c10180c403268091201040480d0074070f01c032072140c82d0302c0e401d40c801103420828810380000c160410442c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 927015917 1250 927014667 927014681
    0x1b060705010e0d02070e010f03030804060b010519050306090604180609020607021230090103020d0209041b0801120c060509010903120207051207080d0c050a0f060f0b0f0112 76
    0x800e5940c401400120030b00802c100001010039030000c00d0028030b445200c4a4a0905810120550307100220400010307030003a07211030304140e2180010030800c11150040b0b50741d0191a6078812580940552508a103030007600440c060502941d0110a9540d64000c0c030040e51400b408101c0421000c2c008a00483e486a00a08000303100030702e03a03482c000701c640004145007060000405030f5000fa00e82161101f160030f90543d00d01c40c201d030340000140c4110000100c1d0f401200122410b05400003981c0c0c602c40800c0ccd04450000710b004104019104015044001c1a444c9041010100781030700d00110301d6110b280c01048286600101030480305003481012079182d0004040b09040c0101d50300003000041003049490342180c00c5a0042c45245d02d00004c01081c050300200940c4690401c40c024418407001040000070600700382040e198441c3d5600c1c1c55031400101941c0039080403d62a19101003144903084083c02903000b41003400103940c0b03e402c00c40e120214885c840d001c1402d0340d26007081d2038410b802c448 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 927017167 1250 927015917 927015923
    0x906080c01211104230a06031e05090c03120702060328050c0c16050a0636060909020309070303030b0d02030109080304030f111207060f0903020d0305091b0607 70
    0x2100c034085240040301036660300d00f11441e6460000c00d00340400c10742844200343e440960100c002000494901241640c24540076a07010940c40300000b140d0607045407420b0626180050382080140b074400001d98a40b00040d004600c28000c0d01c510007210380b080790070365200b550014141d03803071a00d4607200c0c0c10700c8100c540c541100d800c10311600d00c00d404c0b0729481110301c04e40c40c141c2e84680d500f49805400d81040c1c5054610b03140c01d035058405100a80f9111110402d40f40c040c00c0c00342e5240d8180a04c0c0300b5003c0d0b4240d500c0c0d82c2c03030741040761100f0030800003a110b000c0784c11310b0b10360f0654241c0314203150f0103038002228000c0151f44000c104002081c0700e074001e1840d00b880580006046185034010030f0179100d40d01c40a50341c0d10b00c000140700c01c040c0d1104010007200900c0c03500c0c00060751400e110395100c1c920705c1840c044000c40031819500b484950340c80500450b0800c3c1081000c07180747d24010303450300074440034480481d01e4900024142c210114000e20000050b12440c5098640c1e83c040001a03000b000e016 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 927018417 1250 927017167 927017207
    0x90c06181806030210020f07050d081b011103040507261f0e0723060307020a0b1f060f020115080d0c050309031911040b1e0f060d090308010906080c01 66
    0x4056200d14108040703a406071b501030599840a040300c0e6180105c55442107010702c0040e103402002c54a6441a40d2075602c07044000b61307000131707045555405003c03c4540c451400038004188420410006035020440e41100c464031079501c0c007100786880f04220342d020304003941c009001110038440d252064644400d20220002183c0703510405580c03034440c2c590071050491500e10111400a45214000704600c4021070f2214074500d00480300030b4a034018988010012600319012801050f044040c44e0611083d0181413000c1c2d66072a2002000d0741c0615900c2d01c0554a02400c00c061881e03460000d000741c83c2c400c0001c2006c8002200111051034007003400f65000d00090000b000603550607c2100641d142c0680d120103031a0050404101140b5600c4400d480785150102c1d1082c90340b151010300c0005250303848042c2074010307032401013961182040500765101e00d00260b6101d5283c81c1e80e111400f04c90095845203100c0c1c2e2518400b0007220143c4c020840302d0f6102c2c034214051076200e0f040328010030183d4030700c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 927019667 1250 927018417 927018419
    0xb06041d0f1f0521030307090609140a060f0c0f3815120f030c150906010b030c090907030c021005090c06071b0b07120c021e040e10090c06181806 64
    0x405017960001e03199800081d2007200304000c943d5000380080003a02980f9030408030909810001800341005200751010710140180d0005c040340180e4040c1c01c1540c00c4900f40031012004e2511144581c0c513011500d106e0007820445003c5038640e0018403500440041008450352201c003003001c24410350b201d9203039210000b40c020240d403140502c0307007507111109a0b0045848652018146041c410041448020b02c0c044504000f0752030000550141158140030a995072511824466441032103002ca005402480710000c0c48000c5a00d0391000503072044507400c2d220180e40d107804410642d80c4c05d80b0300d00072075444440c0b14144c92078480c008008140c414856070400009007108503181001640c403c49040002103010414071a4090302402c42008030303d4490091440c990004000604240100d60040d80c011200c01d01500c4951000114120000482d90751390f503182c5040c00171f4900e0301c038211a0300c00b503031234006141c6014503084403900344002e8a40b10740c00e043c0080d468101c90b4085900e0202d0381c0701c001c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 927020917 1250 927019667 927019729
    0x260d030b040e0f0d1106041e080d0c0903030e0d0503090f0a0e130303060e060303071407180b0423041b0b0c0607020706021f0b06041d0f1f05 62
    0xc00f0405004403e0301a11107044000005854141220711003500d035008401008001440340040922000540c22042280c1d078850401c1950360242c06445c0100d20300c0c02d9502c91500d90402e200c0c0040700c0c407030380e1058010301451040c01400814400014100d42c002c1c8100a401d15010f01c0c110090301d000340c00071607500e6503107001c0e011504054402131501140b14030903030181340e414080c400181100701d0120809090110110b5900d10584001601800341c8503942403244405104144c020102091003200310000c001010004042e410b0046229615241c0000d8210050348007042002c0040450061190303116140c1141e03400015031604044401014003081c0c40c0b4265010f0100200224002c14186ca040100030340740900c01d4111a081d0350100d030b00e0850101c00803010041c50650b08401084840402c2c02041d0180907540014000307500845055480d00da680408520907510440307643c403036403120103030203110300808000056041c443c6c1205204a0030300c24a001c0c10000088004545070002c1c43c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 927022167 1250 927020917 927020923
    0x80c061b01060308071a1006082502071809030207170708060f0601020d1e050723030703090e070c020607080d0c030b010201060503030c03031609120507260d030b040e 73
    0xe0801c641c0c000c00440c5e03c90500181d0b01405c0303e0039120030301c000040d04010365040034a140c5c0b8860320042040c0031002444090303a41c0d80003403610400001e40d00f01807a0501010b07441d580c580c09820910410040d00000c0d00081d401140b50f400d070507401420845040000c03c03422408400e0844200e88600d80002406107001c00400d445030744211039141a50400c07400081c2001103c0581c0000c1085601c031040c950b00c080070f98050900710605101d07640b105a880e004800d0114950000700c94043c00c4910801d4110100c01045141c0c825a0f603511440c3d15007004003407007401a40c9210001d000007803501c005003040402008868000d00c8081c4c03c01d00d10240c6c00303003980d035241c1320750002035180c40001c440b9580900507480035101c214081d42c281544a402c0301e64a000040c0011940031041c3d8510711064082d40c0e00c503020301170369107855000c0d800e91b00707141c0e41c0c5041c90b200e421800394202100040a00300080600c000100d01e170060100c0da003102100720040d0034050500c551045d910050031264501c10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 927023417 1250 927022167 927022169
    0xa03050712020f0904150b030705030114090f03160f0201050c1905061003020105070605060109030804030602040e0705210402010513090516020a0804120c090626010204080c061b0106 80
    0x101140607110701403050040305002d41d020180140d0f00d64061000045031641c0b00e440015400f2400159590f048002a25120290344826019481c1c045079040f00c1026241c0e81c0d20811701c440403a800c07e104440b01070780e030f44958406200102020300c04800003422084000c201c4034014513040d400d0800d01301096041040c40c1c02d03c894122094580202008418010a9030001500d0101054545141c0002e800341c03007054001014140e42e94000f03042c036801255040003943d040300c402038a0305e4480c82c0c540020350040c000c0801a03001c071400264542e103e58100da100417030030741e0030301c000c044007007101440351300003900072030511070305002000d8007a14900c80302000304424a00440c1c1810148039509810b4098000c01e42103403c040034070b5000c03510326400c0714102c860406007070000d8071440c2000e9411902c1a00320221207410554002540794003c80300401d91015094607515607040c0030300c0b040c206d00c02c512039448070703401c1450441e01c0c81c54a0409800030b6130001d451100c00c2070140f100740c0d08640503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 927024667 1250 927023417 927023429
    0x50d0947070c0e090a020114120c03100f05010e0d0302010e06090714040902010801330c0b150306010b0d02070f03020d180503120a0c0f060e121c0b0a030507 69
    0x200700341e414028988052070061951040700501410290101c94580405010107418400c08259002400c000d200803284031000000c0b4904150501d02880ea510340d00a42d427160001a03a070801140000301241242c04a60b0140c541000e4840c0706000d00418141c7c0c0302c01541955a66000301d00c2c10181070002a104060b44400342c0400c60402c2c415441c4001402ca0f0a8010b074503200000c00140d03045008241514405c2101004c0b01420203803260301c1017103061201011041c0d1035144000300380c00c1004c4094041c8110f00803100c60765080150014521603020340366060703100f5030040204041907401880011154600503107400410349841c8494030200c3d030101c005074002d4806a07107959001642d103120151102601802614002c0003070390355104030444400e4100b00041001d01240981617460005a008843c07040c00e4616042c00c00c018003020340650344c03e0194a0182d80d41c858942e04466940b10381900307d010300350740108442c0c01016140741c0250040c01000700400424020800360f001400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 927025917 1250 927024667 927024809
    0x40c02031b0705060f1605070608060a061d091305060c03040c3320060106120e0a1b0b030117160302061c020d090b04050d09 55
    0x70078908404038a0a45407a00101034212038428000d641d9042c0848117408441080c2d6a240d030481d40c00c1441c40c2d09548001062071154003400540300390412030036031040c2e00884504000340e40d941001d41d110340b02030710109107031a11200ea40b0050b14050541581080131441e10540c181e4580e6511407a10758141c81505e480180881040208500d510302d60300a44011810b03c900341c82c9082c450146600c0e00f1111994102c8401140300c450fa10604401d402c901c3d00300d804010f100e4030b034680039444800038002e6100146103500105080380c0d29026002e40d00a000d001800003a0460711082d8030340d07e210418450f805902c0c000021803001d034101544c0a402c00380c80700d14001e400811040d01c2c003024480303000c0d04441c1007007081003d43d5446081d9058112610145c0650301610154031b00244640f41020283c40d2070400c03500d080c840c410074610b200b60320502c216403e12004020544182c0101d200ba030120740c00c40c00e8180c0c0c0740501000303443c18003426003604103407079900882050078500011000a542d02 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 927027167 1250 927025917 927025927
    0x4020405150310050403120606051b07120611120c030a0612020a14040e010c030c020105130209160201021c050f06150306011803060f0b280320040c0203 67
    0x850244180c5810458200700c503101070305400080b030b031141d60b08100e0703c1a15075940001014940100f00c0303490100341420702003140a0b00c4900c003a00d141c00200301030030782e880c50003410005441c00264201c01e841c1c1c40325148405125039555480585141c0025648003034050241c2c00c44040304903660303030058004100c22034407841c1c800c1d02c0b0030403290300b907000b00c01610b407490445000d615541506410b44580c6c40a80b510b203001880400c020700b9a50003500d20381e610742500d14200c02d502d544041c06c680260380c000d000070313110200c90078090081c410003c0e600856040214510f40c5503030b90104100b0501e80005400d1400c00501103000303002e240201404c1c19250300400043c0241d40c42402d621003030840b4a9071040300844d1494455000051401d41402012004503135401e0a105086000310f91100c0c0500818100e210404d005d444464040c80c003d500189843c880c0003c620000010103002c0c0090900da2441d41e00d405122608851002c410100921440901034440d4051101d50348815001540d4031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 927028417 1250 927027167 927027169
    0xf0d1b0905100206010501081303030b090f0a0c0504140405040302120301080303010f0503062a0c01060b041a070f06090201050c162612090a0807060c1b0b0a030f1b080402 75
    0x1030031900c400701190404c50041c842a0380110203d030f0001a0329000360358005140ca0305500505098007001d074040910010040c41451070b81c109885454071480501c041e0300d1404058400d400b4601503c1148810484079a003d814140c0c00194003600900c100d51524841c009152072075402a0030812070f90700000014003840c00c403025030200408081d00204190320305840b0007144544102d42006600c0022201c0107821103100040d20300443c6a5002001a550b441c2540545548103106488404000706c1111a1400c001c0064640440e046241c04070026240c1e920f410060074454002c905000041c410b43c181a071080280034508600e00c50702200c8130b0f040088075500c40790404d10305604d40050710001d000c03150020a865403010500355455032280c54210021342083d1194120300130a2103107281c0024100d9004c10b9101ca918021401d40a1440c460380c6030f2140c0b00c3c064001c0074460b00c010011039043c20f1180e80000c9661030340490000da02004540f200103203002c200040000aaa207a0501080d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 927029667 1250 927028417 927028429
    0x30911040c1e02070e0f060d020909210c0f0c150901030213081f05101809021002150106080714090103061e1805040b040308090f0d0c0b1b0f0d1b0905 66
    0x6c04186a0701071120315000c0d0000d1075107440078000900403406040460f240d81810089604002c003480b019200d0451904801081600301e0607020141d841408810540e005000c03034010072118001d49056850307401c1042000c2d5030b5104012050403d5401c000062500c8170026101e0b002d0300041c0040e1014018100d50420020281d40b10703519940d01d00303400c1c440200360303004c0e8900c115900c401c0700003404020050310000820310454082d4000100200d8400003541c08182c1042892041e22045081d1340c0b24141110110f00459540002c259019005c0380c1c01d250a8001c0d0801e5001407502162130703600d07044001520b68468412a5138207824110a200d00041d103d040403510301c800c1010000c9161603183d0341e00e003c4002d0405001d100383e600108000c9002072004804a41e40c034001c55020f400c1480b8024500800c888065030310102040c0494502c1e204464072040d1840d9154140c2c0c1064038542995040707602c041040c5000301c1d41c0702110300c9036480b0b02403c0702160200c0d44858080900c1c000034048 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 927030917 1250 927029667 927029671
    0x101212031506050a0e06070209090106030c1203050d0509190602090f032803110115031416050f190803040330120e01020c06040210030911040c1e02070e 67
    0x3050000d41c41007405640e50107000c0c0c821190407442c0c003460f1601088041281441000b83c0070b50044801803c2040c81a415040b0504892060070701c0c0d1a404d44e9010400c81a00c1c0d28a002400104204508600e200c8540c01c5542c110300503009481200c40e0103030181d0340d07400d4800b03021215290003203102046403404003004c1e42e0001054000e480140c24000150748800e44802d908405241e060460905142c820391040d01030f525060001c00c589010308071069080241407004480003c1010340100c80424003040002d5240503102510316407500300401c01c40380910b044812900551101101d05100c140b45680c0c0303000b428130700040d43d621421810440c402c4108403104505009500443c0030f01111405a801c00b07550705031030143c1c842d82420900700c1c040c2c407021444003041d41c00030500e00b00e840004107003030b80124401c8400f0364000c0c08a040940684a0b21000580000d26030010f4041d42c2c1026041a8040f0b0ba580c50b0450000d80c14a425030342c0410f4441841e40140d0080c1c00c207100d50529094540d07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 927032167 1250 927030917 927030941
    0x1b090e0a0b071404030b0a1d161202030c22020a09050a080f19050703080f030f060f01090308160614010f0801060e0103060b01030b040f0207051002160b10121203 71
    0x1450f40240c140b6035071034482d502c002000c000d959000505134070550b500c802592280d90110a80e01041821459038031700300040c2d651440b0320356080011700f1a01484c0300c10801540500030340f43c0102440200200e48100205080c2200707040d4051100e8030300e0a1000380354140f040d40740d80041c541044248075076408550001180c9600c202d0308500c40c00c1d40060003c0c1210000301c000701151406290043c14080503600003064840049035915190300740002462141c91080c965005d03035603031078041055a4044108160118440100034404a00c100d00100401600325558000d1041d166581c142120760300040d150006100b01c005104010b1205540e20003403107840c00034000d55081c1040b06601400610005201503074401c0c485c1e01070790003174014a005181c0240704010b11800f00000401039800f200c400c4400380100c1c00c601009803624401c1d5040070071171440101400350543d8812511103c081c28480e02d501500c1800140d18146201904000e4130403200c41000c04c6904d50040c2c03da03180c010420f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 927033417 1250 927032167 927032177
    0x5040f020703031d0307200d06141632030108061b0703023a110c0301140103060509030d091a131101050d110403060b030d0215041b090e0a0b07 63
    0x140800b000003c02d54075082c2e08505442e0042c00c1c1c800031104c07c205040f1040340c00045400c10242840f01c19488003c3d256201403100c921a41c84410b1407655070b40e10b506000c0420324542079050000300002e040135180000169080c032843d6181c1c10b1003404e4100b41d0284629171b015001f0085003151213414034140c040c811000c0750400c0c40303070381d03000c1e4481c2002c5c40c80320341514000c0202c4002c40d90f1a4170340e402405c0441c010315000342e0010401403801e41c1c1092070030f8451045213200b005034141449004103405840c90690702c540d00710341d144c03005000c000d0154022484140409000e81c1c00c14818191500d00c1005042c00c00c80411465014810380200a40e02c0c2c1c1d001c040c243d00100316130b0020820405c0c02480c1141d03948150142a50041130020351000003140c01090100c100065a44540e0311b06c00110111914442e09103000c80c7e80e40311000d089a28410f00c6d1000c2030008081420184040302c0b44485040d40716162050b5000300c801440340d0408651111700342c0f20600100014003a0020704600e04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 927034667 1250 927033417 927033461
    0xe1315050319021c080901301515080a0207050c0303030a0b1c0201050d090c0801110403020a0e240102030906030a140105011b0201050c161815030c060c060605040f02070303 76
    0xc84405018054061381440072000040648645000700700e0090740d502841c2c042391001681c0a08010840039400180c0900c81010100c0e94000ca42043c00145c0c00d03585e00c10900c1c0d611a0101c501075041610308481c1845101040055650240050340c8a1140b0080c00100c0c00c501204002c5120a4260101a940e8110340ca820161b6846011941c07402600070300811407001500e40165500b0850344031076015480d0a8103510301c681b90301c0c001c0c42249d000316016903400f519243c20060761302003a280c10b010114081d9901086d010104022170b014a41401680c3c144000000841e80d2640210750000c1034590b41c4203083e81c0c15203500d0b40d00f409420280f8041001c104100f100052403121110080e0511a01150007030071540c0400040300031540708900702220950700e08240a081c41e04213004140c8505011084040d019403126a20490784c11107410000c0d00d18000041c0c40e0325580740c0d4240d840036101c1c01d001c00d071604c0e03e005042c0c5000010300c0043e0b4801c490300707008041300c610031204c80180300e41c40c034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 927035917 1250 927034667 927034673
    0x6010602060a06331808010f110a27090f022701050a030905030c07030b04020a090e1e1006080705010e06120c300a05070e1315050319021c 61
    0x1403207038603603042800c030700e8420380d40c0910644844103203845022445114042c041b604400c1074000480029025400340604051030020103098000c6c925030070001042e0480840e080780d401d11106607020020080c00d803506468034000000c0d103c03220100060300750001601c149020b64404104110025814618004525400001c0080c030030140030108144d1503645d880140b042c14800c44980110b04011111f656030b6902c3c1024107010101c4080e8819242c4060000d0b00500c5400b400a4200140c4050b020200c0391301c0d00c800a03484002d00c3c0700d20521450000d2019141e4500c182e8000c0d203404401008940d1400c2c00040c004161044014010a010310880182000030f150ba150420040300c03109444000e0901c0204200344006401c80c0b06014204003e40341c50092020036000f10b8811005200301da50f980c00a60380c4214590346660484039600301c600310ba0405500c826001e2807a041c407000c4c0c8640e00c20010740b0b810b10044888000c0c0c0303901c0c00e80a04601d02114503c070446072055001103400c480761 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 927037167 1250 927035917 927035969
    0xe0108090d0e01110102090d0c05040e0a0f120903020d0b0a051501020316081309290310050604110c03190807021e0c090c120f15010e1206010602060a06 67
    0x140424140066640611300d00d100c20b40503910344440c00740c24a41c40380d403941001d020a8a0354031425004e50300d422010384c410300d000310781d4a2505400240d41d8508100b290b84e21113403007039180c45010030440404804001030752480010240b25000b0161075041c0c0c28404000002c549019110548030b650217240500166004000c0e04c0b181112114100c85c4040c1c6030a1507520703803084403600e41c81c1200d080804140f000290740810218200c48407159030001e45041e403803c42c0081702a160f58564004d59001c0e08000b001c0e0000c43c3d000c20003410100707126244002c1c1c0602a04404503a5185401c086a0710401e0f0307040030103117060544545898021070611410180d02c030351820013142c2c02100e140a1407182030008104840c08900b018002c01c01e00c0c0b508540316615a00f0000f0000703800500e44000c96082d4401004442c0900c1e00701e10403481281c88500151843c4012803107c40e0030000d5a0000400c41100303120140c002c20044d006400709240c0a00c003d0200e4000d81c0040b00740e43c031103401d4407190000071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 927038417 1250 927037167 927037187
    0x70b060a05180a110c0a15021215040905010509010b03010b040c09150e060a0306030209070815061e16030818030f2206030b01030c0e1005090118060e0108090d 70
    0x2c003000069207a22080350064100920620b0500f20001900d10804000040b40114140030780d41c2014080060310a00303060344102100c1440542e01d540220380703007800c854884010150700401c00200443d25039566429144e044960081c035035507800714a010350600b07001e903401c140b008170780c00c008201300d1030406002e000c081c0c0503502c40740784007aa8241155001d80c0102501c404001d10941e1a8103104074001e01400e281e0000301d02a50101000c0389440b030040c1c05040c02900f003c0b40c11400b20b1265414040c50703070004039041e400c01e28503a0301b130142406102c000b0002c2000040000003641c10b14100036001150290036001100010300c00c0882c0c0003404019034400340c00c0b444c10703e50340303149484041140400051000600c108803010001d455034055102c40e404003001e8a041c4109c034810b200a03a00e1450b1201d10940000301808611030b449c0c8184000d0003403000505010b418000c85240070141032103550441c8001c15450340c0d14080307a40c0c006081310350101910000309200c016a02c4024540f16071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 927039667 1250 927038417 927038449
    0x230f010b0a17010f05121504030f1704060e160317090a180606030f0b030c2b0c0f0902070f030f0908010e0c0a0602010c050301060f0c0c0902070b060a05 67
    0x1080d4920598482d255030030400b00400c66600803941c50f50b0412080c0c02480c81340f94414030f91418115111400855850040401e40840e594290f481d502c003a6410100d00e40f09900300000c60316040e040c11101c4181c54000c2d8000e0000298a0214604451500380007003080c02803005298420000036005204003410500103299503902c0e501c0c1d2602241d038064683c3c00a603025410540c0400c80c02580703601410403103940c2e5a0071b10094448101807400c48034401c2c03207130f5019009040034410500300a1065242403003100d4000d0150511ba04243c0c00440b0340201c11611216010000c110001c041041c840252211000071490a2104e40c1c0d44007079036004070002420b014000712110002ca000310000402032040798001d00204000c108803a0321150310710b99241c0715100c0d9510100724071b8414402c481c803084031921001d01e542d080c26800e480e2084600000d108000d000a54400080caa440a40d401002200030258a500781850070815030342c0020022030181210340401c1000fa640d041d40c1040d4040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 927040917 1250 927039667 927039689
    0x306100e100e1c060b09061c0314040503030c0f0c0a0b0d0507090801050702010629031f0b0706050f18030f160c0806040c120c0e0a090501090501230f01 67
    0x41020200d46441c0050300c5042c01c03102083d629005000180c1c00c120342e010412240150a691460108060003140700381c803061b0340e45014154070009024568280d0b00e07042907080181040e41e2840000e06d141c0c4802d000d902c40d0b40040711024070107401002900e4040b901280d581821a05081d80850b8134061000740d904030940710404643c02074000c440381d40281078804001e1049107040d10000e8044c150500c1941540c0c1c89404c601c13401040d45081d01c240d4400d8400e401c1c1d14540391400018941c814a505003034081030342200000e283c440031001408024401c0d60302080a1520300c50300206610010031320504002c0c4d24460f550400004021190504214100d603030b00c60500c18541c042d4000d141000030114240e4100200300164002441d910031813184504945041e12201081040f010700e560090a0340072300c200500945980508999105c00541c10010b1f2100b019212036007920401407050703480342d641d092910081d82204054a14408003038083d2416410300141c0c030381c5041014072649144070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 927042167 1250 927040917 927040937
    0x1b061d0f060f120106090f0504061401230721030509070303050a032405040c050c0307062a0908060601030c050d05222a031a0a0e03040b0306100e10 65
    0x80e4000c2c050b2154420ba4030000111581c6590f80a04041c440b4011445d81404034000015640360500402050340c6002d01c81d85800035280006581100c0780100b10601219617030072103904e40302e4030703c040c0c01a18014007a4000c00004180d180e10781d44000c001c61020181031034108a108000000c8410071070341d052426903540c90038280100e0050000d1121603d5142ca80300e880158892403c185c01e00f0b50b00221002c20600d4903a00060303809100f11449000d86810500c400310101b03030258020550a4030020b000d4842d8481c80b034880c80c40032002c86c2300201145c14038406100023407003000351680c4220282400c10001101002c043c0c064082c0480d0b096141d510b4070700040307605004d446020240e03245100301048401c0145018503441c2c40c0c00b00380b03006820304640c03004801000038050b00101d0b500040603031031340d4210348251600c03040f0061405140d251180e01c1080701d80010070090006241f503034905500d03814418100120341c46180901e000b00031000d543c101d45591103080070b00700303e160342c10425402 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 927043417 1250 927042167 927042187
    0x3060f070908030f04090b04020a120c05041805090601060e060f0904060302062d091318050712030207290a110a081b1c0e010207031b061d0f06 63
    0x401c0280c109000900001c0f8564525124803005803040d01c1b030300102401204484401c2c04228060380402000040d0800584100c503611940016858029442c04601d0252113020421080c44050340041c40c1a5840c0204601c0c170301c0501c03030a03014000c02d1070500010682040001c050b40918003103564003000014402d005940c80e584140000d5a0103468140c50b1910b116400741e02c40c1260401403202e108019940b00c003d45c8a0341101e5840030000c000010302004e0307818620081003c060200f0a548203114184049003081182400400c0000e03c07100700d82c80d4600d0000d0070800c9a601ca404040021141d40c500b08c10141c1741c1a400c455050040d45d01e0700c901d017004440100402c0b400006e1402107030510028402c180340101807510740d20203941c404222401c0c1255484005064801e002c201d20194080b9181c800c40740d800780040144101d480081d01c98071010444818401104500565205c0c204045500440f054582e400604a550343d400620030100c1c0012070b030800356a118003000070b519819 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 927044667 1250 927043417 927043427
    0x703090203120d390c0c060f02010207140d02150f070305061f0509152d2a0606010c0c0b1606020a0819151701020c1212060f03060f07 59
    0x30000c0c501508200c20301d0311030040241c980c00007131024560502a40910585008102c04020f003648101e40135016440c0c070b28201c694120402807001155000c10000011811a00e81101c0c4480104040c00705104480e901900e400b1040114094410080b02040415540c4124099100703246040104103640c038107001524010703540d1810080e0107400d0300b103034070140d501002a1001850548014002e0310004001603264010303035441e0400140801d001d00e00d44140c0c482e40ca4061302d2111241d03820300288202540303485a00483e481c020002e4000440340d01c103c100862a04004c080c02d2a1010102507290008041204c1c003803140c80c440c0c0090f5144035801d000380ca080e103164103e1411921120481002810f822040e51074400105541c400d03400c0201035032044140780f404855540711400d02c0c10300000407401d55605900b425541c02e00080884070b100340310745c031200e81b041e400c00c540d203107121040d4100012000c4c1509000b00d16880c40c094040c0c070700048043d0461a40303005880c440d6035541d81250 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 927045917 1250 927044667 927044681
    0x3030902190603060605031314160e0406140606070605040f060e1b270c090a08030d060b0a0c141e071a090f012601030311060703090203120d 62
    0x904181d003007024100d8200407070004010369038955000d02289642c0c2804807410302060b901520100752102c1d2000000e02d07609481c5141f0b0581c82c0554981200c18008851a003865501c145807205025041000700306d81441050309402d03100341034026500744540850328a01070010018440e80d03881c408542400324820b00c0001d6207a10510502c03208402d14007450b01c606841e951254000e0b0030082c802c01c90720709542040b10000100b003151020340080281011044009885003403620410420020580ca0302c80040024000b810002d55413108446100030846100e54019150380a0078040030300b010794400d00145e00103421035001c0707282c0701103001c2032400e248080503603907100e05030782e01a49010880481e21303a04036401e0501c0b05001041500880a4511a04011991090903180c40c2202903000e64843d0b8006400e040a54520308900c40d003460f00928283c1041d4041040e60418425105040003d0f07139201205180c1481a03800a5000c02d40c1c03074042002c1268081008180a41c1003002070b40411 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 927047167 1250 927045917 927045919
    0xd0903020111010213030f0b13030203090103110c01020403060204180212070302180d06060501020d170c03040f14060402150a08040b1b03010b210c0f0706060b18090108070e1303030902 81
    0x2150385035887c0342600c0040f116160480380c11000d0400a2640c1c0f134080103440c0030703e40640141d07160445007001180105441100720102d80024041da01c200507091021340302861040900503502e6082c4116030b03940030818158000030900412101d0440c40c07503019a990081503a00b401f5031078445c48040329425100d00700341d5540000c0d0a145143c1400800c1d0009011a007080e020388407640300e03400c0c045890510031810705400c0d960500c0030820717000c0c0c890300641d4814054007800500c0d14855540206054000c4c0f4414486c0e8450b1007803005501d820000b4080a40c09601110701d09000f5080190040c0002040900580e2081e80019003040d050f07011801c01042c040d03011962036840b10f090301895009000d5040340e0040d43c409403240d980125811601800344650210b041c842504448515540960002c03034840303440315000100d80080e075000d400d141c00d02d1400001600c5007241840700e000c205901264403030b400741c841045107054100e48541c0000006044140c1a81c0c5820250042c0c41040002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 927048417 1250 927047167 927047197
    0x1e050f0c01151e210203030d0915150b071e03080f0609090c3610050d08190e0a03050d0f020d0c06090c030c0e09150f070c0f02060a200d09030201110102 67
    0x1423002c540d881d030144403540c0c4909005d10070540c0d282c550408030ac15141c0c5118401e00162000d204480482025003440c0d4031071000c80e411043e0801000d101001c0700340085010680801c1407042c02d4807016400355001d8015904150507180200c3c0d400d0f44c0d16100c001c124003902640b0407007600c0c0c10b03040d501011202d6016981d07012007416281c000c000f5420840f40007514501e111804103e40c5000c4110707000c0f864001842600700441a1055010000211071050500c07840029600554680b03c04407401140540050017003090365040250001088044500c03c6400030040b00e00c0035608807074030f403900a80010002940443c54944003513180c1e40c1d50005012070500b40d1001444180c95103010703204014603029510260407001400342c00c00400c5d84c44d14907003180140002c013114030413065082010300496403804504010340100b800c84d800f124802e400542d600c2c4031035201c0050010501e200c04041d1009001c004c0080100400c20b10413400003e0400010340b04504800800350143c1d100c00c0314804031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 927049667 1250 927048417 927048427
    0xd06090b07030e030901200f0f031b15060907090918020f0a051c0201020a08040f03031101090507060e030c150d0c0908070308030915011401030c050a1e050f0c01151e21020303 77
    0x4400c1d43c0b40c11541008001380345038421030850355400300e40c039500505080340c2d4800316110dc104128804400034850f0b020805401400200a696406481000c12403024003035030600c80c4e030050100403191030002c039010340c000880410007a290b00c04500c6251811005103080e004d42880102e061180701000541800b101060103c4e0483d2a6074800086034802d4440b88a80d0740c4aa0303446081e601c1e4443d01508a400070b403c1000b9040c0952440e91032072400405a0b14030440c0a070000314000801008584600008500c8c8405c40030240300b000300c080c90f10300344460702d10300e418a0300d640d4003024000144400400300115103400010400ba10000303808900f401d10300d60711400444200352203a00080d0019041482081c00b041c002e80440d910070b50640d40e10307201d015011821450350320100500c0b20410804004030544c0080080260518504001c004103100e00a910b0b05441d8090b076400c864034032401c0b250f8451301c0d0994004000f08544844000d02444500d035520311072600900c1d03c010f5014000050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 927050917 1250 927049667 927049693
    0x512161a1015020c2715090108160911130b0304051513020f0105040f090b0907111b0f090703090605090102030c0d05060d06090b07030e030901200f 65
    0xc005403241d4100203284610301c2d5240114000b01480044200141c1c0249160300d0850a0030388920500180c040d054540604861111034481c1400300c0c0c0200e154041c100c001c60b00c40c41e101414500400d0010000c1c41c003540c011075442c1d00c001c03c40c8a80341c0c031107035203821a003000030001c1c1c103a03400a42c250030608002c42e80e40840d21943d42c8112070482d550b000349900850140501100389000e00060640a00414404e60900c0442e10703120324038906000040c807000842e2151054050b0180103107041c0810700026407803e001c6101406002c182c1404403001c10801000000642001c210781103104e210745600c010004904194031400b009900505190100b0040a406420a8140b5441078000300040d58812040c14201e00046c1d80b410108482044243c5000ba0543c01c8586c0007030005000350800c419680e47d1401300d407100d0204480d00401c090410120642521502e1098481c0030003961900c2c01100000b0b0001483c001c107040341d0b0345950451642040d040081031000341c444070440d04c07090040070b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 927052167 1250 927050917 927050963
    0x12100506130305010513120c060e1c110102031b0d0b042c160b0d020c010504060b0108010824041e08130807030c06050a210204090b0d051216 62
    0x80000c3da599824400842c0b0440d44116003d03803a250008208804c840ba0340e0000c0b1345107511880152080c1c2d454078011030351004144024102c1501c242040d0706908820100506180b0280b40300100c00e074810f0040000c1802030b01d0029071a452a5041c072507031814906101c00042c01a0072040350058030346140c0441045a89010150003031403158051034003601403410542d28071000802c9407101ca50060200b140d6481e280243c0016001d08202504002e854502c2a01311241124103480044c0c03203121050555810031000780c003400460b40941040d80e880c0402e014880070000540d403a044c00c03200002c0c00c1c04144e2080001103400c1c3c0c0c4c41c075016443c040c10a4180707900408501251002c040e50001080100040d110003101c0d4004001c09200c0d11b802419a800d07086882e0207010312410f500703000508810b200300340c20f903140c0359813006888500b050a1002111084a1502e00520803100c0c50360100d540042c3d00c0004826202550341d40d42028809404492402140106000d0068102d445114005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 927053417 1250 927052167 927052169
    0x150d0203010f1212030e0304031b420e180f0709050f100c0206120403020606010f0e0d060f0e1b06090604030b06010203120103030e03010608121210050613 68
    0x214802d00d1101c1d01c0d0004410700b51007005008041c40155640e43c01e40f030b07001390403001d462002481500d08059907616a003089a022405454002240d00d2052107441c0c8494040b4181e840304001040111503540c0e5491000200c50b401d0198041ca0800d0b05441ca500c2903402d6200b400014020a4003c610210307007400408040c1c441a0204008400080204e441070010358111803005000481d41842d00f81801494501d0f008440108048a0319080158480c40010103145004402d011300c9480c0a0038000d0428070041e00e07050402c0a22101c03117500d282e005d1300c400031a440c2102d00006c07084152404800903c1c060708004d031040d040510030300610174007040b0207200c00c0161610890000c07401c410050903100351000da03940040240400d01c0401d440e00212944202c040c0116440c0c01625511750749509403d031310440c00290030b0b41d815659400c0c00c1c0036a6004044010003001d24040e207c04011081c0114181016041010800180029030b5014614028203028002e5603030368000d4071201001c0021 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 927054667 1250 927053417 927053429
    0x804081b030304200f0607020f0a0e0708130209010608091e0703031205060d0b0a0207051e1b0102100c02030d0c090f060504080606060706150602010c23030a0b150d020301 75
    0x44004510410040e13804503e58800010800440e440b0002c04102054105002c1640c001c2413425182d0403545079290414044c06800201c000d075807070a070350000c284060013840c0340303929885003000400507100c006d03685041d150a401d00700120740c1c8048800d4030349810b8241c510680c148011104100c41008100036013500d00179910b00207042c99001102c8103031002039a10a070000c1c40d00d0329000124000007582a0448103116000d480c007030142d01c40d81e00c0d01d104144004814aa10400c5c4001100100804046009d1402089006001c2c500002c1d40b50300c1d910b82d07450ba0890700d8441d031943c50761003841200c601002505c810031003d49131440041c440c406031b000340b580980c0818400708515000c1e005450440d2001c0c001000035a5a0109002d46a001030b07604603005d980381c4601101c41d0381810401c82c09444542d0000074041e110a100a0403407003901d81e012a540c1c00308910b0008034540c001200c0d8064104d00020604c041c210011450940c0c5100040c00400d2012904e072007921916001103048071a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 927055917 1250 927054667 927054683
    0x6030c1606150510020102040f14030a050a0c1508090a020112090b0406050a0c0810093c05130c090e210301060e060f090d021c03020c10030c08070804081b030304 71
    0x1d1300300260300700e100780d0040c2d40b003407100c44c0401c12102e01e00c40303071204042c003028040d9040b581047e5031320f40c039024503d80c1c112008224004203009860161449035031001052801c05003508183c10503a071204810030020341000705038940150a001c1d144c120b08003071503009005110034a05401d20b000188030543c4c030030352082e041c141400324141c811100903010303000c41c0c0b44020f2042e182803101e00c0240187c200f01840300f2000ca5413110703000c1d0750800340e0074608a070310880900b81402940740000c94000826501041d02d98506000200c0c86034507100c0d040c2ca10b2044c0005680d0246220745d4a8028030042d40d0980101080b403060710f516441d40a18104d60143d221800c1e07800707401042001c0c6c1d01a10781c070110508024040c1c40400c0c5018160b09031910f00107442170964030451312007031040900e541015400740e400101c00d4203850910402d4082d8400d9180303410008028148070003070100d01d0241c8010308000c03001d030110b024807084c04200e55200041c40d04114000240500f41616134000f21b078242d402d11 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 927057167 1250 927055917 927055939
    0x904051e1b0909120d14090a020a0f1a13030605040f050c03070312030213240e0d051c050c0601090c021c020601150c08070501020919030206030c16061505 68
    0x400c0407181c00c2c1c015144000a0840741003003802e02c0c0a0b5811403000d0b1894242c540700c0c2d116402d002c2c00c03400e500401f0a0310280002904e0380c0184100d01300c1643c000003044051820404c008807060202e41102c80312444080c2e03a5950882150010401540000d004107241106000400c170000b00186140c1c3d120302c2c103541900d240041015161203070342c840035200c400360020711100345200364002c0156400c2078001207031540d01d40c6003029070400003030803580c2030b03c405240c0f00e45080d41103490000140011650a05041081e61758141c9502c4140c1c09064528031400d0fa031030341c00740120262800b004e948402c40c0c1013582e40c0d204000150025015950260050107a505102c018130300420070307880101d070010300a40c3d1910003444d901d6190500c40c0300070442000e0480d0000b0f11014010400b882c0140005a1101400402c004ac0801381e11035494120741d80e50420001611000d042d03039807000014040d85d0301e842da90504101c0048040344010700c078a150044107400182d60700341c030304c060312700c2681c0e540c0c1e2503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 927058417 1250 927057167 927057169
    0x3120912030a0c060207051c030203090f01050c16020d0b0a02070b0a090209060f01050706050a05070f0f141809100305010b18010b210c0d1413020904051e1b 69
    0xb071090b10714110004440c4520301c800308086800600000f8800e108580e400b80b2501d61480c03540002c0500440081e03000810303c2580c0d0410051031007413600f403000800c00317400d00c0140b00b003882c401c2c48150402070790105010f40c1550380740802d0f1104a90400600d150901d810402c0c4c500a510007201183c0599000c0081104d42c0c8003407181170a0254007030300d071844d9502ca1a007044a07100c0d41282d04c604002c07003001104001000c2e80107450041101520100c0e29042503e009850305041400c01004c01080c4565200e0842c1e00c400001c1d040d09103200000da5842c00322000a070300343d070a1005c01e83c1003a00e01e000c0c4160801618040011203009000800000114034200481551b020390035100504500780140f10500c03420000f03041e6011065507a00c7c8082a580f480910180c1c21030303005002810200d0038030824440d900503244070340070b103001d0007003140b50401c90060740c100398401c06030061a00c100000c08026041284000003000c440c40c124180300b1034413801e030382c0303000302003041c4032452010140d4115 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 927059667 1250 927058417 927058423
    0x2070b0301050f090603070819020f0102030a0f080c21040b0c0f0a120b030601061701081f05061203040b0d1512030c03300e1501060509010e03120912 66
    0x59a100402d00802c4a91120030000582c03c050301051b13050064a200003101c4070100000c02400010307000b0511005901c0c0100881031f03403841c00aa0654200300701520b02183e200400125401d254285000903482e00c401a150324007a05100706d804a0404803a6040410351605182c0304503c526154034055440813b0500f05000319102e00e406e008042c413200c95014040c149241c855010490005820805040041d1038104c0070383c0800b01144507141d0350703440e04051011441c09040400020441c1a01d11047d80401100c5003245100895952000c1001641d560601c010303000103e1084039203d42e21003040d03020540c441984007600c0c5140200d03022140c075140301c0b1031085806540044100c01e443c1c0c0c8040d150001010800c500b00008256441c000148540f012191210b0400c9034541412002c0c44020031201c29405140583d40b22281588109030350700d0401c0d066031b403240b901c540c80b4101e400040c0c648800800071a90304d801802000d0350b030080040301030119603404a408515203100d144007551 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 927060917 1250 927059667 927059669
    0x106050408060a11040b0a030b1309020102060c07082703070312030b1801060c0f1407060f1e0f03090501020c1b010f020729191101060506090904171902070b0301 71
    0x46013a024081000210602ea0180450050500f00402c0c24000100000c40b42921145007000503035071081c8403015541c1c100500366014001528040c601505178586500310f0041505881110034545030403106400010f90f0381c0032481025040380c40d495240d240c1101c061142c9218200001d00d440d1619550303140266105a16021012408003d0707401c02100315103598100b0010340b10707011140000000101c402d0314040070010300700042d16115040107001466001000c490f00100031000d02c482414100c3c00c410350401c42c81a0412007500309806005501510415601800c0c80d48003285940607050f0118590043d004150346107d05080440010746440284040d02401a030000740280b080c202c0852301c448402440811403184800c071603034011195407041d00c07850f03c040315000109003243e42108101d20030503600c200a21500d4148008125180500100d4510030001307040032405210040203069840082c4401242d6034a10710030000d0071885003800c840c0010300c01c064000440700051400e4174 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 927062167 1250 927060917 927060941
    0xc0a05010c0b2e09060506182803050c09100e19090c141509030a110607050601080703030f020705010e06070c05100905040f050103080f031302090106050408060a 71
    0x241c200304503100d5a4404800a0415005204200824001d1202c8045800000305080c200f00d007014140749a1506480b0f00b907010030b01424051002440d030440710150340301c900d0400d0b950b2643d050428030800e00c40c00428410340d404869605000b0041c4003000c9040c0030000301c02d035940c0c880d54a40780d146000240151068100c40810200482c3d000e0318207420201d40d02096140119040d042c0f03442da14116003da0303200e0442081008001034440c00c090300300983d81911107841504000c82076010070b8071216580f50082013103ca540355000260341c0c042c10b5424907a0000125a00c6685500340c007551866903002c00c1e40491502d1200c00d03031142c80000c54505642042e943d1000918045050100c03680008008440e0041c40ea00042034a440e50030074050707442019500d03100000d10344400c1c00100c5000d040c80b280005d04000050000c03411801c02c6614420b0b2101416649179210b14401c0d540080f091402940300c0e46000002a900e039200014209941841d0300352440c68680d140d44804440f40fa098074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 927063417 1250 927062167 927062177
    0x2040602060c0309300a030c11010e03031302040e010207050d172a1210051305220c03080d0f0e340f080d022401091a03031303050c0a0501 61
    0xa58200034081d0b440d8007800440086017150310300b4850480054002c500c001000030303921403e01c1e0036240c0c00340c580170344000d01c88000c20038404041070b180d0f1a0b1000901050303076400550128002c540b2203903c140b00c1d6040b20b40086444a1803450101c0d02e4030260001507000414000c40c0700000c1d00141c20440c010208080403401c114074101c14528451240d12000c2501c07917050103d04a12485680c2c00b61140c520031078409a101d09107020810070b0381022018251188c138150030404405000001c18a00c048014600d0311100790500e031240f0b09141503040102100e1010840201d0200950030040341280b003a8424000d00844c400541e540c0c440c0c0341d81c00103249101c2199911008400d40c0c0c80d002040c0706a0071001003c3c0c03030300204040c4500960000300160312032225580c20301d03418040000308103e0901d0500c8401e0340c0348109400e940d81070003a10303000369440301300002c079074440c0d100c07222003900107019031b0b07213403a003000ca280c10000807480706139614080e0b4005414507140104c032a03001d590058542c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 927064667 1250 927063417 927063433
    0x203012f0c1b04020903010203070206011a070506060f190605071104050601022a0d080c0d050f0a0f0201060317030906060102061e04140a0b19022b090b010902040602060c0309 77
    0x1100c80121103a040103030700f0541c20055401e29450a00045119600300c0e0014141c0c0d51405000b040b180c04418540d0788081e4043c00001700055001c034220360440404c43c1d0784003036031065038000381074110840c0101c116082e8501d4000350319600310000c1c0807454014008c42200e0800a41400140c0c3c01c00c648860040e081459a80c1c143c1044400010030035500c41500580303a424800400e01c0040320710703015559181c01207950b044002c401c07c1f002c0403081151030600d05045440003100043c4c0a0b0341406820f100881c1105e031881e134400d500c07100c0155040721800c0042000e641018a0540c401d5520501d03a005050000e00b0300d50002400c41d004007000500c0118901c00907601240b450009001240e1044508107050310034501004294045400340342c0c6080d0b181014000b00c00460345600038050901d00510400700e048845513410f081c4801c402c8030640440c080c0c01c041600504601100034081000c04002107103030400c5902401c01d40e645502158002d2301c8101103200f1600085a0011181e070000d05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 927065917 1250 927064667 927064693
    0x910150c02091314060c12060315040f03021c090819120c02180f0708070201060303050a0503040809040905011508011103010b0a050c011a1e0d030e0307030203012f0c 73
    0x3d1228105001d10515001e904480c4d50850130010140c0d800400f00c80045610101007002402460308a00110002d22580351400d15503c1a10340080c0f010340200c000e070040d034003818000e201e502e0a0003d26404415058080f0710f001d01050007500036007000d440b44845d10ba5000e6003000440985903082400441c240c2001c0307800f101c2c8028500e00898000c41030041c00790104d42c0c2e68603214058103ca40c02064075140603100180f0340c3c000204072500316810070004001294008080710a12840c5261442d0743c1d0380c035420100742a02c5181c20087d005458020720000303000e019402030b0600481a601c5428160b0390b112150b00342c4004080c492003c1e00c04200400402c0003110081c01c58600e035007000d074240b0301c80500c00e40c00c440c000008481c401244100714078191925080e92100201086010f651610380718020510307014140000800388841080007086a98003008076000a55000b4020302c031000c9c444181e488040c1c01c04071540e200071344114024044002c107074196880c41440100404860f9402c1e5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 927067167 1250 927065917 927065941
    0xa0b0c03240f090109271a150d03080f071706040c090f09090c09020c061915062303060d0f0c091d07080c01050406110c0910150c0209 59
    0x1580d80880c5082028100f900c400c0b400c2c030300906505d0350014403400543c0340706620b0401c0042c680d01e0001d5500122001500c9a510745480c106035002c0c1c10b0311551203c610900c44000c4280c0715901c11171403e04202090780c0400d03c03921030310b503c225030318a545a05030156070304c8800c02078119002c40c640c00001c0050a00f64071101540180b440c140310401e03a503440ca800074401d141c100c5c114217a215a01350b001d00c40524011001845130a4085103080b100728401c50f00c0e2000584110416088511200701c501e5160b041031150008420b8010081e9aa503a4040d220425044040241001d4040090fa82d803500700d00352442100050105d044401d003ea07940104400b50f02d01c11100e00260500c0880e02000d1071040042c2464050b040c0d03400410407481003441d1220079401010558092420008243d0340003050701d08590450a0901080c1d4a007807500d81041c1c7e5000d6859007100d081c03030810400ba80d20038080c4048440c5691980304c9480c01d13540441b540d4440d1345010790441d07206404690085009 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 927068417 1250 927067167 927067231
    0x503030405250324060e090114130b090a0b07050901031410030b09070e01060c0312050105010915051603020105070f0507031e030f0c050c0d1e030e0f030c0a0b0c03 72
    0x40c038196400713990b080c91412510590404130454406c94204030048100744a8412401820140c03582107107040201d03010340d0904828003e14014002c3c0214144070340c05c0040c5c00040381c0c0104503c0c003528054100500c00d41109000c2c50009040610356500800320300b021500403e00d1a034011141d900310b80350072101e0030024107a0070f283d101e05100041c1d44600740f00002d0280900340c2e1400f16204850800400000408950449007482c0000410035603810030b05500c1207500400014040300c12001081d21a0700421700d12401c504040d26204080580c10740c8003912924443c2c41c2c03100345002040048a50380145140140410085200f9130126508680704200401c60b078a00403803030740c2103015001d054070000d00301e01011510114002c04451004e003c108900703813140c501010711000040009095101c81c0095000785070b0b0b103c1d002507080c40140010350b9001c03129811030756201014040541e444c0b007844400c1c2e403030203c04004210400d40781c2080381d0042c64002840700301812018510240f8a0301 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 927069667 1250 927068417 927068453
    0x80a03030c18031a071d120c0301050c03040c0e010303120b041e1b020d2309120715030902030309040e03090d05010501080105070905010f080703020f03010305030304052503 76
    0x750007000307207140412041040074503ca000311414540d11341036000d40007800944003c0910520291400300742c2c002204902816900310740441c42e00d00e0702580d09081c4185651056015401d00007040b10b900101c2008601592244502c0c40c4907a9503904181c140540030300000380011a02160494545200c1e00710007140080108001346682d1044c0d003494001c144a605550503a03141c034031416004005039105c1103103928600190012901c41000203004907603040c2c810001c0742d8002e003034203134000e100d506691107440054501c3c0c2d810300306c0c03580c00f41d51125148541c0f500e00d10012440040c3c00c3c800e000390080300351b025005600300000c82e000c000141210f4003602c00d6500c4144505041642c50b0b200100046001d00000680c55042003503050a440f0010b12110a0045125041050744d81c003a51543e07800308645803c2a1540351050b0803806031003032130001d0050503000b000100a0100104c000c5d406284600f041394500581d091510044081d0042a122030345040030302003000c5104020140b042c002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 927070917 1250 927069667 927069677
    0x130902040f060e0609010e0603072c012612041503270614040f03080a020d0c030209090f010f090e0a02091608180601060c06090b04030810090501080a03030c 69
    0x120341140c0780442c2c10540c08108940c50740803d0080c0f81c100601010301400b43c1030391040c254501000840d80c1c8840611440301d5842c02c03040c12404c4842c5144501011602000c0f481e6090b5035920407074981e01c109030000300c1507180c0c0c0c0b03103080344525400074584100401411089082503d06515208481aa80204003d02d9282c0344007200d8003042004449490000306600700102d41d15003041c2040315002c110081c031594075070007400301048100d541002e0700380c1c0c1850300040903510120010043d00503c86851221811310110000058048d0054501481d0941e46050550f88911101c5a020f1081c0b054601e41c800c1700c00e0034044030200785c20250b252003400e4112000ba0b201c42d03001c240008403c81e4040c09904a441040502c65441000a5040800d21001e403901e0081038150300c5d01c600e07041c468101404120303041c800400070180c02810000707800c00d11881803813516040140490b1070484803140018100301c40800c1481541c8210b50599002d000202041805641c0c150300603c43c64500c101448 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 927072167 1250 927070917 927070931
    0x6011119080310090c121d060c03090c040b15090117010b031b1305040e030714070608091513031202070b06010336021507050a0510270303020408011a0312030613090204 74
    0x11030304002e8140550a422270890ba00e1806a00785400c00d2a01e07030f2107511441c2400e402003803994400208410181c40b50480f030b1360f1944003c00507a442214080405000b404e41800000c8a0040002461040001c006400000c0d00c510798140c0341e034401c101b280d81d140070b031a09051029082540c4000403229000703048a24050941c1c4079200301d010903600c0c403a865403000c1405d001960b444044c030390b0083c0e2080c1c003c144501404480480510b4010700c982403400b0110464414144101e64100c50007600780340c115580c0340135040040900714102c500718086820640c201c0210312010040c1ca03000042c545003105d00c103042800760049104115010b0780c1c080700d03218546144010a1000b8004148118001d010032036107864504d0804501440294501c1d00c0c118035148287d111980034403203a07a221604262080c90b41c0b909400070b01943e0008196586041000310010451415200c074900701103003119a60f03541c5034100945840122950340d0071411103c12150802d10070b412030844c6034401000801c8074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 927073417 1250 927072167 927072221
    0x50c0903030f04030c06090513090804091118030610060819020c03031012020d02010509011404140f100207050d031b0b04030e0d0302030306011119080310090c12 71
    0x40d003210a0709080007000003010010050000002e000178642410145c2487d80fa210000c4e00540300c0c0c0008458668079000c100007001055000c482c0900000c05007000300d4441e203003104455420550402d00340c0213000e00514898980004c2e92441852034552228146090040444600d41e010f010794900310805446000b0368091800a00341c0301400000842d12840d0880100400c0b90f025440100503204080440c170150f22400b0400042d00d0302801c000d56101c1d451070040f01c0c01404034044590b201000700740811034001a1410440d000c2088030080c020810700b004210803c580081d440740075030310180c8208002c0c14980060000399000f800c202d11409030040c001328a054407a40100d038070101010401c800c240d004100c00030462010303102d1540c440c50980e8082c0d9a444003074221414403498421071207428502b04050034909401d24100d200306c10041c40c00040d1074000780d4101f144420041c00219001c8080d00c1000201c00e41540c5105469013018046001009000954911036401c5040b130101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 927074667 1250 927073417 927073423
    0x160315090f050f0a12030e030a05070203030d050a1d16060f18060f080a090b1b07050307080408010509150f070512150f120703080d0603050607030b0103050f06030d03050c0903 77
    0x140703d1980013420b088074a0740761460014a005e0005002e05103000080749040c0c07000810b90b42c90271014240a40d40d01031a000092070b50040035034403489603080008210070b207045500315400040c0142d00f400c40c03581103026066110001107070403560960710b800d82048450700c14800c0d894459020305101c420001c43d01c1c1c480090800a400075000724801110011140d0740c032007950b980c0481c4942c0c1c20045500c913581c49401164015100b82600d0300e28030041041c1c0102d000c00c94070a10751180480342e07074207900d00e071030740d031540140c03007000030a5291a000030703401c0c040820102002508020758011a82e9066a01c41c8510b1001c1c1400040040c280300d4000c0440c98a00c0340c0d030160711032459420b601d6175036104118450b040d8000c03040c000c041c640a5408054400550801520780c04009141c5034403900c1540c4001b043e0726400a00340d0303c40c0a0600c90345942690090201045c207076001e0100342c0e02c444100040d40c009544050b090f9101048102410b03100b1361002e504010007002c014a00418480043e107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 927075917 1250 927074667 927074683
    0xf0304030203040503061303052209060603140f040b01030303020a03092f1017090a0c0e0a05010e010302010f0507031206171b090c2b05040203160315090f05 69
    0x50b9000280a0045140070083d0301d81c0031207d240042003541c00c0b917600034800c2c0143c0003030690941c01d0814061709000d07802c042c080644040001009550303507404005001c0d00c0426411225280140003090c0b41e14858070509100d60381003024a60769074a543d404400030761101058000300f585c0c4684100000d09482400c07549000480c40d980051419190900c0c0d0340080d0b04503807803040101d02c2156810b507030050314204d98200c5160151025640b01c0903424103002c1003e10040819040710700200314500f0b4002c103140a000611000c2020f0f0780c84003800d101094081c000030340800c4404442800c064840d000600c002d500c2481e01890984d80d5006aa00713941c8c043e00301c0103a0b5030b10245296285502000340c0b640c02e15003085201c040030351803000b0840c913a0340601a40c44850000918805141c8900c0f080000200301414840c56842540700070301c020802901d04900c40e0080007402000c0e0b442d0140340710180c91300007041c5540b84038120082401031164070011561342e031201180c0800302d042844103603 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 927077167 1250 927075917 927075923
    0x172a030405190c090f0e0c120703080307081602030406020309060a050d06081c05074209061404120809010b0d05010b01020114070c0b040311011a03121602150f0304 72
    0x8241d142425a042d064a0455a40505d80c1d4a0002c5a8034200d1703001450605509041d07a604613003184401d0340c01d040c81750341e0308054020b46000040c0400144c1c0a8000340c45075464802e0703904441d000f41da0803a00c030b00c05c610500b00140c2c81401540c4151078a03100502e9964040d040030392a08510b4440391090365000e0b031241c0074135008800d019180070708044800054a03500c0c07501c00e281c1070055651880740d44405500c034002e81d600e403c040c40c001000d140800c0e0b000101c0300c1c0089003a8800052880984007041c41251b103142404038950308050002e0001e030085622100328100c4e108040300c221030501000303000300c09030340d01e450201c1c2090300c6844000203042d00941c004981000c43e04000f80c2548c41031034484141d01a20f0040008240d40a10f03030503a0f00340d00c100e80303a001d41c4850030308413090705e905488a1315039484c0500c5504d114a41113092001c0f00703015015a042c054035a0300c8015180152038056011041300051207005240200350107080180070000e1506000c420903c42c05e03103410440e030403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 927078417 1250 927077167 927077183
    0xa020a09030204090b09070b091503071b0c031211030315030106170c0414040b04030c0206070b09160e131403070f0c170c060901050702041b172a03040519 68
    0x41b10720b1a0701031000901030442402da2a02d400c034071002241401d04007203a10034801d6130100100d02c0d0f80348924440c0e103040210810351408103101e0305284030001180d00c000c4410b0300031541042c0c0501d001703420b9414910301c0003020b1411a0b81e9500c1411481002d01402a455541d030540407903d80341d00c000003400ea0381000001d11b41e0154100c2803108507441d40300d000c0b640d640c0301d601700710008912103581c0350300580c1841c004c0035240552020404a01410300028001d985840400460910000702c10001890900e1648480744c1e5800f5056070f40c0405580c90f14406a80101c81c00c04203c000b0705881d59156900704403860441d0070385482602c190ac070f05046403d4120088208040440b1b11688150346200f180130f446040000c2e80021850321070903684605004000c0740d40720541d03403554440c00d03101116045010018803a840014841b40c0710f9404a654410f02401003032400d14102c42c206c14041144010303490210040440384020f4200030f204692a1160516502e42d44021000c9007a42511980c10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 927079667 1250 927078417 927078421
    0x3010c05040501120b0906131104090912090e0106050c1002130f1505160218010b030604061406030402280b090103050c070b010e07030603050f0607091d0a020a09030204090b 76
    0x501c41c0c9030184e1128050342c100307040c1540c240da6501c1c207241c10a17401c40300c0e502031100b000a00b50140c800a96554a042c0f400b040005601405800c855180d038403403a60400e03903203a104000d6445075913901030701d81900402e00041c014240034100a1500440c40d00c2210101003a80c070170f40003070342d00030450310001400a8104110300c100969102d0050020702040c6003440402601c020b1170360007181c6401c0500c0246461740340542d02d0741282d0300c04220303180c0030081c45580c50304041c242660080e1501c074042c034a1300c400007030f151080b1140340003502e10081001e440e6840c2c0703400f0011003d06d0340c0610300c681c0c807404810280c0911414204030042441128081c0c8800c00320f80054100c5000400ad80b480301400c00c007034800900840d0070396055480d8440130305c0694a81035821401002c26400003815486074190036031005c00001004c07031040c0c0f55035648003005c6866060503442c1403885c20a4509030409000810b01e2800ca60700039040c2d1008030b20340040c2141c0e03a500041c090340c14501d02035401c0c5038400f003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 927080917 1250 927079667 927079669
    0x6020c01140105150a05031005030a05012025020604121412090609042007080720090408030a1b0c050c1c02040e070b0403050312070f0c021e03010c050405 68
    0x10220b801010116000e882c0200741d5403801da064400c0181c824100040003001a105040302c050040107444081d003120181340e0189442802004d0030a141040741610b000b9445024071007200701d800c2c9010b168140e8103140d90640b02e030300060100d05422a404001880301041c402501010b00c030141c0d0040201042101d120f031521404e02542e01450103203804200141a0140c680c00110b80305850182e4000408001c4514028088250705865840e1040b001074200240514032000d0541940251404100b0481d403000c00004490f40880c2250800360074000030b0041170304900950b038841c10840021980483c096840e01c581c080d069440404501c985046600b8440104401c1c1d00940c030a031542c0030007109415800001d1101c00c0b8000344500d44642e55410524000d000c1c040042c803040a410344c4030b680328075040e270f12a0050414a0128050407000940c41032007104030140b5040b031511110000190b603000e0103030071015883c3c2010541141d898101e0301d902c091003200f5040781f040d51071b9600c07103007040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 927082167 1250 927080917 927080951
    0xa0903021915022a090105090a09120c0203010b04020a021e01140705030f31050c061813110306120a0b07120e2a0a03080705100c08160809010906020c01 67
    0x56050390102050040d001d4a620b505c01030b070341075901c1140d0030f010a55480d20400054210071400900d42102d1102e8010302941110b0a251070354800ca0007031000b000c038401484101e0084901340b200503402102280d00c9502040040c500c050b01240c004110010b0710f0340256604e170810b56180b4001100041044000e013151550160449640b0000a00e11030b0341c2c4044500c0700c022005100300020b502c0f81c46504000c2c08100c0d000c0101809403080c1d84071400070007024000c20b1075518841c003c1420400480941109110300c440341000000940d00b151552814091825500106101e0070b1041070540c0c8003184c1c14803034051040d1071a58410710320350070200306001600d10400031030110707911520400d02e0544010051082e019082d4220b20006100350700003030b21000031030348041c00400c00000c849041c00000314007075403811042c1c001408080d010000403a030601c011244c5a07044550303c01404c008921030510f07260080003c2c40046566105074440700c00b00c0e07101e0320300d080036a95620103103d4488000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 927083417 1250 927082167 927082213
    0x703091e050414100b0903030d06140103150803030106120605040f09170903060c0d14040b0f100605070209040611041238040305070b010602010f0509030a090302191502 74
    0x403c026a40303003011401c0002640d00f5001e401400301d00460740e5000c9442c100143c881c40c410407503007400b86035034be94500301c06400c04030843c4ac0020308000c008210a1040000070080b103103840c00440c5036030b18103c012202440300ca94000c08084d01c0e440e0000f1180c2d56405001d10b02e00c50203000080c541c8140c6452904813001d0424811110340900010200c0d44c0c011a08960203411600398a642c3c3c51000c0d084401041100710b5603440010407018071061201b05088144915103c9030303900803540725104006010211031066030f00081d800c0000300018100820000e41140c41200081182134900800d00c0b0380346c1094206000401207001e03144207001c401c56203100c2d152480140420400b44031705e803a60031a0301100b1115002820324002c101014401c3c0100d80206402403501012541c40b098000e0181c00e4441c4644d068504180220350380c80f0300403044074907451054a9030440030f40f031a0300380445111005060110705c80c41c05000180ca268542c10544200d041e60301030040d00c0761400c035004641c401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 927084667 1250 927083417 927083441
    0x90e09060619080703060209060d0612060c020705150c011b030b1f0c02120721020102060f0606180a0f1706070c020d0204020306280503300703091e0504 67
    0x50389034100f20a0704042100304c2640d80041d400750740c0ba00504041241442940e4401c1401454240001005201c0669401e2414841d99092100c03480404040341d54811900030254000c11950b12141d0450034140204842c41c5c0d04400480c00304007400076502d95100311141440441c2e220580707030001e481c10420041007103015110009421001c4240100030a81c42c03180240150460000c0c040300400c10059000204051080403405101c80c4850800760383d84c41d60101e025124203000b140d500c0c0d07820700c1001e1240601601c40b40c00e00310103000b528100808851200d8010384141c401181803115050860b02800f109003040c0c142051189a070340c0307010380090505041100c5e6120345001603031200e22102100d60102e0300036840f52075101c0040c90082444070507240038a2901d0624070310310750b04000751041303820071010b4843c4641031010f9424000b240c02c103500b40c0042d2803039000d100f45c1c10b10006045110700903d0f120f0304258032041086075540000040500c45100001d0400c42c1d40340c14020440c203407103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 927085917 1250 927084667 927084709
    0x10303021f050123130207290702151f1e080610050108191a01021c02030d090f02060d060905160503070c03050903240a0603031707090e090606 63
    0xc54036494540d003200f01d03144040030301c40c81c4e07981808595880418042c60b03103441c0c80031540c8040c113107003004040d00080754001d05c1c1841c0c03600000f00301d020120414070035000d54018104100c078207003c9080c4032174000c000da0006200000d42030450000444c0c003030064070405410f412604070356140e81c004140540e01002481d48001d040003005240c50300c50100711030081c2402d0b0181d490f81502109050603030200009014500098090000c1d03107419081d2020800780c0a40c0c940f9003020610424140800300d0080150340700b04562071402d282c41d40080354150041030030095150081e40040e44641c03142030303062261512240c007032182101912441d60003820b040c0c05180c8106a0800c00340040c00300908031030074081c0103168041031600420465100c01c1c0010140c0d14115110f540c61174a05184800c50600100100c001030f4004e103c622a060503079130191940c080e1140d0307a1900c510b21010081c040c80030440c40500000b0500440c0c00580d001d410080c005c0e221914000007401183d000c16220414020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 927087167 1250 927085917 927085919
    0x30f0106050a0b1e070809010e0316270e030d1a0907081521060a020c070e07020a05151f140411070b0c04030b100e060108060414010303021f0501 64
    0x99103000c0240100e0f10345034542070701e6140d8098161440300741d0240002e042400080e19000308081c0f2802803800c02404d89130390920b100d2001c01e241e07490f020a451025211800b440c1440400c1c81319030010012403001c1000400041300b2407030841900d15031150500d46500100360000710f2003070380c02001003901030541e501e904c0d100c074000061101032003d00200280030703487c804a214880710105525031080041c10340000d0140080303000a8008016046c81c1f200d00410000c80e15405080c02210310b14680c5600400c40c913410580d8040741d20001500f04020b61150715441e10000d4000d1180b0302c41d040749030300c2444081c500f0810b1038840d54004082080c60650311b550074021001e00e01c0020369a9035055400040e24182035110a415129408010b85410f151408014042025100500940344104100403c54031451601c046015450180c1403081041f040003500a5104011562b4014001071002c200900d00960813000030200381c0054006801141900002c60480d881c5140e5100035400104699 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 927088417 1250 927087167 927087169
    0x9060f1315020d0e031507020601140604050d08160b0907050a0b0c0d0e06070b01030b07020f03070c0306090819030c0f0c0f111503070c050706080601171b07080702030f010605 77
    0x86045107103c100303001c0ca20b100f060340c2e80c508102000f5081d6118110342800d0034006000b0b917441e0000d204603140345900d44582429414020140c4044030301c05404061a52a6a41e6207500703904a00030940c100c074507800340000826241c85c40140500000310260a14a00740130611002c0c141c1a000102010420400c5900800f800940c032000c080281c40c010042a25890000d1b22900c640e01000d00341844560007c4184098a1040d900801c616000c4510402908509540324061035a003d040c0b02d542a40c10404502a81c000d100300b41c0c441c001c41c40c5030200d4110b556501904901c3e074003001954500c200908540c0081002900f00501c0c00c06512100c51a0358079107030341c14007000c02000442c014595844c1a1180190741c801211603002c044d4607850700c0a4002c01c50b0b000480181c40e64890010002201030043c03101c1801094180d48010300185009800300c0d1182001c1c0061410f001c642400361044c200c4c14000d005030038886c920042d81c42a0b1030042501d0a01050300d482910392610b6020412 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 927089667 1250 927088417 927088423
    0x130309053709060e01063e150f040f080c0a020a0605031006030e100b0d020904260304110105071704120b09060106051b0109052e060501020304091109060f131502 71
    0x201a500030328140c410300c05041d01240401d101c40007034240702d2041547d0952200c04118030308883c0040390204496518a4038502c0b80c460160f501a102c07040e418850401310f08200001c00e0044524412280c1c101a5a0301203500961181c1c0000c1c0043c01c00320520100400d6804e5944c0280268602400b901418118141e101c3c07062030100900305640350a144815103803406000441900241070b011607181901b0b140925409500b200c0c09810101c48410307201c05122401c2d00d00032504405804007000c809001036135154080001a240f85006008480f1121030440060000c1c0c5450359946041003000d1034442403441c0e002c1c0840d02c05800c034000601c00ca680c80fa0030754a40e800d004c6d81015402406502c03450041410380d0021700b05004202d030710402c90005103c82510080381c100c80c001464401920b0380e084039004e014080c010f030001c000800000c0710980210204040210301545444041c01c00204107074003c0841d08210107011030ba030303611880c000c500800103001c41c040b120b0646c00e400780b000391 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 927090917 1250 927089667 927089687
    0xa15020d020a030f0f14032802120604050903090307080d030b04021206040c12050106020c010f030c08040b061516020a06020f060a0f09060203071106130309053709060e0106 76
    0x200300c48001c05440c0184034100c14046d400402249540e40e05203204001051b030542c000c1400c081380c130841084640b107058800c4880b002e04817a1181c445841d00320030032002d0040908090218881400f000d0030301d5400780610750040c15503400501810302e80e100040c0a8031b00508e05c4520480c4184140140c00d4610340344140e21000c1150005240041c491069070001207441c07100f00414603290001c10080c1e00020b4040d103002003601c50480c0c441c126141141521150240d900014060b00d010400080445101607004000100601e8290310140c42e18281034003e45a1032151041c0d100710207066003071042281025241c3d80c80034042112480c6900c1e5034906000e031004244650700c1c00000d44400c2240c0c041041958001030640d9682003540004000040482400c41e0030301a02e0f0205003401422420030300c005615845000b01a4903150801c00d603402018003901c06103840007105001c2d91403400d841c3d100140c0903140300c00b00c20308184050088402c41d80040600d0001d8400500c005030304920030007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 927092167 1250 927090917 927090947
    0x1805010c060b0307150522080a12050c0118020a050103090b0c07080702100e090c21040807020a0303090905090102090a09021602060d14131e03020c0a15020d020a03 72
    0x100c1c500b0201c0b40802d01c1c1220703070f03449100c12010606944210607400001001084281e600b1003240600681c3d0440c200e43d030510507a0784a60004041d00700103044858040496102410311b14204a040103100e82910a1070a01e0b050410907015400c085107095806200604401c2c40d00700309861640d60b441000b008007500d0080c061001040c8001000800000c44000680c058100c8078044401c50015010340092001d46102d84001c90008000c117000009070b07802412804070082030441c40300216802c0c2400a003041c0e0f0740003400c009040242e02d861425200a40c407943e00c15040905c5c1c210420100c80c0003411900385640100003034803040d0365821240084e070380ca480b001039503401c50290440004502c10030007504242e0200c1c3c281c9810b00301d5407000110000415560350a80d40c0c0a0380d028440c00f5052004004042c8a43d000c1190142c1d00076511000e84680100c8140c0f000c51000203910300119441000f1603220510a1014164140303c0500c03600c040e0b00041401034800d035009402c005a19041c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 927093417 1250 927092167 927092171
    0x906040b1308040506040f14040b1513170f0609011407111c050306040e0a1a10090911010f1110050c04050603011806050117040f020109081b011805010c06 68
    0x107400e0010007401ca80082100519480d600c075501c42da02040e000380761048001071402003503c004141460300030000c24007001041c1c07500580b001340515030b80c1d42100301c80c4904001144000700c0ca10701e550382110502a5003000600c00000c0780024103241140c0100465480c2c1d04010070a030600c5260501150445d1a6003003141074010070040b49464100e1240c00c5c590380c5211020240c00c41782e04040294000c0c141550180981503070400c07030503a2a902080000c001c0c0801031070108040890700c5103284c1242108484c2c5001d80da807084c2032000d41da61207005440050501e0001c0042c4d41e00800354407041c00c458142561000300903104251a0064507102842c501e40765400500320b040d140044902500c4020302c065100c1d40c50350030109010380b1068141034400c1c80c00034089125800303001c01030140b03516041040d5461b640c0355a40072542103501d00c12414042c5c0da0001042000091000020080c45806c0c3d5030a44100d003c001420721113504c02200745450801014400c0b640d0040184100c1e40c1c0007040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 927094667 1250 927093417 927093451
    0x3050a0321021803163002120c0108011a27030a0506180726070e01061d01050c0d230a05030403030b03011e0c02011508010c080906040b 60
    0x1a0a003000c1e00044610340b48005400c6000000540403d11082c3c41036084404050845540c00611401800b601504010f100d65000350309011820690f030491028503c8080b01101e5030106003240078090144010b500b00741440c00c90765034030840240c0144102c0c910f0540c000c002e44040c02d003a114078812400d0f820502d81d510034030100680390b40402d50340f000d02101c0d050a014142161a410103407995145805224000e03100507100065401c00d8a28131a45142c111412100ba40804000094a07a1550080c000c000039450071310420f60f4000e00190303e9680001014044804640d550003100f641880302c00c3c4111000000300084c030444580d60303030030300c0a0b00c0c000d0348007458603c280b03004114014410008100d03031181e40c01002b85000390b10035241402982881001c04d82130b0b610a0104280a92019040c0040c0c0401c0390044580b00c4528000000d009140486035010846540c000ca025a910381b0070107640151301c641045d5000388000050311850505680d003041000c00640400d15034201420 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 927095917 1250 927094667 927094697
    0xb0c0a090e0907031b050306010513060b0409020c010b0405090d121b0c0212010603020306040803071b0503040f0806010509041106160c03020a05010503100317040329010f03050a03 79
    0x10441000e090015032400c42482d19a42d42c0e5a82c046070b00044403400201803070f030000d11241403603000c00d940c3d00401910540e0308040502628501c21401a03403403d4503100002074031f440200080002c1c12080401582d103c1ca2101c1d810b0070366400c0400e01d070140d440c110800c25031840104170f014541a0070710b08601c5940d0040c08040140c01e285075658403880b0410b0040300d8081e0803178210321200d4400d0354001c20b0b2050a030703400c500720b95107448040c0d0140c0001d000240002c07110001150b000c1014100103030007030701c0d421100242000d2044201c5056000190512030203002c0b4625074000e000c880002c104640c14400403400280c1c0241c0010254090101e417a40180e850703906580c04102601280040114141400308160311188026801030400030000b0030b031075111708126840b0381e05100710b4008480c1b4640d81c108410a010700b0212100718103010100000b18201c080207401c42c030b010145c40204000c0303e6803080072503042e8840940714076004d001b00002200460101300c8203405041080440e0002c074 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 927097167 1250 927095917 927095927
    0x142d010203220302180915070903063b030d0b0a030210090914090a140c030d11070609031713170109050c060f161a04032304030b0c0a 59
    0x4210201c04000901d00c03941184004422442103d000b2580000c0407110179010070b25141099400384502d800c02c0d40203030503801d180d80f43c15400070303480d160500d682603403500c5410072a40301d01c0510129509503030141891403040e20040d1424008407141e846200c0d410301c14240e5034426522214601c40d21001d0180190780c40e210070384000c0da00a0725045020400e00e000402e484070b1402a120543c1c074203011412801080070340c41348180c213030310000c0c001200c541c1c8034002103507410041c5032894400c113443c408080c2c5060000088228a0351540405812800d411904007190303a00040e0401038011310420200d045060705c8040088811201c958130301e0981c2c0211403501994122001d43c0c41540d0081a80000560007107980710b000314152190340c271000c01040a81d00c200200c0c50902034003841004004207110803010542c07841910054580b148012403134a405904590950100d8000320b504e100c072601d4122075141c0c00300c0d00c0300614681810340d40c0b0040b440d0009440791542801c0840e0740a8098012 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 927098417 1250 927097167 927097177
    0x1f060306050106050a090614040608060f041109122d010b091005090a0b010801140d0f0302010b0108010f0e0103061d1f0b060712030519050a06142d010203 68
    0x40c009201c00d60316008041d145a00015540380042c158400005440d03104449122202c0101000c240c80d00380341c40c108444c2d141006c0e007081c0d400080c0b5202c010841d903440c420783c1c06030b2040440c2542c40755801420040c0710501c91400f1412a0000003000400c100c401c0c0c90460303e5103607017000703842c0905808029030052030b2515540d030304074020006003c50441d46d1040030007101c3c42140d081300c00e41d81d030201d4502910302114ac040e010849050043c040c020740341c025031035004000340a41441500681715445403289885058001d130f50340b6840d905d01c5580c841c0d03049026004001014030110b1602413443d500303180502c00500f089a0765220405100e248001c40405c086520048543c03076400031844904002012171200e401c40c0c034144010000382404004c0c0c039130701500b000708211017010380039040d00030b000010812650749a0400c52505805068030419000d402c00d441d000401c0c2c0c1c10058100540000803111622034503641039403424021b150084110304000007131803a2004540c1d200142d02c2c5000d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 927099667 1250 927098417 927098423
    0xa051008070e16021506010f020a060921050412031b021810080d0e040905030412080a030f02280e04021b010c110640030807030209031f0603 62
    0x1420340005000000e8500103004905810920294a40b104000d994a0a52100341701c0000c0726a00094050b600034684200500520300585042d1821540d03000200c1c1c01181088461180c062080710200791105d12201414595041c001d140a08280c00c4c10070807150383e1401000c00040000b00c505900107070b41c03502c0b10594050b001000b40f100040300150035040858417550701802301306000444100c0004c600b620765401d900c44a0007541f140d420310014004140d0140c0d40e41c40f04000020714a9031061030100685d008444503912010303128401001e59864041118075240180241c0244210040c80000039445403070840c40c040180200130386d44100400380701540240b0105000040000c0000070511610500c0020041083d40007429076000b1264480002d0a030700810004490301d06052800e1128901850207003c1d10b00100b042201000b07000c110010141d4800c4a02e5040503007210780742d0f030405000d0906509083e540000700ea59401c0715442117089023101010300c10480c400d54400700241d50 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 927100917 1250 927099667 927099673
    0xa17090901080109151a06280c1202070515070f1407140a15050d0b03030f2a1209040e010e280507090f0e15060a17060a051008 56
    0x20b07444031814024500110180c03007144d000c49050380c840b002441502c1002c0040c00030b10028088142c280a89908a4190080501c0400c8a02c8082e41c0d00c0c00711010103e0b901d990340500721300d49807038441100203a40040c04259032015100b842980d460402214004550541641d143c100701e00344020000c031f00400141501c0784a11410301400e40100744081074601c00f0108044902c042d4081c848030070a40e20400f80240f20064414440600c02d00041007401e0840d1004900401d900e400241194401c00110f0f2003c800010844010810400000c403000b81d2000590300e094458081d654650201813200e0050300d030005034020f00c030341c2c2e590300020040c41503c0c0200054101410459034070031120100101104054104803040c0e485200302040e1142d003d0050600ba502d41805003016145100c9940304094589200d2050800204500240d118018803d00e2031340c01c0c110203121122070b8940140c01840d035814061a2105800911250000c09941000500390303500112028800480d030020400c40c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 927102167 1250 927100917 927100919
    0x3030b0a03350909060316090204090f090f020424030803040209130309060c030c1a0601030b0303070803042618010e090412270608010311060304050a17090901 70
    0xc00d816607440450042201d030700d40d0303030301e0303510b0141100c00c8241c07840b88806010080c0350203d00780f648415802ca00040c007100c0d10b1808034940c5481c103003425080f03810043d5001c642004400f07203c3c0220041215860410000f038a2580c0354003d40316041c0d02c001c1d021b56207580c1642c0ce4010060603642c007504c1400031841c4495102c0c0341050080e40f00350f42c143d10a0384883c3c040f070a103003142124801c26580c181c4030b44078803914054040d01c4071480c0c05400c0d0180210442205c001c55810145407203641e84803003955606180500c0094101c0f0b4500380a14002d507c03d1111b43d0015801c44c04403500300d600841e100b1405c40c042031610071500e40c2c240304007101200c041801040c803038950480d48035007142600e801340c0c190000424003410440844000d0f10004450100304680e0f401028440b5040c44612030404480808040ea4121078075181d12070400a51500700400a200c82e02500c803617403000031a007003481c504182d100c907540c175809408040c2075200113180c1101124110b400325209900042c1002e4055 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 927103417 1250 927102167 927102173
    0x2010e042f04170607120e120304030203120115211107051612080306040b0f09130311030a0509130204180b130b060307111513150605100c03030b0a03 66
    0x55080361150001400c00c001e6402140e04011840030320070341e100e070368040100e045400e211000e01f0b080e0030800c1c50b500806190096940280008500c100e0183d0000c6903211a0524885051041640210b160000302845500c006034444144082034141d0b504031038400b01000e44440003400401d081e0128401e00107a040c007008004a10104140e2502894500c0c0e20340c0e440300c0d003c20700c2d40c0400041c4210010800100f003840e040d817100207110300103810380b20003000400100301c0c008819104803d181c000003850300205580070105040e066480b1000d1410b00c00c90a20142681c01100324141c4661046003403041140c40c150305881c0145a030340c90b0400264014036600c001002c500000c107009141c2a402d18141009900560040c1310f400340c403d80c41d5540701c0030110b407016480070400005028046601f0183c0c420800d045000301d2a6440600e040c01c000d20f010492081c00e11b10318034203103092450410055503130500506401415003820070300d0703007214a000c400a0040c0f0328240d52280400a022040c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 927104667 1250 927103417 927103511
    0x9011e0309150204080a0b090a06050108070801060b0f0304030e01020a05030a0806120c130c090b070b06210a020904080c1506130e190224030a1802010e04 68
    0x7200d009844000e20680011032039000d0b07100e280a00c200720783c8035500110026030421040c0e0352000c031220540310310350342c20f5450400b074034420307486a07006034080041440420801c1c841c45005050b407940452500090007010249404000c2c0090240200b0415071034941e402880104016540503066075591034120002030401201500c11130b002d02c2040c4502c0c010300c00c0000382c0e0311461800500b01d800c141c03c9240c41802400084540c202040b0709010f00041c0f443d0350b800508040362280c00e0b8401070b49041c505011020f40c074804e10040c81026084190190540824482860f036015201d21815540e45d0411804da0b02c51070008140c1c1d442807040f40d407041005800c1c0c013030203003504454811030181c02c1c0d4031a80541c0c259074401402034100c2d510030300001c40c4030f16171010342c0391014142c8e0072a0b402c1d050b9242c4009201d810b0311508840008100a0715100a110f0f00481c4486981c0e6412007040c540c000910040e05240c1c0c40b030055548080c40008201d541e8038803001d1442d101e68454080d00e1501d8901c0f0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 927105917 1250 927104667 927104681
    0x8070209090d1e0206040b0919060501091a0a12171902060702160e10150903032c0f18071128020d0f0602040e090c01030c02030f09011e03 61
    0x240350188004256003c003020b9002280595000b0451900c80c0e844424202ca4050b0880000c0d1088003e5070105414024988a050b0701136140050f0b9589810b140b0b00959180c1e0300010f82c0c07150034044011282c1d84030962003007620103401300b483c0320010394078201c66160342d4861340c841c2403900421090452503004d0805030000306103609440983d01c800b503059a41d20052454a01d5008414000340043d200140e0910b5100c58500891100565208104103486408034500d50000e0010700d814020b05411600415070300c0812100200302d1b40213190008a00b03a100443ea500c541d0b05002c04416945d61240500c1c081e8840d4a8840e405041c8410040c15800c090300c06090b0a01a20601345000a40c1020000c500c00306980e11024840d01c5908005040e0081e40044554043d050440303c003203145403020708090548621200400d0a000340e121717140c118115800c42c10941400d03c800301050b03010041e034070f40d1555000700c0c5031600702102c016a2034040b014044101c07440c803021002011549500491 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 927107167 1250 927105917 927105943
    0x7080c0a0605240409031b02010e0a09050603120a050405040c031508030408010c030b30011a0103110903070612021c0c0305010e0106050a120209030307110306010602011e090807020909 81
    0x70f80f02c582c10030180419038800f444040e02140c6000c01d082c41c0c50130141c40c40c900861051401c6150075070604002051040a60000c810080d500c0d0100807150404024050350480e49681260070110a81c400820f144150302881d405030752505540c984450185c2c1140b40386809080240b103010b41c9030b8003190b5481e082449040010340c24841d0341d401300c41c0240314103484602c0240100c000d413107284a4040c00b22103000c2006522041110788600c000e0b500388143c92000d06c50307400d9112031010601c0011706880500c500090380080810103007810b550b0002e008012628103040190180c004440c58000a001d66401c0e803081e04020b0940e070302d841450340e002c0d004908a94404100d940d0301c80140e4010300c0002d018007008075004000e0a8402d0740a0200c04100b0404130001500e0000000301007810f5811507101141c00c90341d03030421003070303245010b0240c0c90140c01c00748020041d44004281d030780d202512002d401203501d13a941024405000320101114006034015000c1c2c4c030039040c01c0755219650760f240c024030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 927108417 1250 927107167 927107221
    0xd0903020f010c050c0312061923060a05030f0a06170304031b0e01090f15080312010801111803030906041e0f14040203100302100306061805010507080c0a0605 70
    0x240c0b0f0b401d07005000356414803c890380114145071203982450902c02d4040c180f1540070f420719103203480103c83d0000e510090819a0421180d1480c10154040c03015840c0100600c2904248103c2e01100e501405032a40000e99080d01200b6840e20002c070401040c582c0c10041c00400c0c0c1c14450050624000001e004807441140c2c0c40800140000030001500024041d4604006000d401082005035641040920309072003540020380c8808a250030440d01d4890344400003a03000403e46e2614681060391503401000c0c4070009000c898480c04503000305204035480341c3c02d101203202c000c0c0c466840800c11b840040d074021f400382e95103a0b200c91202a07100360b9007102040d038510b9140d000c41c001c2d83c00514002103640c58224000c500079400c04202c081d400080c600020010b6000340040940d441800604980005441c0091101d080100090144804451810b00c0c02091201089541d0b40302c01200c0c240c0d0f411100d0a92503100c0f8000c52400d0600b00c0710301405080c1002d00384040c2041701c204001c1841180812 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 927109667 1250 927108417 927108431
    0x409082d031f170616030e060a06060f0e03060c07030201110d0b03101b0c020301090204060e0a182105040e0406290a090c030b12010c02150c19050d0903020f01 70
    0x100148034241010004110340045000c91a41c6645c0d501884050f00710f401c001c280724200b4401c141c5400c2d012201d080d512030315100d04104542d000541c50310010030700c1c54058070aa403500d02181d654540500b81350104c21000030329a048c9403013076002441d01ca441ca0f210301c0c0d0f90280307050b0101c003420071400c1c0c041c424080d5442d000c2a9824a01c9640e4010a1603024010454240b0030181d85502081d00c5c00d036015502e4131041c900695640c4901c3c0041d180c10b04005540303051030951a801c40e4407100d05054000e6982c0703030600c085445050f99900869112402d103804035015981180e071806198000c4a1291601e010300c010030400b9085500171801d030726443da480142940f030b40240001fa00452030b0b0060000c1000f40400009500900008191414042042c000c5100881c3d0100516580b44640c2d0b50745009500d1510790501001c581da0700c6566094026090a401040c20303442000341c0040013034800700c8080c0c402d502810503074424540d1603004001840b52414042d4035680303c0c1e80c41580390351070f00741 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 927110917 1250 927109667 927109679
    0x9040204030638010e271f0305060f0a02071b0602010c0302090105030a1515081f18020d090b04061431050132060409082d031f 56
    0xd841c00c043d00b50030081c0e00c0c40490400042d40d40300080c21041d6081203421450000e0803001100719001401034010440391803904014500c6c25100085130328002105254041010540001d21759030000225110580b107034136985800b100034450348800910311151900c4c1c2d0868040e1403070009044408a4000307001092545404404034401c1c1e05130b0b00d0104070240003107104c4010513400f01c5d0904080188030a42180c44400f10080c04c1604850140001c22001c1040340100d03050a42501e9403550390012009141450a41241a0b514111703100040340d01081400c0120811303004003084903007001181c240c90806040c40005032612402c2c5803001900e0b04042282301b00c4030105c1240010103407800c2c600d5521260030510f40c0c000c4007a82580e044d92502000c42101074141081042d0038080c50107140c070040da400a52840100013001503200b20324140011380414840310440302d007083c4000400000307061480710340e15a8042c2c0e00e04651180404002c200c0c08000b07010007407600000f00d01c0100b01580e40c4603 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 927112167 1250 927110917 927110981
    0x10806150301060f120606030602270a030803010501082211190501050405060c07090c1701230405090a060f0506011b020a090203090304170a0b180a03050d02090402040306 75
    0x710420310a40c820484c00c010600a0021045101c1d10a500114181d03580707403038000a9030403840c0200d1a290340d240800c0d114501a102030446040d0980780300c0c0e08149962200c0b200f500051040c5814004407000240348000d515903084c112303003461100d21b5050101230504803550554139004038000c0b00c0c2800074400c420781155549049603016518240b4180c205002e10100703030030507a1517592038450090003195503441c50288000c40c504683d19010b2403a6240700a401c50081a070020b50f10191411500c90f03841942c2c482c0b4100041d050f40c0214035070300e4220040e85042203c3c9405842d49150041102401e18913402090150341d00360303105009048043c0649402101d4104002d6000d1481c03581048030f100aa005590322042000c1a01c0c10141d550182480181e1846e07400300c45072f00b0103d00801003004400c02e00760001840a243e15003000400352041e40c0d8148124082d06002c8c01180b0545984000d8045842c5a00050002c1d51070360340e0782c507146015080320801a20807885401b04500f9542045c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 927113417 1250 927112167 927112169
    0x1e0c1707030b06060702130e21030f0f011401050a0903120e0301060504020406051603020a080403050106260a030324030c09050901020a1b0206040b04150212091311090901080615030106 81
    0x180061000c42035624140010480003c20300130034001d40d140642e29107270f66400381703010280001501d6641d241c0040081e024003001070000f030f0000b45050050260040407492440066020301f0180c0c1c2e114903680042e40c4940a503400108210a00d0411192041c0d01a589010408040d0003e04c4031343d40b200100800d900440c001c0400088050003050300302190f0b843d04034032290090058034910b40761034403405003c0d0f004c0e030400e50b03d680d1507072403c100d100d042c1a8800c2c8901c203034826400c040018900c01c2c5031074080c0c550010341015190721004a07502c140c43d6840c03e5090440e5003420311140d81c0d1402c1c03e40c0420500c500b428003882d1500042d11043d041c000c58204009a80e54059040344a144072b0300100c010a4080ea000f69003400b01107143c80b041d60080000c0c24007a82080c010221009009144c4480000d07801c0d5218028001d881c09038454010503100d00400c0c66012403544060007044602d4013800040507401440840001036401000c01c545001c4c5d030a101d0500c07801042c04040c50f09039462 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 927114667 1250 927113417 927113419
    0xc0a0b0a0e09040206070609051e010c090e04051f090302060604023603011107050d0e03071a0904060b0703020d03060803030412210c0e010206041e0c1707030b06060702 74
    0x640034840074034a000460154020b00c0184003900b068900e0300d40204a540c018002c40c0e0580c0030903101c144001c034003a0f80752094040f800003442035203c8103c0003003054015200c3d46009100000114041040c1408110b500c0c46548240080390208505442c028004030b10064001d4024007002c10340c141018000c81d50b0607442d441d803075010107840c10440c51040e6107010301494031b030441842003a01d40c0da007030040002c80b00449140c00d407135056500f130650420010080d00c1c03040c4484c90040c240caa4801003440422104840301c171201422021603001064072903035030300a50003881c09001055000031074001c7e1001074003030350845070800300c61030059040ba02c1c81d000d68034650b030003800000c002404406150518503240d00e810411840e040600405540c4650111b10885450b4211360280d10350144907418910000d10081000f41480e0700c407040707038060005100714034625910301c10041c0480d080d00382c0e00519008404030707040800300f4021a03d800c810301044451043d0030001c20004d10300042501c1170310703070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 927115917 1250 927114667 927114677
    0x1506190806070e0315073b0405220501020a02010c08101a09220b03010b010c11060f04060f020709020a022d1504050d080403080403140d0606020c0a0b0a 67
    0x550150a481c5408040200c0d503040c42401200d07000c80410300c403441d00401c100e40301c8080e0044240c8071f401521988021300849070540445490640b0964046045c08460580c0c00003150b49481c800d0030306820b031910b20803002c807128002803c00c100c4d0560040c10100120340c0200070300c0807050401c03107512000b682d045a4030b41c0c2c0032030240b0003031280300d4485c40ca8501c0050102d141000e20b4000c44c03081c120459101d80212010941001c0e90314060082910081c2d00310000c000e001410000a0042140024098024171400b208805c042d1140700c02c9402c2c4100844d0b5003501c40b0b60740c110040c000c1c120039a18030b006000d0074000140407145030080c2c500c6480342c0d4003c0c102c040c041c641030100360400c00c00e00c007401c0c0140c0e40403880100004e11040780d40410203444c2c1c19103441d01c0e0804a18080d2900511410004480c0420000c2030b40042c01c65000781e4181752125541c500c600412280e4043c0e00303030403102c440c40c040001550035000111502103200584005c0d000f20340e1000c3c0600d06000710704400c0b01280c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 927117167 1250 927115917 927115921
    0xb13060c0321021e0a030c02010c1718190507050306100905061906020a03030b0901080703080c031201170c0910060e0d05012d1b0507141506190806 65
    0x5180b1040365102400500006060451003a510114162921a5040c2442001902480056042c00745002e03100d030710f00080c0300040003060b00900a0150601403d40000d900c3c0c00b1640d522401039020041141c0c80d81112403014052400300000743d9408000c8a0520402e840011a400c000c5030503071080e0700031401d05447c10b1070498520003405004244030b03804000303c4040b200304095806d64501a02465005010441c07052501400700c0e410690a14031400301c48004210f52080010703140251b0398460360054403041c040c1d07080c5180d4044e4400701203903c4c1459002103180721080240d459030f03c1120f0120380d0340c01c1924003440b16506090390000b0807200b95040c1030001902900d4140c10101006d01560215051501d401d4216060b60341154480c0c5021400030a28024824004110110600003000700241c021011500100c80741c042c0c81c140302020070352805000d449060184010041c006032001081280c2c00300400030f030103d821b00d2240080484420700140d0070000d4400752100b0780c0080603d9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 927118417 1250 927117167 927117197
    0x21c0b060a0f0c0b010314010b010804080714190605070914030604030e030f1c030c0203341b0501030e030c070b030a150f140904020d0f02060c03040b13060c03 70
    0x3101c1041801e020f07080d10038000103450301500d07500842c0190f0388204411000d1141a007540c51200340306c0d041100d0403080c400410b01d584100c1e900c003035200a0f600c1501001c002010300306503890314ad8002c10202e44109105100580e00124400d0f50a550b43c003601e56101c6007179141906001d150542c05600c8480000c0009028022030001c8003c020304840942554407601032a11096142600242c200c0c4001c00314400e400d03000d035500185250014508200c1d07412140048050500105444001203452484000600b85034003504e40b03403c034003404080e0000084888000940b0b1160500207860240c0e00381e021900031003603c00705640800505811458992400c50907000504412031455031481101c0d00041c1c2c104230304005000c000d10300a0f1b21031500300d89030807061040c100383c0d0040c2c464804000040e41c3d2400d0034490183e1001070b804162641c3d0011489d2802950402c1183d0300c8005408180120b14201070f010603110241b981c0c1c44030380c17508011911040100b60040c0810340c000088028 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 927119667 1250 927118417 927118427
    0x1050a090317091c050408070b04060c2423011a040b03040212070e1b0712030e0f160302120115030f060b15040905281508030d021c0b060a 61
    0x80340e0340703104480f56041c1503103015a0420459083c84017090002174200321703100701400790400512940078418102031906101904001031220010110800501c44900aa6010790751201658882c0d174200804401c03241039004000e150012244c3c000807143c0009000320440c2640a5041d00c5540500d0400d482c20104d2206030b04003600480c1d0048030601c42454254081007180001e000c1b002080d0346070300700b026a208000004a000040e8007500300300d90004a6030120b40704500ca0364619000400488441409041410404000182c2c0c00f442c1401c4164a0f40c0b04001000d1702d0007101c68040c08240c000c1e40c507080350b041c0e400b01103004035080c3d0f042010540c00c1c0da21714455406800c2c00b0800c3d0420f46d000131904040788128403116080401c081c802d400180c0b00d00c1e07901403a180012400e60b00c520301c495403440420744c5441806030b01c17856882108001d80f0700020007844218200c82d1583c1041d001c40c006500000f02905104003105c1403038107040500c0c060311400c1da0025119516004480408880c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 927120917 1250 927119667 927119671
    0x9100504030f2a060b1807200312070f0f09050d0201141c142d07020a0804080d110316200d0b0709050d0b1611070311010201050a090317 60
    0xa52581c003405018040320a00f5500034101c4d200d8040002d030541801c0c20000000c0c204000b50a9180e9040b08026085801c0441038050f00c0750541603032140340c40003007c0c2d4594441e81030718840c84402c1d001408103041d00020190000360042c0c8614400404625048a00000910940381d000e61046044009940942000f400004040c00041e2074910060030000010f82e145001030759a0b80d55000300e804c8100c7c3c0710301413a0841604040030150314501040502d401710000ca003681c02d40c9440c808200c0440c0204000c04255a0007080d90713403615035440c0b580742c580d0200c1801c40e001c5456402809000c3c200842142c00d4484036040b51200b01403161130f9500f20501400d00c401180c0d1180400c00c090b540c49621080116200b5841d4241c0c1c0d01e07000f10001c18102507a40080d014900c9400c40c1800100141c651039441040c070300310030310f4101e1002c40844060100b01c528040c2402030311004010321529800a612007042a0020300c4162194201001101c002c2030025001407020844c3c0000401a8000c00d0307 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 927122167 1250 927120917 927120947
    0xd05030c03060a0305030f040509101401140d0606020a020312071a0a0207170d06171221010b0d1118131103010f03150c0806010503040c12080309100504030f 69
    0x3c00b80540f0b030b50b201c616503804070030500c3c001e41e008a0204550f1402c1c600940e03020101040015000e0716201d1441b200c600c4003906507050000085e21240155520419181074180070001800115075803440030b074a0340d00c09603069002e8040c9032f01c0c0d040c144140c007007103402c0945d00c9003184603400036403401e100d074604018149481140c1c08204100c046040900000c080182405206590f042e0f190604d800f25426680000d03840020304208005400c4082503800031280000c01fa80c1d1f070781c182c801685981c100b48004004ad4010b030b000022401480c0c0e0406400000840e980c2088101398448552032180510003c82010600d15881413420b030600da0140304580c50301c0f142c0070a1840004083c5441070708260040301014041c034404100740921003800b6074060122150420011003103c80081c15080001c00081c103102001000c03404014900702440010007908140720102d000600d0221a9640140c502a100e44141d1000c859101080d00c00e280c040d583c540c071401c0810780d4048044d10b00510043d468 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 927123417 1250 927122167 927122179
    0xe0616050d050408030601020d031b0c021f020a051515121f0203060a321201020a030518010c200f011a01020d0c1707230a0507080d05030c0306 63
    0x244450b004283c040c0e442921000d441c0d280c484002883c20031803c02120030541400c08903610380400e4240c146009555151080200c047c1d030010401c1c420358816001c200c60502c07a2900c04869010031912500c62082c4160740c480c0d260404c00c0c4030f6000055940400103001394548202c44d1070b01d529040784010401c400e032880303c07915079162107101c0f10440100c11120380010422620745060050000980303000f0f4400040d8030307220494442e24291000034041001990900c030000e0b65900502d14010600c1e5100a5545076418000107020702401d68a02d0b1106a0014404074240030601894900c9042d0b60340c1c02203100920903820505042a8449032298060080c0c4088100400c0c01488600c0c500700303410b610707854000400280b41903504030f030000400034524003c00010301072062040c440c00b12400d8954860000e4200b940c002c1c605860510210005800300704c03441c3c1004560303074001d40e0040043d0b580d034580d40c450050302c0303920000c10307080040c1d020000500c54800d01005160003180103409 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 927124667 1250 927123417 927123427
    0x6030f1529221503021311120c0403020a0810060b0a0c030e040b040c0206012c071d040f05060a05040203060609190f030302031909180e01090c0f08100e061605 70
    0x303034400f191240841038003603103807408080c001d40c101001d803a58501c0182d036041043e85480810140607005480000501c0c800391030202d45c0c00443c000030b88001c0c680040000c0803060b65121305695402d040031845400b541400f00005210800b80e041da120310300c060310341c002460500d980449003054200045540555105070580040e21280b007141131403145500180030a504081c141940c00380760942d4040f03155001d542d10b180b51024004202d070041103504002d0a128100481d14200c1d200c1c607510705400c00e150442880e5103a030f41e5003056010720b0b030590390441d4858032001031000381d03c0100d694a030030480811050f42c2e00c0c10445c2480c028500012500101c0a4a654035599103000642c42a40103920203e02000340c0e5403a4100c01e06244c0c07541c107182100b546004007000203140c0396041071210390740c1d60009840d94070b420340001b03912580c061121b18003036444d11006407800d1098050440b0074811220b14109409041c403501c40c916003400010542583c810381b401e0b04041c2c04482c014100042842 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 927125917 1250 927124667 927124729
    0x612050415020c01020406030b040204030f030f03110d0501051c02102006010306090c09200a02150a061d042102191208060603131506030f1529 63
    0x30162000f448198005a503d40c0f500c0002001d58400007805031046c1e204001c2000013070b950f1700540728802c0d8507041c2490ac0724030321101a4018400703d4991440d0050000d100103003015242e002034142d5004481c0c0740c201e001c00c140c1080d05a00c030080003d4100e0842d0354280c06080c0030380a010411100b031740c1c1c21074042d121903802a0518100b030340100d841e96146c20020007004122101c00000c0c020800702042041e2215010402e0000c0740e41502c4480c0800160701c400380c9200340941503406007807079034188090030050030190007008107216050b800400785102d00f070284009004c180c05503410155000980801304c40d00c02080c100c4482c1d0809503c0740400544281014103041d45c1030902031003047c0707840302030307035001900882c4000d103460300c0b0f1341040040110004c0480e00c011802500007138550f03c0300c50701218840007040b0b1504090265801ea40c1c140d0108150561000244258404280000301208040e01f0501300c03c2200304614941044030045d003403d04100304400c01607499110522200411 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 927127167 1250 927125917 927125921
    0x7090e091e1617070b09011b0308010303080108030c030904020f04050306010326040602060a09020319061d031c0c090f03050a03020d02161a040e0106020607020d03060612050415 78
    0xd51940a4200c0540302101400719003490780240410543d5421a45002d5041034a50700180200481104041410001a4031401d05003604c1b00603a124020301d84a10304010346444008d04c42140020305020004c00d940c1c5010040c0c0700107203691001107052215000410010b0341080a1880b407410b024440020745030f0301001013500850046180d240c00791410a1801e030554451170801c2c0000b6003c01c0100a036a90006015602030801030001800da04540300190904200d0041242410501020030b018454291300001803200a421021040740b40c02d00415103d00843d541c1d245081c1004007031840500294002443c00f1442e403070110b01c0151143c2c42030012031050340040d1500e07400500e5840c2090f8040100f4040041c041c002400701c1000100b00010803d540d0107800030f04680d455049910007040c4040d00d014141100c1c110f8025031312544025683c00341220f0980062207200c0d424909640288100313825260035642e000c00038111000c01c0b0b0044e040150007200d21030031404c066410940c0354 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 927128417 1250 927127167 927127213
    0x150306180f0108010b09010302010e010302030406062d1d4003030b0103050103080301152a0c141311090d050c040b19091d01230f07090e09 61
    0x8100c01c50100e50600d03a000d405c45001d4040240284142801030015030b8201c2e94020141c00c4c240ba001d41e03265501c1c40c014019200769800b2070b01d03040d00c1c0c1c001d41c02e11001010a4020200d20f4441c1c0c48806a0758100501201c14a500e0f403000070115580440d06a2001c143c1d0103110180c20300001002013001005424001040d510b44181105090f10110030141e0500500c402400c3c01d190500c034550454035103d205200601c40d0034040715007485d2440e106030003100d040340c1c0c95850a542c0e82c0511403401710400c01920f41542110402c40ba200c0c04540410300c5030b1600944080540a842d580781481c0b1084024019800807045c40c400c10b10606000d0755559500061300341c85080605950a00d0406000a40d044003090b5841070303084906540448514a0600003160140301004c2291001c00030804560040408480c0155080203d209040345007a0440f140d9014403404c02d000340c0c0e9422920320290702084e1041070004030030710810000c01c0c001ea0b0421760482155410355079440800001d00e0094040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 927129667 1250 927128417 927128431
    0x3080d23060114281103191b0206040b0702090903040e040b131e11030f030d0917030f0f070c0320031605010609050a0e07061b1406061e15030618 64
    0x1006138104c188550003507a003c4c04140920095040283e80a414401c046041002c1810003441e078614910111140d03620144094002e48059504c3c1c1e11070a0700020703030b44601c00590146020740085581d10394004126400c4541b450001011030f202c540c6c0d6074012001c050403005200e9821440ca401007003075441590b001c4034801d0301e0407007504024a0b14000055401014031f01c079070003402c0e003150050004011100c500120314800a04139143e4a0140060741304c0341d1450003082000301c2000030403440c0079104e5002c2e802518a0140d19503e044003121031041928000300001c1d12018a4583d003541d0900c0407803181c280c4001d503402d00c0326180c0b0069100380b42510030f8500d40e444810070407100c2100e12401d90000e1410034140418683c40c081c49503184120311035881001500b01c484403c0610500221010552203940f54116900618a030742c0d6400c004e0b201c83c1e02c50010000001031184080341d10404004025201800c00c800f0180112032941000300045e411001c0e80040a00040f040016540700d046 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 927130917 1250 927129667 927129727
    0x18050a08010e010c02010e070306051b04080a06050f06011704030c0b0a2702010f081504290a030c120204020c03030108010501030512030103081c1503080d23060114 72
    0x42d41441900b9110544001010b40e40340c141060398040002c105041544e410070400305468641000c66070200c1412501010000030118000c80c01840104094080a004042c00e010325210766090b0851903601b81ca803140803031800c40c030780c60a0800031003440c2d41c0b20f03000b0704000b910000305444444480008490b40c840c8269600b60409048410321101c0c000b8042d02c0c03603102065401503002900d2609141c140c0d9050040c101c001525503081e0f80d124046000e0058400d03c0960b081c14900e500180309038480d50301d4990394035080c07441c41c2465020301003103a4000040d020b18500c4d0580b40341040d07400358000c0c1e8101d602040115280e03030040008600800c2c1c11000081d05601d581401c40c20140c14207420504a81c013040100041803800c4e040d2411910f079801c212070390b0203d9940071030041501c01996210b840f00b66000000307001410000e491198254207003442032031011410513602020819820b84882c0e000000304a65521440801c86001c0e0304442c402d150495070840070024101019500c00011 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 927132167 1250 927130917 927130931
    0x70e031c030506030f0c030a0206070c030503120411010f17090703060905060105011103030705120c0c01091b170a12050405220c050703020a12021e07210f0318050a0801 74
    0x1c11304004034840501082c01038482c2442580c002611401080e8000e88180004641310003480540c950040007158440101c4e40e031150764050303100c06c00004a0341600e804040c21014180755016001a07a44000c469031101d90004501e451800d0030710000d0074010b0f8a2081c0107000c000105a84108215540504001c0100d5031409000420100d011569030140390400d01c1070000007500b00d0161081c09011621104450b40d403a00303031f44102d005d200c00035105c542c01c061845050051982801081c0420f840c42070080301e03110b04002a550081c140500103961040000b20081072021010065034819864100c0c94543e4807000a68442610040640000302c2520316203200e2455100c0c1024150490408034141002078402a4031400d5220740a805481d070030001581141c420b110001c40440041208124020760f07106c100e40c1d40c240c80c0960f111241d280c40014804000da07150008801d940118084044011a07900301c8000141c1c8002d102140f844000104e455a25001d09078098030f80360f000080c00c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 927133417 1250 927132167 927132169
    0x15080a080702100306030c030f0f15142a0d090f03120c03091a0a0e0f0a050c09010311010f020a151a0f06040605130518010e010b04060503070e031c030506 68
    0x21444000c1000c18549026010000509a1f404d001c00b20381d00500c00000b10360f01c90510300014004135200610a104040c001c084000c1d0759408245081c1c4a48142d142a580c0d1503084001544541d081d0740100544d510f0324400450010300401050404000c0070a20b252250f480041098020310114081480356440514140382403044061200e440c1c50180300c030782103644401601448040302140003071120000181c03440100d070001d050900e00001190016441183e40175291410002c04883c0c9014562540c3d4003844e101c4c601c60f0580c3d40181d942c101050040005581d00700d44410580d0560040c2084035003c26144808580004102d41c2c1c0803440d442c0c1814200c1e00d00c140c1c03c007414031035080034840c000d032a190003059a094075402e06080342d07902e1000c007000c1c5c3d009004d94849580203406000300c05000d44550146812a0607484421038540d880e043c0c1d6184070f00460003490300154051000988151141000c280745c1704d40074007911800c3d507070103940015a00062000300082502c1c0c209201103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 927134667 1250 927133417 927133429
    0x1805010903022e05040809090108030901020d02120406030c0908060f06090901020703080402041a09010b071407140f060c030a0903021f020c3a06060906031515080a080702 75
    0x144a0511040d4180802541203a030010007055400705a43d40c0c0d9200041c040150050442e002580001c255000c0741d17030b44d40469a5a588031001c4a401409a24401e4580c54000070b440307159078205d0600c43d8141400c0c414101c000f800106085e00412541c0c2c1c20005d8070305000d104c0d2781e0045008080708000c0d440c00c0300074003c070040e01030544804d603071040105102003548060720641055040300c020542003203c1c802114000c40f441e100e2075010040c1d100000d04050076400500ea19807140c50782c0c141c80c41509004549403550343c03007800392801c00003c00c40c20300d10f8103e000d65510000213200608001c01c03510100d10f1600224a600c01003000c48a0038030551030318a83c0f00e024a401e946006400710b040d07410082d1101c03030322407000e03005200c0c641d03444215132038600e028400059100303191030080c1c500c0384910040ca0700d00702060314040d1a00c14003052031801e80c01490249c0b0b4205285080b10143e4054010007007400c50403403c1b01880564002c40c0e615414049400540d00a00c819a2074036424010070074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 927135917 1250 927134667 927134683
    0x8091c0809011704081b0f0304080a0b01050406030512091c0302060711010e0705041a0315010f0e010b0f073003060f0501080103150f02030c0d050601031e0b04180501090302 76
    0xf40612aa0003080005501441180c0c6a1400c01e1100054540b10700f0700540340c882801d1885011717000104010901d400000394911546c0c1c01048106a266030b1340341800120740960101030034981080f00800303d00c011040c000c10840174045d100d21900500c5491414200c400e40c0e404900507003048c024410805d520180001c0b480000b840200284043c0e0703a12183ea8551a1140380d001c0e80d1103404150600d40801044082c428000e0180e03907868460101c10310f94523109006007035003001e1140e4041641e504440805060707444981d00a440d04510141d07201035900420011510100c008507107007058041010030408041716280e44100c5050015400340544030150085410003400c0c2004010aa130b000407200d04407070f00404800c46a0b100070084101030452085403982c00790000052041900c820b030010b143c10740346160200420788a84c8011400d4818514259404c0300307501c04000c0341841980d0000e09030103401480043c0700000154041c1120744a0402078480307075500c84000c000d254062203442 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 927137167 1250 927135917 927135947
    0x10050c0a03140c370e0910030317060619050c190521130f090c030b01020a140703062417030706091103100e1606050708091c080901 58
    0x34503610701420f08003084d00950a03016450341079a10b11801c9003004001d000c5416018000107024205554800341902d41044109402428114001610203848200820503254940d807035000783c000d40d00403214100000780203554000c104114290038101000d07000000000c007511002e448144d81c809040c200b143d0b09031a944002e91941454000030302c007051000c0c20464200d00c10220203106004660680a0b02d00b1009400c0309000000c107000158030504001c40700c8015041c02000507421080b0300361050758500030302507803040e10207000040d803201110040703401b070301d0885806c250340c1c1d00e40c041034030390601c103080d05454a0200350050012a01c0040b01804401600001041000805580ea0300c10518003a011903a03c440d09010401008444000c03100011b003101c52102c064501c907801456105005202d502c44d03c4030003000e007264640c600045035140c4c0c807070500344516621000b445900c0f940708242e2103c00003010300d10729084013800815607401083c01e5500c0e020b0341e030000f52030201200240 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 927138417 1250 927137167 927137201
    0x70302102111250501150f050904081b060603060c191101020d020403030302070b0105121515091807080c0d14030c0d170108070312030903030615050a0305010506031302011110050c0a03 81
    0xd10945588042900c11030f070080d41d403812203943e030742403090850050304603107a8020842c00000d040e1050020b0040e013b104100d0664115444203d80041d1034881c008002184450701040d8661050150700b0005414020b0307000035207080f0840d00100c0413a44036810460100e030b4081010418030401e415614050401924004030792810540382c9503884828005a10491588100042041022061440d00600054011640d82c181200680218601c45d65400c2e15032103494800212480e002034031071341c2d10001030b044608584068071402c20001241c22042c017544010800c1c50b00b454010071080c0c0c7c401c2059983c400303500c07134101d011032a0400103a01441c06540441001d002041c50044030342d070031000728240003480c0015032a066001c0e000d541e1080d44031b410810003011400b50082c00504860b0303896501042140e0700c90040081502080c0e465424401004044e24010350280a001307400303a108004440d060500380b14000280c1c0c108403001c1d40110804103400440580601401280b0901030080d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 927139667 1250 927138417 927138419
    0x9020a17010b04080a0b0c0d1523010915030905030d2007201305010603021b1b100212040b09010329040b0a0b0c07030210211125050115 60
    0xa0103541712888403014020814407008038011045210442d4881c1840500c01e220a186628014030312141520410b00e5004847c03041c10880301c6034068284040a0503101d822000b0700b00382c506060071030080102000c1c19942c07001d10020a07070070030103060301c8101c500c004a48020603023010102c54601c1c003182520303448107000b42000154400341c1d2001c090350107502079032425403010005120007962281202030b58030304000171940c0b41c2c2c150001c2140c219000782c5d0300c500821080b00c407070352107020010b03000e409143c034407002040380b90040c03d0162102c1188111801c500c400790b1181600e0b8880e43c17213900810340015050f00d29503090302400c0c002c4400440921200400654000500040400d62a109941c0c45000740d2481da2440520406840030f85281c0da242c440803100350f5910707002804240e2140b5030801c24404103d09c47c0c01da880d140080701c10701e1850424601e41d103102400b01d000100c5541d10307091103205d481c40785292490140342d0b4204050401d914880c100642126901c894a1310152080c01d8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 927140917 1250 927139667 927139679
    0x90b070f050c060705090d08030405101a010c06050709050307060806010822120912060f1a030a1e12021e0c010e090603014122030909020a17010b04 65
    0x80c009500c0442400d20300d581d0780035100041d4003d00d1f5001e0041401201000b130206028000130183d00c000401101003140d00214882503032040f004415142c00140f08010940005038039400aa4100d1f0300782c10f1081116454000107420b040c031a41243d000101011b023040715039070b8080c0740d854001d0b00d81c0a80710306600724003850b03010302d8601c55009884040c0880032134004505c41c0c0c000381c00410318800862001d07120352800a001c0e040781860441118107040000070320850080110301000030041c020145104a5628948103100b001d001c9043c226581101001041121070768813844c10b500c1d405402c081e18820541019440482e201819552048181c510750ba42c200c4442c581d031500880d00da10300c070b580e91000240505403a500d6140e640d041802001030030100308064010409882c4e012a0f50f803104003081d050b0b026011078212242c4000d031402169268903100d0500741c0e45002c0d02d800c0c07032082c0e103c1d0501d1050741c1c007440d10900016084c0b0b00145060001d44e10050240003451407442c90145408 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 927142167 1250 927140917 927140923
    0x7081005061e0309030c0f010213062d0309061d030a0c0503090d06021c020901052502031b0114070b0a020a020f16030b010e060d24090b070f050c 64
    0x100403a03000d008002180400071040030902252140003507182c0781d80b85441c0009580303913000117841c4100e5216401c0003480085040c0240c03404030106407000341440e80382204c210394a03105029005c034031150036040103643e020003030007054070070720036031804a0428060b2501c08120783c40002001c200502c88902084d2805c80071048603d90702c0c00e03283c049906403a50800314118440c0740f9900d58085840c1b00e41c3c0080021a4000c0c0844080c407601d003442d40c802401090302030384031360310754140050b601f004400d105042c00d607038254050140d040d0343d8580b44d05980c00309180c40e0b0104841941c070360402001a920790ba014068020303c1900780016820710407166141d000440d030242c00351600c607801042a2600d184204412008968846c08840c00e89207a941c40e109404091701055075030103034840c008100c0484401c40310380981c030064418102450a038941000f0b1801a0003442c0490400c0002800c0b1801c060007010b031024000c03004105141804c0c1405010b10a010080e40c0510a09000020714050b003c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 927143417 1250 927142167 927142169
    0x90a170718140c211008060f0106020303040f0c030213050603071406030c0a031503030c060b06030618060105090a0803250302030a08070c060203091c030b0f040b0406030218040605070810 82
    0x1443c903151300c0b18400d440d1540c000041c01d8000103400c1c1d80800f080a10291601004101c03050b100946000391100341d01c01071102d10900411001d40c1c0100046000103802d80b204d54a101c0c06500d610b43c100b44c0340e50000c1c0a80d100c1300b0305100c10760303100e00500409250a00584004240c4201400403120880380804c0c1c6501000702400d5081d40c010a800d20158001d030801103022400c0240e89640d941c507840c4c0504180b03504401505c031146003644035106420400104d90040100900c00500c00ca69100089041c40d00200300504000c42482001d8854071075640c901e01034505100907646415000030a07800d0317074a441a40100f002c101c0d14a48c804642c01104461413108186401d600c19902c0e0b540580da44d22480c0401490705200008000300903034042050a2050218500d841c07c05007085c0c3c0850a03900e80311602580300d0400e81000e0300f945020342c802c07901c4a80c098004900719580786c0000d02044220080c163f520912501080204003a600c1003035072001140c00d09115504107240103110ba1603103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 927144667 1250 927143417 927143431
    0xb01090504050606090a3c030204091703010b0403050c090708061306030f03030504050d02060c040b0c0a05010f0c0f1704020d02061911121e090a17071814 68
    0x42c0310702040c0c841d1940307011034191072406000b42c0c0580d507540440d01d00a10a0300d8480c0d0710101c104001c1580c0407020284820035849401004440d10704607000c0100501c5401012204454128030f682c15254990001c3d40c000c2c12040f4104d0f440e1465030800301d04044002114034400c5001c0400c00040c3ca4004a04a400101c155542511100c65414110040c040c681000c3d0003000034a00ea01c0405074141c004900c11032080d41611031210703040c2c00c1680d41d90810b41740d11180040a001c14040003201c2ea02804e4040d601404507840410a500d0315821101d01070390814000d84c0740c60010030280c0d08503501d900806042d2400c201e11a8100d0001040726001401c000d01c05c1e02e010440e4001e42d607586003541c3e5031085200d48101c856403005400b50103940000404000c42c01004043c8031040441ca0a40b4070b06aa0040943e814506914086a40e07900c00c1daa4103500420a0f440461112545221072210044070340080c100141042220080d1401041d29080700e0f03400d0200000300381c0d8011581c6900209 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 927145917 1250 927144667 927144671
    0x706080603210d1d010612060f0207050a03030b01020a0b0c0d1404080703030c0311130e0601031103060f030a140c040b0a12060f1b02100c0309050a0b06010c0b012301030b01090504 79
    0x200c41440c00c0304e503244281e00045940c00c0c04800b041d4400b284082e081c5082c8143c01c104001992091400264011150040d1071034100303080c0030011a01940052441c1801441603c1c003d80c103603070301d1180021303060350442c1e0742060210788550407803410b2003001d9581a007000400c2e1203141665401403d8070039850014201038981200b001c0c003a020b50403070185a03441c80701e0359480304610321a0395400051882040255144c020224069500a110f136443c0ca501e202d40d440d00d10340e644c0080c4071842c52100f5066070144100421200803800000400020b1a0000e010b0401030800300108010365007600c0c0d5040c0b089950700c4040100b402e0000202c4402076014030302007203418031424132130000c0440c0e002203109519403403006c02169034007080030f01c20b2000d2440b0400c0030500d20f42c0100c084076004480103040d0391100c00c02d480410b250211299109205143c003456504040d130756840194000c1c0d01c54000d00d0828201041e00284031008842140d60038031701000f03068400000240740c044503100700c2e4001c80d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 927147167 1250 927145917 927145931
    0x1d0a20031f0e0132010c020f06120f041a0c180d020a0b09210307140a08121602010e06010504180b0f10240305090c030706080603210d 59
    0x2001420741200501c2515030341d240c20341c1e482c0130984003140212110f41e1406000302101048112030601c048481c031040e034130742a07203802c83c0d420301c803c2460780c818455000c6014440f0401144130b000d0228410718014040c0c111500701842c0c891501c6c104143c05141f0a0161b038200040f4104c01010b5896079902d641361562510a550b002c00d4800341710031006504040e01002c046181c1c20890003c0011107030680340308003007088000d42030344207030444080817055400c10800e00c40456002c1c01c070300110240103403c0d03881c1319680c3c5e50b410b8140d034089020007040c141c00c40100010b01d6602e06149040c4482c3e80024001001c00346501502c60005000e0640f245507640030405086814819260061b50b1100d4501d04608100d0036a0b01c036910121840c800b05503480c8804501401d81c100b00e441c134209014030b0304400c0c24400f00c00340c01800c002080c1000078410076240381c800d50342c03c010410040403681c88a0442d401c054092504003c14807000900d07008520540c1e1040c90008000c84404a000380c800082030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 927148417 1250 927147167 927147211
    0x4020904150e15011401050f090105030c120a05010603114306150f0b03010b1e071208090316020f011e0905030c0901050f12071d0a2003 60
    0x615808a03007041c980b043e10083c4104400c00c42c070f440d0580d030307203180e410390001c2e00c11300111140d00c100040141c41c0c00c0240300168142d4001d0028541003a01080d080d8148200000c9440510104031102c410440c1c5420040100300c3d018811108120b030b030509030a1403d80c0d003a17005020401041e0050700c81000e410398201e081000340c860f54203150ba80395441c6c205d0b40e0103418244054020744600c400000080d103000039002aa101101089a03100108a41142c5c0f03458080d610700c1d044202140c0e8400301410310303001118441c8000748a03080c401c10a0002807442282d00a0051000903d003004d694000c00805007904403156201c84030035030450703154104c1d2100b000103c6500c80e0000a00c2c0c461105c03400f000c554650807240c01c1080d5030b810790444207140510010010214000c0c4140e81e0862010704034a00203050040308800040041000c44001c0c0b03981b0303140d018100640464460f806420703601405030f11580c50065209007154070001c9211040302c90715039209072001511402c02426044101d101d5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 927149667 1250 927148417 927148421
    0x1a18030d0e13270602210421120e010b061603030606140d0209120105100e09010519090314031003020f0a0308030f100801050117060a0c090b180d2105030402090415 72
    0x40b0030740499518030703800840c0c0a86c1d240e21420303201261006076000d00711840311040040d0b03010381c4915568200c4c58001c074480c040020100208000d42075500d07410380017a60b0321a01c008284580c2215040b000760351140c20014102c5005d40c000d4420016031015100c1c61015100664500c0d044031440103a40c5c98800d0001501e5400040d000b00d51075003060100060303001103d0952048890852400f80e00d6600c64844a0880350119682a19096010206219810b81c0d502110459110381481c9060901e14000740d0f0f81c0b600b081324030b41030340308001d0303024030450030855518400040f003510711000140c11641d680083d800000c15941c04c9489110001c2c030203611240000703000f03004a900802480d40c5400000c00d11000880103002280b03d84800301b18403445501c540e80640300150748101c25142008001a02ea61080e041c10212130742e40b0340c860740079540301102407000d544681c00c0d0b03d50626103c4140c2c692034401001840c140a0180100405602c0781d0150b45d0740103910900e8003005488080042d40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 927150917 1250 927149667 927149677
    0x20a030f0506101521060308030106080c27011125120c05060f0d0603060b040b0d02150c0703150b0a12080403080306040e0a050a0c0f1a18030d0e13270602 68
    0x42e4081c01c0a400105201c0d42d4001141038601c142d07685201580c07004100d00341c61007004000651006503102c24400c40120061000cec51940525110300d9181000284a15080351110652034080301c1c1805008c2c21000d010b5100000c060b40206000524410380702c40018500900c14540150b00000750000340b201c0380000c0742c02e07c1240e04010401d1b90745a081c00ea0042203030714a1280500e18280302d00d00e0394504421a092000d500a0000001c4103240d115840344c2e410401d0907617102e00c07854102000007400c2d14020303c1d0a41110800140007424603007003200d0072a855110106001070403008001040c040d50131501901c7e040a1216903c0d04c07107101040041c9608200844680a200078540401c980402d11880407405028034204044d19a09844641042031090210342c41c0f00042101c181c030005c001504002c0121040c81001690030703000f09007008803649001c1d00080c401e0000c0446e916225410000f05110354200304900b0003041c0307400744c03003070f0710b440c8620304204a0700078030300400a943c0c0403a4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 927152167 1250 927150917 927150977
    0x1715010c051605030c063a0f1401050901061209030513060c0309050a050102100b0402090d03090e0903180f03010902130207020307050409230a020a030f05061015 71
    0x96440c20b0525920326800c0ca60b400360b94403d00800d03d0ba501d0526015041d9022802c43c0d2140c00b1815200b20f107807100150b40b220301c80710400500101da034050042403040b11008111483c0218a0410f140440e04901c1016000b5034440c903290750040c09070950021506000c940780d1107000503d102103003411303200703170003080095519890602c50205015601400851010384651074034051583c07907800301310092a181c01a10700591000024250080098110300740100c00900010329100d200c0020032680c00e0b5100080e000304140080802032413048082940c1d01800798009181040b1901d24005000800c01c0d80b803510803c0c2017026620076540c01c1d808104030f6039000b04244c445060201d01400130b500540c00c00e81c0300703000315040025581401d00844404651081c0344120000e0440e94150182c24a14076041d106d200f41d440540058848010520142d07005031031807401c0c91400e2410703c3c034019009200e207072901e01a500800c05180c460079400d1184c1c0c3d8509150003e251514010740241072200811 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 927153417 1250 927152167 927152173
    0x90417030103140f0109081c020c0d02030403030816170712052701110f0c0a0c06080f0106030c0c06050c1204060c030b0613090f060504090c151715010c05 68
    0x1080080d030062280c01100082c2c141e50260b498020000c0c206c4402680182c035640c0b0402c4501d84102844804110701041d46000605180e10940c0340c0e4644103007000300c4e17000f5a2000809009254010540c1a840b0381d071070341c3c0b005c4981c1e0b840301c0060509003a246400c034010069000300702d01034042d044000010503640010040d40c500036414081c10000c5c074015181d110025640d010b040f80040c000c02000401c0c0c49445890411450004141070b40074503409100e81c0a00058040024400d0303101e40001c000380c1e51485040c1c180b609203401c0b51601030340728005040c600f03001d590069800c0500725241582110f00003409581b81019503a40c4c0c4941003c01c200080102c081008100c034bc1d50240740c08064a0382d0801c600b02007130040c0000c912a040c44400000b0011100700084c0b80650051342d030003420783e02c0c081101641c8601207816904003003030840381180c9a0300103000000014000001070419880c0c9000c0d03d03099210310003000040549a05485203602c0ca12a4281c2d00444030807840a5100040f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 927154667 1250 927153417 927153419
    0x90702010b0114040303050301051e09040501141501080609190e0a20151c020f19050f0d05042619050a090608070c020a08030d060b07030203090904170301 68
    0xd00a04000026902140140b9440303102c011000341580c2c1525496102c681c51b41e402c0100b0414800c01d401050045000b01d071000034030548030501c0c004c1c0581e00c01ea00210304e00803951442541c4440003424150300410407503600c0e003c0d071780c010307021900400306481c0441d1a441d86800c00500c6034030052210115802c1c103840380010400042d0144c1c50f24080c041500087c407100d09011139003581d9001056015442c1525802c843c4080402810541c4110882495202c040401d0006a070003841000f40d0310940860840960100b41401707500d204a140b50242c40c044079000b4100c0740380107440d0700d404031550b103400240401041e1218407080307035a4860548001000c2200909042d4012600034842001c100030710b16180780960240c1d03088510f66210302100704e007003080c11501d4180041001c07041116141454001d60ad03480c03003d0002c0d09460010359a2412105411802c4d100d859000c0613500c44200001c4001ca5400700c255104c1d001c003254010b0303803a00d4034107201c04045d000040094240b000000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 927155917 1250 927154667 927154681
    0xa09020c0703110909060103140f190203010f0e0304140d021302091c05070501080702011e061517040f020d0501050906040204060509130602090102030f070b010e010b03160302090d0209 81
    0x1503000704891184014000b103506500c04d1211080c416918001d040d800100181700007045c26030014180c0600c001101d801d810a046d49a10341807420701c00e8541100603d0450082d418280500b14581d69a018140201603001c07003c0f5941c1c2c400e510a110f131440211807650b440381c0da400100003200340c000b0190010700c210144504025880380424078852402400c42d000d074070940f1040c14681a4100001c5c1c1010f0b840c01d001507400c481c000744000f00315507913180ea020380d030440c910018038105424600040c6c0e0904003000c290300390720b4500c0c0032400d21548103081008050b0298140e54042e0f40910b92912412603840824144034135000002d081d9424881008100b544c002940c134826802101c00340b0410303035100d0074091010000d541106451444814040100e4040d40013821100018412a0b00d86694591003482c00e1b0040740d070807109444101e0040184100b215803190261040070a0300d0b185040804002e00c1c9403103d00c4035042415008948250541d45da0368040c414560050440b0700f031454519 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 927157167 1250 927155917 927155923
    0x1303020306010801020a0e090c031504021216090609140d0c0e131203020301081c180f300f0c03020a0902030906160c020d022e020c1c030e0a09020c 65
    0x1b12a540003c0c200c0403444401c0c904807407003900070303405800d27914650740310b11002d00410700018108075081902048900341c908541d42080d8170030110b400f004000d84807a6480202034420319801b1000300b2040001c14071030b103401c540300c1e21f51025049501d0281c40306c6a02d064104903010364000014078400c281040071001c00e520924410511460b85003421061024099003240030a002d0291507a10000700740750300e4900285c5207509442d0740d05090300c035510010209034040c0c2140d04010000720342504208401c108007594000980b0400d80b0901c05600c0f1400d034041c40341031401016001a00001c4540140f0944503104005946c025008500c600d032100320440103584103551150700392062100107002c100709800d080c40d901c5a0340d40c941311070603490b800f0803911190070703d0180d0340030048141954408205080321107010729211900451600c0c1c1c508040d0400700289041801040021441c403601030078141e61524a6074542002c0c0e182c000100013040031003003d500900300c060300c00100035480d54800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 927158273 1106 927157167 927157177
    0x803061e03100207030e09040321020f030a09020118033c0507050a120b010608090c0409150f02090f040e1603030816020f12130302030601080102 64
    0x2140000d007495442d0410b82c00e00c550009001c400c25401c10080c0d91480c0088484524910302903d0103404c00301c110308041c20703110703050400350341c5001d42d0750541c0c00d1401101001070312881e000e00071200504000301c0990115020609041e00c3c0c044071520744007039a512607010751010321001031108419207001800241800014112040c44032201c4420380d20500a80041c007078586800280034406030302d9002800143e103025070409c0071400c1c00b50b40038112480c600d010640c80e500d080e002c60170a1060b01e012039000d8289004001400961482c400c40b05000b54070402018903c02c030341c2c004034820340d07003c1c070b4005503801d80950803494594058a00101e1500a0312559050000d281001081c6500101d0110b000c49090192900310103001007002c601d01d0004002811400d0350711a5601d4100510b070038103410000d441059811004c5560000310750203002c072140c558556551070301039001 = true := by decide +kernel

theorem cover : BRFrame.Cov 926978417 927158273 := by
  have h0 := BRFrame.cov_init 926978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 926978417 ≤ n) (h2 : n < 927158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
