-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4759
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:38:26.046088+00:00
-- url     : https://prove2.me/submissions/f5d82a29-937a-4f68-bfe4-eea51dc96946

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 855755395 ≤ n < 855935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 855756645 1250 855755395 855755429
    0xe01060e0a18170306011e020c0402071b0f0f0b0405090402100e03101e3c0609090b1807120309031a010e070c020a060e0f040c0801050316 61
    0x80c90740d00024420b05a500000340700032040d01d807060900c43e409041d0a007074a001007009103e5800065580c90261802160000520080c1e4000d46900106044520075500001d41c0c2046c071202100700141012140c0c071142045955900820501800c2e21400d2204011008005590090a0141c0301141c5002c2c1112400c1e6031140d00700407a254a00300000140400b45c120080c00361010400d40710700c50347d8a03500003008107100c00058181c00c921500491610305007a000410400401320401c112800e0148090100a0f032180903104c00680d1000100c03a2464106c0019001c00140c02050103140100c40100064590540d00c00503029010145000395104060400000800c040c3d80d010480c02440c0c40e0b42040e4481d07403026406082e03541d40007034004040d401400324130302032030020b5000315a13401d100d040c0c01d5141d40440da04500c50b205860030f12183c3d0410342d007039880e403042c4222084001401001101403025000c0c1801000380281402846695040c07680e62600d07a10b00015a0690140120705003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 855757895 1250 855756645 855756661
    0x102071e020a090b12010e0d1209020d0602130e0a02091302090d08090109170706030e03070b070513120b190204031a130b2d010311041a0604180e01060e 67
    0x428408013036a0002005002c004650708280b054008139134100021b00312812003900d00502c05008500101441032601c504403005030398004035562000d5014002517100c80f001e41c070b25181012a50300060003d2070050410000c0005a8018620310784103c0d00d07155000300c0300e40020101d0103a000c0041d000000c001c1d03204c01046c1818064200c2e01014500a0b02d800d456100002403400c4800b403401c0603510926051201302c0c3c050103001c3c29444402d0040d400d0480c00d840b20410003001074000010700c20b0004211109840d50f0807504081c181030045500d0110644c0f8010134589003c550501548043c0b01c60060609441d00848003169046640307080114407030040481c0000c405048048400c003d110380000146144182d1481a550380100c800c1e482c0b0300c1c5d0010200c8618000081c0301d085a0b4000620000740d14581c561180d01003034030001020f07034080705062103000981201c141d200c03e0100c0c000500c0042c01c80046038902c401c540c1840301815460060b42071b6011806003003a462600000241d0407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 855759145 1250 855757895 855757901
    0x1506061d0103200a0908070b0901020d0c030207170607080606030112142d0606180406051305030c0f010b030a0c061d0406090501030615081e0a0804080102071e020a09 73
    0x5209503a11000402007401c0c50300519600c82c0f5404c001048003e80c00700840c550601c0305c0801456800c8049207440c540800013500e4800c0ca400741d400b40202c04031407000341482003250380050011407600c10034032040d5900c0590313500700032220755000030407040000b04c1504083d0f0559040f500f02c562072001240403641d480740d80410001d11001e092261b9000984215000d20070410303648903280e0401289514180b0041c00c2000060426000e040400444528251000b514990107600200005041e44480000b1040d5440795079001d003081c88081640b400311400420080380c00d00c440002040103103803600070f0584903490040042d0041220344001c0000c54018401414140402c1a0504212524038006070459600340c21800350315586030010300030403076180700d040e09034503009001c0d9210702d140242c055561000ca0390200100501c68032070000c00e0004010034400316900c2000b054569840e01c0905000b50040307a81520000d014250145510003a007400d190f540d41c000d881518000c0c2852842d02c06 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 855760395 1250 855759145 855759161
    0x1a03101109060708120108030301030807020f040f0e01020406030e0625090312050a0305070516120e0409050a0506060a030c06030b06040816060e0a0b04170a050a1506061d0103 77
    0x40e0003003040703803055a601c0d4020f01c100303885003039030315242e00591840c0c10a40c4016040500c890380100014408900004251240e5560456000d200c0c1d08050b0301241c081c1044e100a200414145135888030300002c190050000e481c0c080ea810440d10110b541d8141d91034406848a035401201071207803a0f0b6601c01103110f0a0740c0c0d0514240401d00300c0c0d6030b94407408803014201600c40060030100b40c0320041030303050040c1c40d00f01001d0b141040c1407000c811040206280c4125004069030102041c0030842801034000c00790501008001300f0090300d65090054559492a4044a1600417a00011650b28025a0b403034280c80d00681d00013855401e00b070050307009000003200164024018000003450903004c0140f4210f40082e4107548004528100b0054203a00e4040d110500c0b1f070090401c1809410385035000d070390071103000c802d0000c005009404560b0400b150840094000c2c001c1c5450344042c811003000d140d42080d05200100034075a51000304442c081590b13a64422045010514440c0562107600000c1e0b03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 855761645 1250 855760395 855760421
    0x8070602031003140f0706030608150603010f06090501030c08161401020705100509040c1e080a0e030a110d020601030210120f0c0e01020f0f150a020c010203070c02041a0310 76
    0x90030039241e4840032002c0307200e00400401c581c1710303012040b60040e091180c1c10080125003000e020041c10410066116180910101d020441442c0002c4281e40c00f500320525003079030398100700320b11a01d60100384080c1c1400d02050755044c8510400240b0300c0c5d0001788014841401c0c000710742c2410f080694002007016031036800c0d8110320a0a0000c03510b0303600c8991801644209071103082c0c0c0d5141104c140426030380501c503000240316400b15aa0011400201070324061500744c03502c103c603661411500002801c1040640c4c800d880082803107040581c2041c91200b412052904480749481c3c0d6000c200d030303221400d0200135084480300e031109100e031380503c4443c40071094803840802e1074054481180d00700c4900040e5080004c01c0c030102c1d2941e039601440502941d0714042c0c0074001030100c04007038a566124910354440c14242d1500013802c242083d905032084501c2c0300009545c0e9003460403004061603102e4900741c1c429407820368074119891104020800402003d4007401040b0445010700340280000682c02d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 855762895 1250 855761645 855761671
    0xb03040326040209161e05190503010e010e09120a02031612140c062206060e0402010305010b031009180c030b09071502071a1204150b0105070807060203 67
    0x407514908491001e00020904140300070500d8140104a500b1101902950a401030060b04050a55201044000500304c8134640b41e209213118208035142d228a609011603c0d5103203011560180c0c3c00780046048402c4000c1100360781c1d07281d41665a14510a5030803404560203116900b480600140160042c803d10b40162030901219900f0720041905c0c2354400c0380d5001010950f500c169800191741100e503c0b03401c4e4002c0c20420080c00b01c40e0b9903440a04840144581c040412103240002c1c0301840015502c40c4c400c2c0301c060780e41c0449a03004503080d03600b24042400c00002152030b8030503c0980b8132401c0070820210701c00d854011020010309507030b200c0c0c0b1404444035800a01103940405203000952084400c0d410b5840c000e5011818040c140d007020309800c0c0155000d81265500103508015500c0100c1c0c00c00c011904c1e4000c0154600c107600701e08449030b06110810060003a81181c03280007502c0284180080d12020004407664410384600500008040c090f08012848544c05994029851030b102 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 855764145 1250 855762895 855762917
    0x90c0d1106030a0606030c02120d180f12021014160306210204140103020a031118181c020d031d030f0a0e0117070305100f080307200a0b030403 63
    0x890700992049412030901d94032220200b00683e41481040c000598501c01341440c0084141645002c5c4101c05101c00e042d0f84445030084801100c0c9040612140e020420703c406400307510344040590b20071100100076006a011039800000d09008071042c01c14404100460f175074a040d900501030451403500003c050362488042030701e1404180c10000d000c1158051440e0a240e841003209603004031034545103400e1158010001070f00c58603284000d496011480e8640401041c010600d130803004101070f4450109002072100140015804082816455040d039000c1c0c41142c2155440c200e40c0800100143c0c80101d09466882c0700703610002c0030212552508508c1c080718500c541c42d40c2c000080480d503031000061107070001c581000710030407151000c1c201061100203200d54003131018401080c0005041d2200c00042c1c0348207180c01010301a168690b05412220b84400c1c4841c0e880e08141e07000c17140040130101c03049582e082e800040101c000005c0c001e414481c00c0034040320444d08080d0084090243e404c602e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 855765395 1250 855764145 855764149
    0x603020313020a0f03110a03050303010b030406020d14090607210b0103020d0c09050a0e0412080c0702090403050d0c030e0304170f030a0810090b09070f0207050607080c0114090c0d11 80
    0x11a8000c11400a04130141c9080d41083d080c0709240410091044c9070002042000403404019a03044450349144151070b6501d44c10404064031508512400952902c0d50400d488003078000624021523850084030740366500e0300008c0e13488400c0fa5402d041180d861654401d0789024030740004003c404185009801d25417142c8091040d24951f1000101003001d07410180101d0411020f070200a0000f0312869049061030388511012007040245030040006180010b0800c2042c002180c4100d9400360000c1c202d03140504001348250460f405d08940241000d07440807107507109020303500900729804043e5260a1070019081e0300c01b078a0b040c4503215030054210f50418000144040c0c41c3d8004503454034459403400c0750380d000c009121a0000d16191b071824040d51a10345540c54032690018103424110260741d107180c4113030b1500d20076a0149511101c005982410841507401800703104000310002d20414400c0805160400340c200d41d02d220780d501040305081545031028a2403a00d502030040608940382000c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 855766645 1250 855765395 855765409
    0x510020d15062c011b2102070e0a0b0616060b0102190b010b210c040501030609020412030c080417030c010534050d060303030e1005430224040b01060302031302 70
    0x1029a2a86d141003402c80c10405540c800601e400050f1001c1c2c0900b0703040c028140e88032031015204481c086c1c0d0322516580a0344490040f1220303801e54400400c058081403602e41d01410b80c81c0490b030b00500401d0090041940c0c1860070a2050350700c10700c46034040c0e0030801e1600c06078018403800c1410f00c041814400c0d4006035406002d0080d200000303c15502c1d402d000024094407481d50240300c0403031041008010030340c03007c0c0282e001c1c540c0c5450000c80043d66420094154040c0340c12030b9000d10302400001c11b010718000001d10340b0b512100c0007880b07196140c181240d08001008247c440790700400c091000b51754981c10340a050b4580c1c0d400c0c41800c2c4407072030980c6c03411038200b03400071070210b079690b40310020002c01000342203101264000c0500803032070401080801d400007400401044880d07040c1c00071445810246200b00380e4098039116646016a0701c00079035a008001d9641c56074100e43e040100140c85030382006220399000000852264030b040000c6000b5803004003180f594041381c003e108010384da81c41c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 855767895 1250 855766645 855766697
    0x3c0f05040b090607050304030801050907140a052203170a020703060c090302031c0f0c11090c030f1506030403050d0b03060702010c0905120a0308040510020d15062c01 73
    0x803250001c9290040c030361490071401400880921605104100000c2c1e406a5001d042d1003007551b00c20100e40741c58a058500100108640681c044041100030b107182d407040c0601058104003814245001c039200c18440100e20380e02014144008400b06004400e4002c00205a6601248104c4800640c0c0b501c41d03404135070449c400395000400c039040800c01c0d840c00b002488031741920700d16107030f003000c560b1140500709068902c1e95109100c0050341007024480354070380f41d00c580328010781601a00e10300240c0201325035000301e0b03500350007250010109103094500601e62056001c007802036451038440b92010790381a00311781c000082660300d51480e1319607901c0a0004078040e1610b9000400d030000c00480103000c0d03442c41d400a500420029603101400400014180030380ca4050800b0000b41c0c03100d080c81400c0260b080c0c9003c41349400003400c40010609940607280703c03008400d258a0543d180d40c0c2c21913070316015801240501c3c82d0103030b90400d61640303080002640c480506100c024a41c0740d42e4041c445032154 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 855769145 1250 855767895 855767903
    0x1503060609020d240501080601090e0901050912030f060103110423030c0d080d0e1501150801050d020f040f020c0f0109020301050c070c0312090b19033c0f0504 70
    0x725980920400d140641d28070512091480c01c03000319041e4005000703032134a22450b07041201d4100894681c0e400b80c000300020348000e900400e050310341611514041e20080d2001c4a084c130600e49190042d88113001901d000e0420416074507a503449400044000c0c0441c0304401501841c20003001402910780c1210050949500031805200720300c0101b0075080401a040b000d00032031200340c00100054482c0200c440700d01025900241040c500b01100e440c0c0790605040d20300c095807034400031a101c0402407141c00076141030742c0c075140c140ea20360051049428507107000a40080a0051840c114506600888207d4004450050034010484580c52501c40c9031041142075966800035502541000e00815070f005155261a03840c0611a50f541004a000b500c4050000c070700360000810301a204010180c01040400005610b400c08600c0d00c04080804607455004a490080800c1031841d80000ea106070104512b9990441c0c8401001c1040d10810429544c01c510b0341c80320b48031803260b0319106a40c002d50007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 855770395 1250 855769145 855769147
    0x20a03050601031406240405041104031202010c0804030e360c0901050703050a0908060f0a0c030e030f090a0b1605070e0f01030f080714010e2e150306060902 69
    0x4a01c0001d4100c440002440211500f103d003044196100d071480b10004000c2200c00d0100203003440984503450146801c855403003420a80a080486880d0f8044c1c000c0d05c2c042e1a41d00c640786c6401d00280e088502e40c145050105901000040c04a8001da251004086014140c03100500c0302c0100320410711203c600408001c00510740ba0400104111400c9501101c407540c42c9181c5801100060300a00402c1401010040005000280300e8415035108009240c000222065424440a441c400a10450300046224a4000c0510116209000d22800c2c0d1005001071490501006d218008550000300c0842e000803a4500004000082c10014141501c00358042961415140360544c104036213503216003541c072240402e0280400396146070a044130b6008008500c82091850328800500800030003a25031882007401403103420040d004050703501c03011825200321528254080c1c03268410401418010404540100e00341c0045074084a030f0001c04501e650282c56890351000c0c2900c4854100020701e03a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 855771645 1250 855770395 855770401
    0x124051207030f1401360903020d5310090b09040309091d0312010609170a140a050a08070605070503011410110d08011a030c042304020a0305 62
    0x5552142c4a288042c40080c5501035140083c1079071000741011b00c0c0580a079074400f50412a0782c0c0040e08881149030b40500340241140740c2800b80d201c10101218602103508400d108114417214400c2c0d02003024a141d45503501c03000301034a07100b01c1f001c901301c0000050510480203c240754414000744549036180310301e86100c1c00c100980d025140c14410446c00b51b403524003840300081c0c21008400940e01c400c00001940b0702c0217514112003d0301c2c01200d09882c003000505160420901c2c0f01c141c1030300d21a0300d03600c505540d00c600c42d07100850146243d00507608040001c40000f150a5039000160036682c0c2194814101a00d900c1c0c24080540c5c411904043c0006d1400108007650141a80c00f40c228280a0704542c502030218240d04e002840e014070690401080700d80340b1b40610010741c8080324600498690010f420070240c030301d6a0a0060100d5200c550000c0d541d80f0600a04991007650f00400380307070800d4500640302c85041c12240080c030600131840c036a404036407641d1001d000702d07254035500030503181 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 855772895 1250 855771645 855771671
    0x915010e0d0b180706050307031509020403080c07050907020d030e0a120903030f0306030c0519030803280b0a060809070305030f090907021b0f040204030f05070302090a05012405120703 81
    0xf4004441403500540020070105802605880e44038200b400c002c2128000c0120f2514903aa968011140980c40840c000c014030138004080e10006a500c0c04503400c803030b128000c11000300011940500181c0c416010708200324480d810140d032228040080b0751b03a004440d81c40421410402078140000b07a0032100030000c2c0343d0300840d0040400038900381001100e0454680401811640c040c41c0c2c0110040c0c40c1e000307003d0301121b607404001c5401102e2162242802d58542c101c0814095020b0140f500608050000b42e48071b10074010070b071000400712142c003440e1040598110400a1004500d0f00a0407070000214034148003c1c400e0812a1641c0d59603154000c0812100003c094030500031035203d640030b00c00070001013640745448042160390300701032200716001401030320480c1c0000707080c0001c145000080000000e42081034038402c44800d1103650312200510202c49003441004050f00481c3c0b144083d051880d207240703900148603e090380c5010584003041d49262001e6580c0d0001aa5404c0b100e0164 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 855774145 1250 855772895 855772921
    0xa1b0b1b07050d03151d071d0904060209040609050c160519080415260a11120604060e0c161e0b01050f03010207051c0905100507021e0915010e0d0b 65
    0x1901c0c0408008284006c40848950034020080c800410702561111202d090380001c110b848010500400d00e8156140514107500a9004106c00c18020742c00e0940106900f0603501480340324007003044443e41080501c031301a9600d992000001c0e9410b00540c15454650380c0c2038400c002c0d0b001d00806285554900e01000d2240304008c804290040024460714071501d500311460700c40304240d08100702030843d141d0071004e40c020954040422070003140045c0b868450407801645030f201340740444041040c140d98504600010074229412015002c040101d0070540b4200110401c00382d0280c4d00301010480007440705406c0000149013580da540c18080100001c2c50318211001045200b54000d50611500b540c6103503951000c03002803036840c0680856802180c1c4180c1050000701401000424400c0404002912a501a51042e4000c48151192884824810341400034501000c2c080c54015941d01000c4080050510107145c1040003221621845a490b080c1c01c21070036005121a12030360500010083d98 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 855775395 1250 855774145 855774149
    0x90d030c1709030a020d1e0b01291c1503050c1f02030412020f0405071110021206100c0b0709050f1804171e0a1b0b1b07050d0315 57
    0x114400c10009480b4a84000c102000450b9041c0e42648111a140c901286450345014500000404ea00034902c240700e01c0b0103802d070480d0125031030011403900c4808020962401031001e55002c690411805a0315041002030f6489107851007000940c1031001c4400100300b0721705500954195004034946401d6240251760b083d40d0081800d040e00c006c0048000c00780d12406103100b016102e01072528a0025511010b0111810f030741c008004000034900000060080d40d560f034622070943c40703500405144001c061007203522643c01880e039488103560301d80400c40310340a00110310303040082c641c2c05840000c0b029421240524026102c0b0a00c190526081c0a1801c040079940b81c070a10058058010402c0055020ac3e08150010f81c950600002c00317622885510598000e90480807030450240ca02580304806000c4000305540d809140c00389801e2074029010302e14601038a558208800308110110b82c01c6032220b204040301c44070f414200c0d20340340d8038201410300b00d40601180e102d51010794420b040c4250100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 855776645 1250 855775395 855775433
    0x180207060b030c0f1e0d06051806010608040803070201020c070e01090c1404030605091e07031203051902090301090b0c0703091e031104020c0f0a050d0e0f1005090d030c 74
    0x28502c3c03400300244801400150642c042c0d001c0d8074030b1111440805240e013202000180182007002d03080e150503c0142021582d02c0201c40c146c0b100c0d42c6568002240c402d04031502640d503100c0d140c03a991540c0d912640042e0501c3d09640d0300b0045540400c04c184459001004480022101076241c403410f107041e01d40300a0082d0401010f4800001c40d10341d4a8280c80681c4d07001f0000240680d6040101880d14807101c0003528045000451140c2c400030005009044d00d20564107a89941015003064080d5407060380d0080c6a0384803511480c04504896000d0400701e1401130004c18400866200e106064000b07480c110320841c80012a00107258001c61180000c1210509092441170445c0d651800c60f001400020107001600011025036911070f010b80d440c000d4134009440321444901020350f990b4400103000c907428001c207048140c4160007030410b2982e20b02c0c05000e12420925260402070301244000500c0309001c82032004030314a0b1140800304600314442d40b00d6000306215401c01200c40011241404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 855777895 1250 855776645 855776653
    0x180b1e060a0305031803010212010803040603181e021302070c090606020c091f0306110705010e0327060705150a0f09030f030209040e0613030912050307020118180207060b03 76
    0x18000011240c0089001d04401545c0f401c1e070b400030303000e8030401600b4000c0410003800410303d01c1c0080f0090040b40c0c8552020800c040d0102803400d544c1c3d50003800603111001c103c443d0035140405000010816100615003484803450554440880c0c004c1c030700594042240c0311082c040c2c00842d00c20312000e0145070000b00745407500100000c078100d6000704a0000e15010b688130012100c030b03c0840c3d001079a40214140b216040780c0190340e2494010300400d5030749600741179421204030b80c04000c80d8151640045640c0c541c40c40c03601041e0b9584901106e084d0000410400c08002ca8020300402e03100e1034a50300c60307600c0c42c201080c280040d9410400031000300b030720f0020400002600400c03041c0100150782005601c50900500250040212449894017401030031304001e4a400307403200d041c80e014800d0710340c500c0761038903404100720b003684450000740544c0c020003842015600642e09880c50b51079040c0040c002c191506811418122680c290011880e00032911700100070050107801c3c4102c0c1e042d0300074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 855779145 1250 855777895 855777899
    0xe09010939110a0f150605060a030b031b0307060e120102070302060603100509060f04050a05070612230114061b030a090b03101701060e0408030f060a18180b1e060a 72
    0x40342d11a8598000401002d10742c007002102484c2031b0814001840002c0c02e02e511070084983c06030142c4140f884c0340d8441d00035020b821540c103c00700b40c0c110718200043c0c014035020341002c03c00d4550b2909a440309a003e11545001c10b000b200900050040c14480e0303001e001607040c80001d261400c200c446080d848207080c101009100c45c8001059035000008820300f82c032645480c10040e003005c45240c8046e010b0b024503100800c82c285c00c090b4010106c1101042006002e4100d80c0f0020032528440d80640b4104100c00100101329610304e050300380c49401440d440c5000c2400082015941c4c4401c1d803417140d90000300702107d060350418000801464811102e80c42e51074500d00c0308081010a00411205103e0700c42c02d40e242580c00d5000301c1c042c0c20358440c0317403566080070f01b00314005030000c95801040b4a8000002403550811203d98011190001c2c0c00f01c80300307031401c14410090441500740120409031140c101010644010506006042d85020a403080305552400500c0820080c0000d0007407581c8081 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 855780395 1250 855779145 855779153
    0x1110110d0e19020904080f0a020c011d090c0307031407030c0e0f01080f0c040b0a021b040c02060408180d060b0405070305070e060d0b0409051b010e09010939110a 71
    0x1203410103604a60f0204c80740d48525040b80103004072180a00840c1001c01c2440d0441c0d00001c840111000036201e048241a0390700307038007020244804d041c507006042800401c403000e507810301454104e000c90802081400c64000c1200f0358420032075107680040e45609170340c00c0c82500302c000801c143e80240d40e00e415840c0d1080021b00429000b510000410502e04005002081c0d81c8041c0c0d0050b100c1c20040c0342c0e5607030510b40020364840941000c100541c0307140810700c1c50391900d486040d516441980103480c01c1d60321503e9881e032a0704003140c002481c042211001c0703043e43c0d680444400c0709200349000183e403240001444201c59008000c0805c4c507240c2820f001581c1c0e0082c22000304440c04075401d555030703031070b02c2c0700c940c041c040c0021415001410016640100100030511450340800c1e041d16404e1040b410004544005070300c0c080c207070849030840050141188540000034101c000c5001c2c80c011f5104400344481c500c042c5011506074000c4040545101680301c0001c03109510180d000301207450303903510307 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 855781645 1250 855780395 855780433
    0x50a030c08060f0f0f031b0112050106020c0d0c03061b08100e01120201020a02031b030f03120106050a170c1305010e06032a04080106090b0102010504030e011110110d0e 74
    0xc0d03044c0c41142d050716078001c181e8070a00d103070f402c003c400b406803443d980a560400c0030405801c400c540c04a9204028403142503c40d10415040f103810b036004046810400c01400010b450300c50341541c642c1c0d1414000700100e4902d00a004480500c0802803000709450340c4003d0610f080034105000a07161110100031890030013031401d041d034a11050010041c0e486d440140c5c075080c042500250107000300007a500c00f000706040003000400007501540c2e1a810300405080d100c1c0714501300202c0c00000c1038018800b082c45107000c1d1503000f0782410f16000c2520059109051104101d40a81c110784d00042d50a400346111a0f148004000a0801202000113040020400d02006160088501007455003a940c4001d91b502500c52076171805034140e40c3d54540c403082e400303030081d40106864a828040500469441481502e01c40e94066407140b000801000c01119131180041c252440351090130003030b072180a070511414214104c0b0300c803140d641e1800504503c081e0355880c5080032054000c981d00040502010b4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 855782895 1250 855781645 855781669
    0x151203120c03060f10141308061806060a060207060509060c06090c030d0c0f06050402030a08042409141210060603021308060408030a09031b0b09070e0903040b0c1903050a030c0806 79
    0x111b1241d100d100361200d07100d0005c0594412030491080c0d205209454820940044090596005a0f462561141c0510480354054031816006900c641003c05c0000c0c4284080c0207c1d6400a21480c50f0420605c01e45261278007c0e40d0a6006400c180711801c41031600f04040d1010249504200000c0728047d11014504c131004a00503000d1364450001408664060040b800305550007a042c1e5203590722160091144800843c1403400e0310340040c00b034140075020300012401c9404074281e41440609074014030031301030306290f000c0001d841040714400c00c4070290b001d050b0242c02d4558006031a100c20015003000c69810f0382c45511503410020900c008203c0c08401c81f54404450a0f000c1200061031030210307a0b01d1011409050400100e86000d01013101811026000c0c440c024100c1d40040d03100d10340841d0200741510610701761b03802044100006040d0802074201e482080056600900580f00c41594020580030200c0025034009081c20031950588219260800180791064092420030b0103e80c03845001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 855784145 1250 855782895 855782927
    0x3030c021516050702040f24080a0f02060c07051c03080f100b0c0c040c080f1b0d0c020106050a08150a0504030921060905030307020f06151203120c03060f10 69
    0x3405500307541b202c0c0c0202c0b0002078194001c0040f2080c405070369038541c5075400d4211981e2a4003e000071446400654460340700c4d000782d2568207200307403503080116503481070320114203c2c0202000010a9075820700080030310403240c50420210307a00d51170018413105006200e0303034400300201d090210301c00810240200b502c2c0100078460b5507041e4003484030b10b06a0310808165025041902400080307a0000d805130207915444019202511101c0c804407900f40d103c40c0e0050518810300401040020380e401c090040c005078000082c0382503c030300c081803c02040340c0095001754491002000c0010700c40084a80c040d8808804104508160741c00420812480c46a040984031a107580051005503031400d100c59903001104206110710362820b00e44941044411b68054020501010700c5510007051452249141241c42402102c0244c2003046512026901000d02c2c032003440180d0200d01040780700e6011300400050640c6920740311080151410007803c2c0c203030154090380f00b00035509410400d403101590113 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 855785395 1250 855784145 855784147
    0x50706050310030803190c0e011d0607050604050109021f0504181e1a01050906121008120c060c040305062815090c080606071e0f03030c02151605 64
    0x4402c1505500c1070190406801a03800100b480b014201c459080b004d903560ba15400e10906030110341c2910014040d02c941c6010851054071070500900c030011490210000078411424076505464940c600042107608542985d0f68010900c10340ca440610a05241300c0e203280c100755945c1340780006200303008a10801081e020b002ca82850f01107441e410900340041c01c082000071610b90000050007410342000800500c080b04001450b9075440f540440700103400260141d851b24842d40640c1c21540c400400d402c0360348550b1440440c8031340003407110750000007100b1001030312011a40401c40c202040074000d0108034004001c00c1001890110301c403a841210041c4541c00d0700030005000884100440d201c000c1180f5050345103000c81c2c1d9050004050b180d051200b00030310802040103803203508060b261298081000e120f044001800e0b603541d41c2c200002024002201c0a440d0707120507084040c80d00c00c40101740c8407a081901c4650421000040c0211020030490905180c04071960400080d1190703010800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 855786645 1250 855785395 855785401
    0x15080a03050d18030f031505031213032901080106060839040e0a02090619020a20130c09060c0201020c0604090519091a060f040c08061305040507060503 67
    0x50560320140300341410b0f03030000a01c0f201c21301d4024802c0d0001d468400110380b0f418034440c000284d00403800c0540c0d00280c002c0040741440f0203590b040742c001031036a05101e08150320120020300700701481481000103140100303251a003458030b2a40c818050f00311000c0c0c1c2c0e24200c4200205580079005035000b14030000801451144180071485c0e401e080503404c4030459002c3e10303941008409500800c11150405490342840c0c036000c48001c10b074460040314a900080c18841803050080d1400c88902008181c012121401c81c26a900b1310b80f0000070074200380c80300e14032050030170a04200b43c0e10320b80007a540c003080200c040d075028017402e0400076014a1040003070740e01080085900811079600d985200810b9a030b1966070301c07100180a81000c8030003011503081600b0b110715003002c0c6c1c00b0790004240c3c4009510052111110341c8402440020440c95010800601c100c3c81c988440c4a800041e9038035942d180820b02d004014040e000201c4940603100070b1400d010030012400c00724135001074030110710b04269251 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 855787895 1250 855786645 855786667
    0x801020a09150813060b0a180608060f041202070f0f030c0504020304020d0b0a0e010905060103030e030d0c0b06061603080103050c1e040c0216080a1214090906031e030d15080a0305 79
    0x11b0fa1900b0a07041104000d003c504403c4030b2800c0e01c0700002040b03081c80740d6074464901c0c948a00059691004c030101540c04580000c01d0011852840322041c41103c01c402e03503031001c0045458040d40718405c101134170305c030034010b001c0c0c41078001024142c20ba400754034604040e404908030b411840c101410718403481c3c02244260019400030b52141e0031a0000307015071005800e009860b90802c2c0b1049022502c501041c10b51820046810004001151581e448801a580ba0800701c070320024005039015004000150382285240c501300b510074003d6440201c650b0440c07602629100c000700c00144a111492481701c0c9201c141c4090022845041c0c601080c400c40660099180c001c0350740e020a420800700e28013013544000014080d00f840d000302c041640c1d542c0031443c01c1e2650490010940400e100030096441c035801e0202205410100241c101d41001000a1103862030b0a02c024407074145410000310b200911380d050041e000414501403140e40400d03d171440030396540c0b110000003024000041b480c034101e1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 855789145 1250 855787895 855787901
    0xc04210602041508251202031b030915071b1511040b12010501030b10210509031812030301031b03080f091e100c05160801020a0915081306 61
    0x40c00c1d200341d1410f608803084005010400211024003000250301581c00241da2204038100415003241c5800388003000034900003010b51300c02852600c24114000c0c182042243c0e1600840c460151400074041c0403c0e2003040d9a141c600c098450020081107230010725607044250740d03c6000700c0e400100c1100800c5000800d034090039099080400110001c28005601c20362b10300142211801c40e18080f01d42ea899000642c100e0301191860761b040155044d01002c001d000355401c00070340e200904840c4088204401d0607040e80c070b08940600541d04040780b8201c1c0c041a0307809080c421031044502c2c06440da001c0143c150b407800144000f4003000c404607241c40752261004500001746401208545ea00c060302040e03440c1c6d960068002a001342d005107050280e0007400680b001c8800c0303000305036038544280603604a99020320041e0545480c010050321003407031050458008000c10040f0000740e103840b180701c0003078403506850340f041001110415008d00900d600c00015030340f0490326540c86101c00250f08020f002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 855790395 1250 855789145 855789149
    0x1031a1905031615180b0c0c040c031b0903050a0602031803070302061012050606040b1203130302030616050a08150402070c0f150804021c0f12080c0421060204 70
    0x243c001c01151003400e0034150151400d403606450790782403680004404441241d401540301e881080044018440522000f00510741d00012104a4040703100410005084541c1d25000c6800319139100068840016044130510145c815400e21b40317021465134403060f44451007158010f0807658004001031105070b000380550000c4240b48116910f550403850041d6031058142c0342c0c101c1c190829600001c0104041e05204815940301024101c151922024040900100d201d07460380911228200d500810b0b0070409010100b4003401050b08052a600501d810701e4406030040c091100390780041012180c010b011903944150a2801c2246991681102d00354681075501c420340c0310b03000003000814800d11810000c142c4007c40e44111465030303140c80010b03144c1249109d1901003445000080c0c05441d110001c40340c41240b0a01500c1011065682d84444507442c54040b1074000594141c41001984202419030102c40c03819901e15090406c0e8004001400c2c070010740380c000341c0700088a410400141c0540780 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 855791645 1250 855790395 855790399
    0x1306051e0c0d09150e0601090509030703080c16050a060b01050c030a1107090203010308120c09030c04090c08030301030c0303180f120512161e0c0b0d020f0f0304020f01031a1905 78
    0x2402014001c4c0380c0c0e002d03028840c1c0311a45131080c50b00105130240903200d030350700541c19040103529103040c643e010740754458018540c083e440410710006500c280e9040c10300d1482d0784100080c0480302d40314980706c01101d4070b401c60581000b0b170078060322401120020071590158403c0c00d018000d0030700c02006d41e03c1d15141d60460019540044000001c001400c0043c01c0b1040c0c4100402c062644c42082c4580180180700da1f07a030f410382c891a000000790602e640104040750040082041c0c454540003420b00e0f5500aa1080300c034800c03801010810305510100e030300c426144001214441030b1420b4441c00400c0c580c0e01500c94123100e038410306401c000e0208141580240f1506002d91510035290540e101d07046410320a5840c40740c0792180c50012813072024024002d40d8030149010780f460400186080c242c110300041c1141d268200801d480000340640a0000c0020707030840160b40e80740074414410b600e0b9050f01d26505041c200803c10042610041c0070044002d010368403045208031750400180e40c0409540040e0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 855792895 1250 855791645 855791663
    0x70909030903024b0d02060f13080703051606030902090a11070b160905061e0a1704060204050a08010207050a061e050c030106090608010e06011809051306051e0c0d09 73
    0x110301908850b812500c990307480070840741301000640611908442c00c02e4020f5100b80200001c4040d0716200025101083c4044210708083d0f44030700c0d526180100d6070304107894a80c800c17018074510790500380c0844080d018520342031016404544c0030840d00c0e070000d0040b0381d4139526104003244015410f000e4403407164200e40c0220041c205680c503900034401c00a426400a21201d0010075a4208001100d0100ea20b141d50180140500c20320b9038441d0f040032104d0820031200c3d8004084040040d10b009009900a600042e911441c0508014060103280d110306451307401440301c9400b00c7e0000c81c00d05c0005401c0703240401c03100c0088958540301c50000c89000300140ca030034207010300c1d030140b02c01441c1691a0382e2550284161502000e03580700c0000d11a50700078004c072200080311035110760450f2207800c14004c0000d54103615000c100090740ca04641010324042c071040e0300340501900380911a04039203800c1070f0a424400a90100302c84000081480c0080311000801040110140d0301507000d1a8000f8a03138 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 855794145 1250 855792895 855792979
    0xe13060f060e010803130e040221010b04051308070f0c050a060203090306091501060f0915020109020a14010c030c081b0604050709110405100210061707090903090302 73
    0xe2401024140690840d8202e81e500200702d204000007110000b02d0058544a01c1c18940254030148080c020012600300d541000c0301041d012a4a60a4a4030000540041118031510007070000f110002002c0140d002a16509000440c26950841d1081a000b4802c10880ca1041c10415200141c9500103a0828480310001607582d0740071010b0042004105c00380c4880ba01d9031309009035100200f0f10010118035150004002b52030050240030040e951601300740b40140d984002d2020b0401e804100d24016175100c10311039045180c00001d01d005800000c2400300030208400000301b008911601c0203044c00041c4000c034003800301d642d00b078404204800c9018204925014031140c0c07142c0e803c2d030301110b651240707000100f040c942c40d0050321040580be031030240c20715281204000030142c100f04c400c2d080d400b810090040414490080d007000d010031b201d2200405031044040e92500000754020b00c031003441c2009a400180c8e00204080840e6011981c0c0c03000c03629030400000441038810702c0c4202502e0003d0039 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 855795395 1250 855794145 855794171
    0xc020106151205130c05010507061401150e012c0316080a0312110f0d0b190815010b0d02090a0906060c060615081801090515100b04030c0e1306 63
    0x951000b94120301824009a25015050b0110414504d00146006405c4000348002d52185000d4980343d400307208041561010804244022142a0010111050100802d05029800c40c548038400b10b400c0c81c00101550605620840202d4061189082000312000401e0382c4d81d010030088200b189101941c1707240e56500d40d42199592012001140401c0c140c0e0200c040c414070710300c02c5840800741d0807005443c2c07500e018803070501d560050502000981c0d4640c00764100b900c1d500f00400c402034021030038007178841c1820041071806041d2034940e6507518102006104141441064446803200c0d011b01586658400340007034600602900a0460b10b498100002059a404401d40e68424010720b07041000f10744030300c10380002c490340c10300c0400802c603008080b55911441c0051011802c00020001540b001c1a0780e07990304090216a031410444031200c00c0c403c880382114458001444040300c4140f40520755501c40041c8100c41c8654003000100c6000200c049041107040001241d000c101008601c0640c01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 855796645 1250 855795395 855795407
    0x309010b010311041d25020a1e030e06131703070201030b041b1808030f030a0605040501060813080904050103060c0806031b0607081b0604060c0203090a06030c02010615 74
    0x35480380002d0602c0f5010071010601070450f07041d100e201401c034800c031058140c400c3d500c041c040c140c000407150b2001441d0038202c8003100c5115007a410f41c0034000c4041d40e4285100c03449403661420041c03007464901000041e8008800402080054680c40e444610809100c450124168092200b07074040c80149000070710040000c02c140c0c1d100341c82c20440e108505040c001201d084d5041e802c0f50324129030fa09111240030790042d40504111249429043d0703101c2c02001e00b55004002c1d424800d20000c07041c024141c10318049d11000e000150707401c202c00d40c500600100302800180c02500d51140d18140c000601001808842041c10080d005203e20350396807808000411600c0300d4480003c88031000300c1e40c6481c0100c0c3c1003a8640040b00b5090103800000200840c0341c3c0503000072500b80e081008001d002d4030311400030300c1c2d0b00c1c0c10391790142443c4d14040c10a4410748000080c2401190030402c241c40d0950759501401c000e41e04240340c00110b400560700280d0060030b813034100035440380b0391076100c5e048182d01c46 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 855797895 1250 855796645 855796661
    0x303091b060c0516030b0105010c2301060302240717041a12280b04020706090f02030d050717090d05060c03181605150d050a0504120807120509070b030901 68
    0xf408440401075600e00d018036200c211300000700104556001002150300c60103108005034041c0510310000c80700a074400701c9020f014411500306035102c1c1800c000f5803500c8a19069482c1c070103030000179008009400001c0611801f0f1004065a900f4541d4a10030b460301c8007514080d0855030413148058031640e00d11030702c0d50070880d01c5105c801310160010b8203000c14190001148103842e0720602d00002c40c41d11080150080f0b0501c65041513090242c1c0703022660b0b034001c640740c090281c04800c3c01d4810324018141030964580303006c420303c2403c002e041d0004050540442850081d4218107450320b01200001c0e50071111140d016010b440340130240684c14900000450194030000b805540c0c0d1281040b8403500d6040e007460402d00703a00f142000300518144080301052208030907549618050500381c8140c12250190f40408003c1d54500070403003040000d511210903254142044110ba280c50032006002c075107120b1203190000d45170400324104030340401169000e45000c4118580300d01c0c120390810b008103111 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 855799145 1250 855797895 855797903
    0x605120316061503080c010f0b010c02030d0e130f02041a0309060109051005030a110f0a1d041704060905030105061c0f0201110a1a010f050a1e211101050310030303091b060c 76
    0x10801c0a09c0d40c040c4244404c0241e01401600d08044bc0f14010746540401c400035503013080111064814032039680c030a002c01c80c11032071001a105d504190780f070f0303c2242c2d0480d000b059058041050240ca08000100d290441d00039000104140d03495202c0030204100681c0000d0700b500c20944140300b04000712405100c2c45d0000d4a4401042d55a002003209a243d00d1258580c1c0e01d1402d050601804180118180d01501030150640d05450040581107558401c3d41b09400144102c8030510191030300303004940e0441421107a403c04d16035140f02c01c807116406078034018103005a0140280859001d0380110400c00740030420b590026030305080c40002000301001c459000c0c86140c0001c00c020012581c810306541003c2c00c0310580504113840b843d5460034280454640f03920040780000c80d4001e00d4150a9aa041d40090411118041c5014100e50b038441c90300b141404024001c00001c01c8961810404903500f40c40c0c04600319800d41060704040340d8084011604082c51840402c026400681d0503003d544a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 855800395 1250 855799145 855799151
    0x103090c03060203240f0616051e06070e060306061c180203071205060f040c030f140115080d27121a04030c2405010305010605120316061503080c010f 66
    0x184580c1e60b005c40482c001c40d154041c1c1134022108003810000c028040358540d0302620f01c03840381c403034403034610f80640419164074000e071201c08a11001414040160010b0090400d0100400300c1030019070280001001c080c06a5004110034101a24907c1840c500040c0c414041042c440342ea840c42e5403188840100303070300030300c2450340008010b05801904100150060080c0074503854040e819000301c800500140c40049403004003101040e50303801109000c5102c2c080f806100f40c02d1600032429182c0103260310b00c00c4010706104001a58010492500e034880b5403409217030700c80e03409c0000340c020049504400464404400f0209920701a4550b9582490140d1000f40030405454030f4a07004a8044400400041000700200000f45d14501810ba586c40c01c40d01c1d8084450154a0074001c9038000d82c03003501c0a80d100c490410a83c1090701c00b00002c00000f401843c50140440245e00090005d820028940d954403010791a01d50310071440072000d150710881c0740341d88000d5000c0083c068844241c900076070720700d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 855801645 1250 855800395 855800431
    0x90209011403041203090f150f050906130602030901020f18150403030509040507171603051501080c09190b030f060a1d0604020c030d0e07090c050313020103090c03060203 75
    0x41c00c01941e200b65809000018440030003181140906a11075085170340fa500c00c2e41e8a000103130204503842c6e1211040034006903270310000d40c1e010103480019204c143c1c240c202400340314404214121032020a500110007599940390464418020302c112541d04816546c04181c08001d280500c48295080c20704071200141c0d0f00d280c1c2a074196501c624400180400e804210064503400d0540000751f105296090404007014038415007a01500d045407100c2904003079042d012000c94151140355000f140020764141d002c0d08610000e0f022040242c1781340400480442d00703404035910003109084c441921603004212950b40d1092400f160030980d0541640314251b400190603050800c0030908803424503448500a00c2130740f50030400c001024201c140c00c640c08000c603100e1008204000e20f20400b5828000416940c0b0107000c40c00c082c0f150f081070084ca0b0401550210f16548001682c1c1c005841c420280103404242c801600180030040d4010280000814000103010455011350b107d55440072140381450 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 855802895 1250 855801645 855801677
    0xe010f090914010320030307062a121104050105090d050109170c010c0c1a0718080c040516090e070903051f1b0f0c081e040602101b0c03030f0609020901 67
    0x60143d0340e5854050b401440103101107400e0703810610324010700ac1d01041c0048020041c914012141301001804201e502403842145003041c031171001c11180c03c4445608040c10f00000030070502c035092481384100e2800207147d083c04001e41c0420800e1303600c402081c03845100d080182c0c200d40c1058000c0e151319440c2c04c402080d400c2c064040000d6290344400359107403034512100318801c038180203440c4e0001c105200300002c20315004036240b4000303000e44000411100300c8460410041d01e00003800d410448003074444502d400713078120300701d02e0907501303c103207021681c0d0f407600030460324084958400340041c800d400032411648041d6a481d4003110481d20240034403440400345090f5444103900070f034001400200b082102e28802d805400640344641e020614000042c03051090714083c801c01d1501314500081e00304030040c0c0401100840d01c1c44088180700980303c0d42c05103071641c036290a11205004044009808143c401d07440b03160a1030b00342c00c1c2089029100e482c000001c2d000451820f0216180684641d40c0d6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 855804145 1250 855802895 855802943
    0x30c0f1e010b0310020f0d0e0f01150e06100c150b0411070507030311010902131a0909030d0209010c080a030506130e07181104030302030706050c07030e010f0909140103 74
    0x3090103002013184214901c03511000354080a848420200c0c1402848210f1810703029030400c0c419500d0080c002560048501800c4501e0030311281040c18101d0381c10404407000954a0b5404001100d2a0310001c105040c1900e140c80102d40092110542082c6506a141d02d9803040410900c103035000c0080d00802c00c05c046061090441c041d005a000b41030400001c2d2098151791066448a000400e0030030056000c200743d103034803481c1c0304812074841032848900c1c401d1300d42410b503210701110024558205410095103e215645080300c540360000340021559011b210104006640310030300c940d842189140c020000c10056a01c0c52103494207801c0a1043c0c500760045400c4402c1a4000c2e1185514000c41c035080c1c00c181990604080e03468204940040b0300a101a0008501130303009165207010b03038504841101c00040c000310050b40188141d001003503012000380309042c000c0c00c0c06580020080400d032241e0701c00b80d06c2481c41606042520607581076030001d03075040341e100701400815180c40c46850400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 855805395 1250 855804145 855804161
    0xc0108060f3613031d270414071d0411120d031406060a0c020a09090b07020d0504030804052116091d06070c06110a030203160c030f11030c0f1e01 64
    0x285800c150041d02d07090f1003440c08183c1c0c0d004102086d0003400b0040c0c1991b4440c80e10b500800440032108100a202900388115180c0040d500905130050422200c0d24050a601c1ca04003242c40103580010304101d0044501c4643e1034004124400ea58495202d00b5690503e2100702d2001034101221001109404a029400f5100040081c0e0034007000840460b403000c2d0352003050ba07005545610009098200388900d4040030f0140740001d15900c1c100c031f4017038034005030198000100f0108006c1040418109070945040c0c510031141c620442442060400105401c02c56483c8180182c90380b81400b0320048140000b143c07641602401038188640c7d40340b000540c0c00c02600c095800c0003002032005449544e998800034851040010301401c2240040c5003600b00034070203004030f980001405100c040040340d11039414107a241c802114106550300504030000304901e40f0500003a461030295680003801610f0040c2c1d060b5040362150328603a880310740da0f2101c108140f5804083c031295100c8000c010301807501 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 855806645 1250 855805395 855805397
    0xf05010b100509040905010204030b09071706042609030f0105010807062d020f190213021c0b0303070602070804050901050303030f011211091f080c0108060f361303 72
    0x401d02c3d50308402d020250509880c00c0b20255801c200200c000b600414066010391714038030043c049030341003844c069100100c80840b550140d002500708000181503151a100d418003d00e03680c1040620803a801105006011209505001e00c0581242d40c0c44150702050403210300c003040301e10059a4101c1a241d030b181c90007951004e8216120405202c0003001c02c89000351303049104842880220303c0d82c4504100c44c030040401ca290001c00c0c0360095181c82c0c40c0700403241158a40441c03411306074030040e04000d03100345e810079482c070740b941c0d00014140d6041c015152038a411100555840c00680342c24a40d079440350103900c1c811921030b0000310303950030f00009580c400c6002868602c07090742445211b014203d0460821900060043c04d845d980743c48951704030740074010b8100d0801c45604800301c0d26080c0d03441c58100c40b020b5070054200d000141c0e44002c3d07441e0400ca0554840000801081c04500c0d000c41e4085150707080b03000512002444400c040d0800b0341e0a58603401901c0310340781e04400800c0c801d00f0507400741c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 855807895 1250 855806645 855806647
    0xa1209140405060a03150509071508131e0305091c0525050414071205130201080a0f020307020a050f1504110d05060a0e1b010f051803010203040f05010b1005 69
    0x11a1078106540300300c0c1c00c984000c0c8115580340e680d640b866100d4113503407030744100d041c4c07076500f4401c808000f005100042d12414071001014001400001c048080007000d03403000b4400c0c41080000d03c401d01034841c2c024800c010040415a0079410058103580c40400d00c18066004101107000480010601c49000c69015015141441024098411101034808910f2601000d03400008565a0790701c1118860180da400031000707440c250002822222980f204900318508181c20404403650f041543c0307064960909110300584c4503607222200030238101d2101d50001c0e10010921220907000142d1000040c4a84100e9680042e4003989070344a40c45400285101101880410000b844003510070907a24030140109a03072500a499992600f4000d6400c4c8441a0780c4410746035620b5403e0180b0016000d5511480540101d003000080c0034604010f2060208039001c40d0964405800500050a102c0014025520b90400e81803c400c00c1803041070403151907280c01009581d41c2000401c8444c0404107445003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 855809145 1250 855807895 855807929
    0xb0a03053f03160e0a0306140a27050321010e090f0601140d050610060e030307020d1e0c06080a050a14010302013209150316030f1d0a1209 61
    0x303001024072941d02d4206000500444d8516500c5103510180154002d141c0880c200c14401003001001c0005005141d0f501d04088030f0501c010905944155072040007210540b81c4600c506085085009112012046619061060704075407180d00d0382d5410f80b00c481508001588980d0101b9650b03a602100d5000c242e00420010042c0181c0c000808601c03100c05491942c0700e9003942d503078070304140c0e0883c0d940c480b01c040000180003059210f480707858824401c1c0c0040d0300e008004e40001d1039480004500400710603540905441d035a624030701c40c400031603005024180071744d190503025012050445141c183c880c45c0a00050510200380115082d40c5c0070b036005d0660590a540044490b8240302000703d9204a40d00700444803000005050100d54a4080c3c5241e15103524901301301d04102c039116800b90300b11091051002c0e04d00c2001c071402500d1100c1c10001001401000d59101501400e0301583c5046450000c4c00440107000c2840b603956071055401050741d10f800103003a550223081d401000f008200010075 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 855810395 1250 855809145 855809161
    0x130314062d0a0c120207050607021002070512030a0b0a03060501030308060406060f180f06020a150905190c09020c030901030e01051e04060f0507020a0c08030405060d0b0a03053f03 79
    0x6590f56410352500c1c090758515014040107036030000ca401c0741c195100504008030150f0620025980400180082d0700c3c04642c0e84400750344540c80124220801e0b000404103038081c5c182e51000c4119000500803100e4940d40c2d00707018004220034401500414900c030f0005060b45454800d030015a40d040d12410148040c0000407030f00105d1070080c021400694200100e03820355a445042e0050425034004d0051200e1403605060306002e09081d01c0016040811301c6000410115100492000c80c280c1c10300d280e1030301c1c100200e400c859544207142d56440028920311142022004010b40d60f001e0b01d00340094a8140e01c040e00700c52003120100607030010303440d51a013520003d4000c290824021800440c000d1480c104041c201c0d10305941320005030740088541d0040103001e03001d540080007204051410b003842c020201c0e07500c1c41840e0712450074a554003040b9583c1e5a03400750706800386401c07100300c850300454803490801034903800c020305580e0010540c1d07800c0c180942e2000840b10011806c101e0f4107513200c1c03d503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 855811645 1250 855810395 855810401
    0xe13152c070813230c060a0906080a020708030a230106080601050705030d0e0a2604090c05130603020405030f0102090d1b120b0a050c03040215130314062d0a 69
    0x510380340300200b0311800303010400c0c100407008a030b0f820404028540e0500a03070146018170604020340903100a1203440c0c40b4a4104a40004603000c2e81001c0d006030340c4c0c607811305c00244641f042c0140f12400200034468401d281d82d000201e501c0301d070100100400d20901c141080118248203c100042c03200d4002949940f203a00a44000340c881c50131a810071220401410680c0c402c0848100f9541c840d031055030500c00d4081802c404803140d114500100c3c0380c1c1080304410b6100d00d000e0207035400e0300d036081071510303502c03900840d5410308103801c0161119456500c0200650b000d80b050621a208403008800c844106100719020000000d00e0390740241080c1c1e0700c040110f00090100749a040200c0d40c009109045108420b90051042004004a10b8201c1c01c40d8120340300034100001c0c0207002c0c000c00c00141c0f9016503600f0000225602c46456034900c16018200c0740741600010305803640c421041c401080d00048090182c480804140400c03400c95091038000b0020b280500040000b0001040a94207035034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 855812895 1250 855811645 855811651
    0x2612190e0904110406050d0f0b06010809070311220903020c030712171c020307090f03020d0224040303030204080105130c1a0706020a020c0307051f0e13152c0708 71
    0xc1c0c00856203a0b9242d00180311800451f0701910b0004404a04404106883c860550320140c03d080c200903509040360010f0392643c083c0001000c4540c030391080c00326a580c044042d15000b0b400f1559001d00c81d0001994400340610309400c401500c100d0701e40c4076003450007041000030b8810300c210901c2c884038031386c90b201d20600907a2691000084204544117040c1c00400402c042c0d01c01d08030001d40e4a00b8000c200074464601540a101a04425402400142c0e603410800c0b241c20740445280700b103a02d42180003a020011a0178030350450400060000805815070054400c980340040204580d507901d094000351a02150f100900801102405004254181c00302e00d00c000144001d46041c00c886660390b0003241e000e8110000580d01502c1c0718800c0b45010488000a00000e0380c0c0e16400d00c40c400c94885030070140b11059000c0c031a07000b000041c141c0348c561040002ca260500107000f102d0b00d14614001c904054001d800000c88405440184d001800070100b1050b01824020800f6a503945000c84480c5005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 855814145 1250 855812895 855812899
    0x1e0604090b01030807030e0901050109090903360803121308040b030a050103060c020f061911120f0a0213152007060207050411042612190e090411 64
    0x80c101140100d2600403007140618402c4a03201d60b9100541005491040c403c039255200300710550052207135036404401c80c01141c00d00440891030040038542034074100007200040000c1c40d901050104410f060505280b03031003131250302007980d454032412071944a11a09031400340c010312604c081940e4109c2120b1020240340107500d01d038180758440360166100d500c00c1e1110041103441c0c038014020311140380f0034500d45078080e00041c14041e071100101070f100c40c0020702c81c4044c0c0040c4106500f04c1d54068025a47c81248010440d688c0d070002c20029805600903039401c0400800400003c0c0004c1441c405c03a0a480d905910006000f40f60051070075030000c5103080142040b641200024150000542c07045600c1e134010040d2801d5400c1200c002d140c905c40c0da205510031410011a10107500c01e400c1140c0950f0b00320b040b440328888a02c585ca1000b0170700503c58100502c00c403050200d080350380704041c2100546802c94100030b04a40801108c010400c0760049610000c00c2012034001003086000e0000c040d00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 855815395 1250 855814145 855814151
    0x21801080709231f080109270609050624040f020d020304031e020c06090609012a110105070201021510170303010e10030819020a0807060c0f05031e0604 67
    0x11100c0856000780a44004926003d1004400000c0d28040b2810424103082c04a0910341c54000140100a48018490b01c04910303a80c1c0b01c0c04603100c20f148190f03134040625520a9206186900d0702d0b4000f4000c1b0343e0203a030140034040100e00c61280015800b0382800e03509296503815010b0004000082280c0e10b241300855500b0885002c68000da400a180300342d000c1e80b03030543d117070180000500f200440c01011508541240300000029903500040d41c041c1031040d40c03c0780e01c808110005807440c0c142c0c0040305100a00800e0602d44a0425000e5102894440e0511483d00258080192054010064001e0158000c80c003445101c00f611b43e02d60341e11404004165014950725410b03002a60f8099010003e23503000040180700800c003002101ea0440e501c8481030054500e152603e40b8180500c02036401c0b141e030607041980c141c0c1d100308585407401e80c03c5000155116071914007a40141405006500030808250310351600d1401803056270b00c1000e07414030040c01c6040c40c00220200b0000280700903441740ea = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 855816645 1250 855815395 855815399
    0x324030c0916020f070803070611090303071b08030708070206030a1b0c0606050a031e03030b0a1403010b0f030d030e0a1b21080405010e060c0f1e01021801080709 71
    0x1d900c051980c00b4200441562585005900000303040600002c21401c01d68004482001070800000840c1c02440c0c102e42c1c0040e100701c84445161040c0708580145901d40f00115070070040c001d805180d883c044000325004102555103200d01500c9000d00303d405082175405200071009820950001c680c04003d450000402e01c980713540795070207000799081c0c8000107080c2c2c000107004c2110b0b1340304030009458103d40c1c42d09424659684e01d6901c4112481d054004545410108205400b903009004c00380001480701480c1619500381c00c00640720101281d00c00e42c02c08400c0421403e18210880107410040c0c090010f04044420580292243c2840c3c1100b40c0300e8050070202203440c40c0a0201c225a003020601d401c64900009000c2d413283c0610b1805d40005554152400201c1c600c086800304d43d001c2c00e0241018600400043c854028400c04940c513000740344d980444410049100746c1c800781061010046203412800c12030803800380180e64000c0e0102400e9079002503006040c0700d94442064641168016 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 855817895 1250 855816645 855816649
    0xc0b0c1e0f070e010e06061e07030302130603092a09150602060705040b0a0f05070501180b010906031e0204090c0608100501052b02090303070503120604020324030c 72
    0x200c440552035440e50420003040d40404000d01c2018000c0001c1c19084029504004085100c0f4001906d507600c58100080d518809000080c5c00880040141c508a0384484c940e003805000b96018480700c101403000d01901040c8a40a445502c2203942c002081c0c40010001750500c094101203c1c82100074040303100400208840c0074024542c98880d40d1101c800964504031300a441d00310060034179014048180b10600c0456039000076908815590329101204050410f0103481c6481100f8019000d5424550540c103004029642a40340a1240342840c00380c1e030340c0e510442e0448080f800018015980180c00c8115451902c0001242034002000040c58034056078039414940d0b2590300c800080341410701041610201e4041500040100f13003013248c60050741a0107000f038030f1605250840e80d0300081c104a2105512075041e078664880140440783c1d1a40c00e41045584ca030003003c01c40700c441c0359071000034500703043c01c0c02aa0b0103aa030a4085007002100034a5402414201e2215281c0610400541221075 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 855819145 1250 855817895 855817933
    0x7062a061a0307060c060b120607080402010c0b04061b080c12061302030906010303120911010f110303270705011e031e06090f050103051e01091502030718030c0b0c 72
    0x3050030b17489921038410380307180c450140c03803181c502c0d00d218221400c0440d15180000c20002e90042c030713500d01015255900e2005841c1402d83e07581c0030f4541d810b00e508001c00c101300c0d607212010390311084485140c9180c28560889180c40110381010704040103200380b03000f4008240c00c581e0040c070020301d01d1400c240030001d4181241c000700da109500d85c1c0100c004009040e0800c5640076900c00081092220b450a0385070200304c42030b0518094100107403082c03041c3c20a07109159183d421950350047c1c0c0d58a080000700000d0411010743c00541003014564807000c0741c0e0300042c10304104c99060b160402e880c03a100c104a041248000c0c0d481060584565820460140f00c0342000c3c9010f40794031000031a14204072614040314140c41c0807a9070b1034980700050020850018803030541c642a12000d0020b500360b03100082c050700d0150001032410141810001d900c64554015500c1095a96522509000940e08685004201d4800a004412041802d11a41d0049401040700c0002601180c2289003150120006 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 855820395 1250 855819145 855819149
    0x6090304061214130c0f030c030803150306070306080d180e07021c1821080a17270d0f050307050f0313110a03020f060d0e0d0207062a061a0307 63
    0x1541d07140880c0c000301704894201c80040d00303103000381c940c1142c190b41d6500c408003a240000340040380e006c00010b25441e1024042c822240002d81a074000e4107115501030082c10050080d88214080c490045030018403c002001142408100c100031080c6032250188148002421000443c0504482c5c100101c11038480744440f02402d64518030395108000d0802c2d085500f5401c040c000400c0f00d4010790074519001c3c4d030080481e4128911b00c4d96200001d20030b481d60302d440b100d0480451412700400000c0081c6000c900420b4032452601c502d1009004040c9407100300c44907034000400c000b0f03405c0042152180d801780d94440d0b03603030900394540041200280c4460b00215400601d802d030520f480c2082280640c076113440540c06803a918421030859001031140340b49000840d00580c000304040b50204000e80102d4480391095058582a15043d03600a48800240c040c103400301d481c0c0441c03514810f1180341105c1448060000105d1001c40c40d40d1410044c00c0c035840042d0403030f4083d140c2e1418030f54007884070b140 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 855821645 1250 855820395 855820411
    0x40e030301080f1209031b04061205010906050a09030c0b15060708030a0b0a080c09101706150105090f01050a170a022205010e130608010c050c0f06090304061214 71
    0x100e41c0401d80b50fa180341014098002607142e105010160150302e001a10703403c6c0417a0380d00340018042c0384601007802046c2c968403001c80c20659060090501c030301940903542d55405803e00380501c0c0c1da586200000d842c1c082000a0014501035001c40106214141c441e420000100503c040c0c3c54501000a0b01c9400400301582ea00b94004203200c030000701c80c803c146619100752a8800c03114680300d840360311402c200a1090003480400000f601c9528428001800340116610b943c41c50038003003105c03d50301e10b8119811034000308003034101d518560141041e1480402e0040c0b0417855566240011030345504610340107024021131a5030036058603240007403036102c0c07d0300d0200162510620080c1c211986040000089090010f0009001e107903807004542480150540310716092124005c0350800400545e0b021812031351a010f0310070151a8001c009160f4040407404452100c02c80d00b507013903100d580507145028168000c00041040c58004c0c400c07860409040d441c000f50802842c1c104014212086400c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 855822895 1250 855821645 855821653
    0xd12050c060403121a13020904091202070e0f010e01051c06050412020d030e1005040203120c0601050112140601110a3908030a1809180203120906031302040e03030108 73
    0x4601c10302030300c11490858a017000d00c81d14420030030089000f0503031444403106601c3e000141d52005482c3c03a0045d441150f4003894a8154840340300c0d009448040d180103000ca961240c2010660385605040014144c500d03181d00d101083e4039110402c18540201c2c10080340d0010360f0b140c0b04002c1865446020701c154010014170090034842c00c402810001c070402440141031804518000501d40081d07680e4810890407130016460b156400040e1030002c00c5407030038840c87c0000941480c81c450104095048a1080e01d650000980a112600030f5500a0410202000d40b145c00280a98171075806c580e610301c00305e010f80f00c8010707180d2106181c41756075081c907c000c000c080400801c52181003805802d0000320584044404d410103404544921030a4018000c1014801501c0c0c02e003090191482d0040541900230801882c1c02c0c811014003001c840c10a030310a0040c3e907640c54801011000b1200348460040c400761840d981d011700e0071003501480c28266002642c9000000081c50300700000d6020b440e1900040c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 855824145 1250 855822895 855822917
    0x909111906090621090309050907050904051005090402240c0708150f01120305191806020102090d02011209050712060509010902010509060705210d1103060d12050c060403 75
    0x2901d141490342c407010030400ca140c50501d0503c0031324201c291009400c50045002e40c141d0804603414101d40e0002c0b544a52402c0c20b01540540200040c1034600c002d0307a05110582c0c1e1076800c414a01094400e2035001101c4030300080c01480c0100183e19840c003c9098642c10704402500b041203500403c1981da5642e0140c8418000c06000708014000c40c580e01405070310918142521a00340141841024000205924410300f010301400989070218440c407400c0d070b2101428100148103800c0c020300f44075440102d42e400308680d0b1041c0200c991481020f80712000405169004451a50843c8000405143c1d11005000020b10074050000181480c03a05051100000c0c104070b400c89001078140b810680c03401103c440180d8002090310300869046a00e0350b100c40c0c2c0c0b4103106080403a403400c442040c5d401a25442001c6404601410003488503080812101c00d0942ca5030b1260702c03054035504d82c800f410f004400d00083c44401c2804410405141c000e00f000040419145040b100b51011000301323606541e4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 855825395 1250 855824145 855824147
    0x1e090e24010f031211011a011e0e01050d18050d08090303130f060b0406080303010f0b0f0d150906030f02151603260907090b09010f0909111906 63
    0x584044880300e6291055154508514a40c0107110381c0701c0102900004120b44241ca0300411600384800d550303100038080c8019210b894401c0e1810320004034082403484010b10900c881d4081c074409810000c0e110340d00180610001036a0b50f4000405c0c0c0601140c1b2107455000240c03508440d01c0302984a000100782140060b0405072031503000508110b80da51040c401c002944848185409501d03402009a045c3c040450031b10304013400c1a020802d8019080c003c0000d011840080110304844200700342d80441619081101594440c0144e00c0e80c3d04407060100b140d02c0d400560045481d040d225080ca201c85540301c041c4802d0700d416070f00507102c42190585c40000c1d4100b44140b507005641c10100d69240002442403009240c41110014041240110290301403109600f00711f807070b01d841c4a000400b14500050340305d40d592402d028882c840740c107140400c1c1c80d60400710360043c16184ad000714030000c1420700c050000104600401651ba0100d05c0d0032004907501c5e04400400e1151503070340118540740c18060 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 855826645 1250 855825395 855825433
    0x3030c0615010f12050a1b020717010b01090317070c08010b04060f06021009020303090a12120e031218060c1614010c060e0f030c06010303021b0108011e090e 69
    0x1425074188142c00c0d916078100355000070026100c80381c0100010300c079220080608021f2001c541503070394001c0711a407511421500051400110380080d0301c0030009080304601b80c0c4c01c1e500b40e444100e001c01d130556002d20000380719600294401500124890034000b4948270402403140702e44c0115501d0755071303141000c2103060901504004d07108092201404514246000759203091a8000b800103654481414045503001c5c0110f50f02c1180050600143e540c8032510250925024141141d0703039540300c00389400980c020150810846c0004002d04445032101d4066105075105066022601d00761041e00d000c02e80e40c0c40040c1140e1501d4400900f040d01007905038966501c0e058000c050902e01e00100300c0b215030307409146c0f00401e070390000c0003045405800e2510303440d1103c40c0c0c3c007030301550101140040c0401400074507181240d001c0e5003140d00410050802c1e10510f1620b8840c40d000580c00d00043c0410390600080d05640e901003d011340406a031440345c80c085446402c441500c42e00690120086070407156 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 855827895 1250 855826645 855826681
    0xf040f140a061e231206100519020106030209071710230d060504030e190e0c0306031603060c09080309060405040b03030409090b04030f05030601020a02041a03030c06 73
    0x510045060742c203000c2e01a0082d581c0f81405110b10b4001c01240d0741c0e00d403080130702500c04e610130030592030720610146400045803c0040c040003080c041e070b4002420f5241181d2030350505402074984518080075071030201c2188500240030400c0d0341d01c503000000140c0b203410500b4070030350203559a00715900c40542c0c1d200700c0f120090325400c1c000940302030a00400140341a9111920300c1d4039042a507450b52040030a540016040020380914070b03100c10402415085080045c0c020800c651801b0040302c2509502c2521100c0d000d004c005800c01d4002641034107040d0300031504070030000d007215981c40a484a081030005160012103520f51580030951a280c1c110b04040003a180c1a00514100042c40000c92054042c5200c0e42d88125159040c016081d2010300459020302901b07401400b4400300780c1440f201900040c5c90403030029000c2d02003880c11a2141c1d0580b8001c0005034040c0c16450b4107a020032000d030810040c2c5c0000c02180f1842c1031513941d030400003000b03d10864800382445203084401784404105030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 855829145 1250 855827895 855827899
    0x70e030a031d040608150618040c0603020d0612060c020d1103031306140a0c020c0d0807020409060f0e07051c050322031709040621170f040f14 63
    0x40c0c100001e50007241041c5081540030980264920380740c001009000035900c90f40050003812220842d441810395200c0c07040d2004d85003003030900f4102500002002c002c68000d011154941024010302d4031940041c00c14004108021441039100c4044031000482500304544645d0382e14a800ca48a40500c01c5e4030001116091006800b0b44284c0b8064403440006e01d55210040c0405401c1d04200140e807146030340c1c0326030035400d15191900c215044d0081c48110500005481a91070340303031061614109070320220380c0c070416040c113003181a4203000250241141c00c0b5401d03030300e800078a081c221061050440c0d0710a40001801d4061510090000f8ac01030b0200c8643c510740c03441c5258000c42e40000403141030141604803801082c03043d0028441c8003038190001024108281041e4041503a400040c040c0a03400b1941000703001d658022088030500025401180450500480b4004c146800d0460402c44010000a07191030a800c49020302980250400c800001c02d4450621a800600c601c166440b801 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 855830395 1250 855829145 855829153
    0x501080c032509060803030a05010b040f03020f0103090b150f030a1a070c050d0c050f0706020c0f011809060e0703050c0904180b151e0d1b030c0905070e03 68
    0x40e00c080703a21882005030020010300710507140d00402c1c1d03841092100a084141d010001541c0341c2181d544c50390b00595880341482d0415001181009880c0700f02c50880d40100c030607401d42c03840c560a100645030030f8944117050680da0108034000c82c07292068103201d2070041c4494412500300c401048100051005814066480134038060b00040c1500c10788044483e1b099503440342540c0358141128120101000141103000781000701140340d4000500131800c52081e4140c40c0b030804141c410790366403c61881040e0040c0c0c4551940301c1581840320300510701d400180350010440c00c0008a504070710b4200d138071061710141e499608000440c101c03c0c600c3d80140c0b040c6030500c000e08203e40440c0c8180200d03501e2070b1045c0e0b074403c03a13152007101e00b800c81411140d100503641402c0c0b03007140c94003084c145003610607130044400311405020700048800035511400014002d200100c820703101c1100da03650b0441d40e40000000d0400c0840441d413800b5040000348a000c10100d818035003400d00170485036500d10705a0090340 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 855831645 1250 855830395 855830413
    0x106081b0403050c060702030a080c030304060b011805060d150f0e1308120a0b18071d03061503010b1e030d0806060304030e1c060b100507051b0102070e011503050108 73
    0x21021441d1080301381d0888086444d20214000a4108811204014000c44000544013540000800510700c00c0d17004207801c01580142100558045000a09000170816001c1c41070100c0d142c0ba501810649040200003d60000800d071031000030351007a08480b000150000c420003a280340a0407455224590304405504403125030744501a034012070f60303080d10b03041d8050700142e0313681e103c0c0d4032030704070503000410360303a82201d03c101280b04146050ba400e1001440001d010341e443c012003648894009000743c010400340e62060f0311924850601c03200d0a034155241e40c903a40003555260f01c0e0f090034401018200d84561460700070185403514801690040c045000c04000050361590143ca6009425050640e071304410784002940100e10100d0142c241400404064144099a405400740e14400d40d0000004464113500f036440d8042d4a0008000d68410050b11050480c14481c10b41c907c8010b004503030700d1a45803500a03000c480241c000c1040b04071001c001d5024150300d405a580140712110140c10042 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 855832895 1250 855831645 855831653
    0x301050a0606050a0f1e05072013020702150a090f150507110f190e0c0306030c0d0c0305030a03020309012d021602040515010215011d1e0106081b0403 66
    0x80104100310017403207031581104050074017408081c50440701440d400024048008005001e076080b445081e0703402c80f03400070910b05842c102020310149440003482c41242e00b075162250400b82d404034000701e0300940b60b00f400d41803501c40217010380616691911038240744d81c01d000340800207c04c59030010340c0f200c5c40d881411080b590000f04035584176400419011034810504041134841a0300d4001c0c81c0c201c2c901d0505400b031b03c1c00a07041c19054800b60801000c0710386032030804030702d14001034450030740c1908280c0c1e46c90001d10345440b042071070354803403c012455190307262a024103540240c1c00b124040f0b40c0000030080001028400c032908440070005910f070b01402d101c50714226100140711041016400180890014031101c0c03400c60041c0e00174420720861400401c5200311070801181940075109207124040e0010001d0002070688030100400d020921383c8034008a81440060b281d4070303020216621020a19500d0070a0718007800700b83c3ca442d14582010700c0c00c004819480d07000d125100405010070301c005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 855834145 1250 855832895 855832897
    0xc0308040905070f03050609010e18060106050409110304150506031f02031522021b0a080a03050c07120c110301090f0b10030506010509091f0902011206060512190c0503060301050a060605 82
    0x76600c2b1a10380c4c03641d90f94440e144506010704d040030701140c0c0704017400020450f50007401002035400d450001c0c03001c60044541140907010544009000101100c0200000c44113540b14a1340114000c08540e0100c1012900a40a448600e499008680c000003000060f0034401c0390740c000000c055500d840e0070342c01000d91003503042c40c040c1210003541c1c0000d84454101441e50301c444900300a50165078241d0203d18001100d0f9020441d5400440c1c103181c0001d450284590658010715040040038808000c01001191943c0c0901c00403100449030340314802481c4c07000d1051082c203510500042e0440c2c80340303091203004000c008041d0780f40c03d04013250620000340c001c911070781103c0055820b18140d40790010310a09000c015115014140c40c400d0708031101240313582107804958000c0c0c035103001c0e0f10140030408040d2074107801080003007442085800c640e02e01065800354005146540304c100081d1505002042d220480107480c0019008000e105852402f031040f6038010321903940810005241032000b80003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 855835395 1250 855834145 855834149
    0x304050d0807111e0d02070612090f080301091a10022a04020f041712070f02040902130e1006150f0201090501021603030e0c060301120c0308040905070f0305060901 72
    0x80081c014049180a805650080c80c00d00d16903055078000521050b8403005043d0305010940700e4400d0120417100c0b0390000c9038030340903950340d43d41c3c2c000c8240035800044090001c4ea1401c654000d102e000240200d22414091406400000004501240f0902d12a5032181c6001c2d0403a100d2918420b01042c03542d000595036001d11104144007215100045e42044144032104090303400c10300006100d00500118001001503401940030034800f0810349c50003070340d06d0003041e404040028040218902241450180c00d004600c010004203902c040c0d076001c26080c9841d420307182d01c12601c42d031804403141c10510046100c03401c1d80c2030030040340e80b074210966403141c80c0c10014014400161000c8607210310030b400084410350858000c0d552600d031203605c07000c4221100803e40001e803401054125000000c03450f0810050000d1101c0e040d40d017001d03802c0c0400008048200c40d54801c03003a00100242400c4003800c010015031100040d545010000980710300303452401a0300701850301c02001b14a43d514101307141 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 855836645 1250 855835395 855835397
    0xb09130c0e1909020a020d08070216171606050301051c05033403090f060815190e0109052203021c1709100f0212060d030c0b040c0503070b0304050d 65
    0x50b044606264a1500c5603036030400a0305500005240c2c5010340c0010345441400e14507900c0030910342d5030350340403601d03480d6450481d2200c0030802001c100c0550981c50f484040046d40041d58058a200d02c00e00914801d9540010003145c400f100400051401e0001014050b2000005080114090b03441c19105c3c41001030052008111240251a0303038440030f0b1000603141444000012031301a0b050103040d91100b48074903c10480c80350004140584036141142c0110f02c2081d0301400415544108040010300d81b801180324410b0010010b03403007806840081c001e2006010018442c20f0000d0703cbc0c11849680020034001d41601001c1d200000c5e40021a5000780e0809511000c0e400714804c42140d480b100700300039601e80b45121301802003000c0040348007112807030340041c00c10a804822402c0400d90060040301c552483d0b1308000242d1a040c4444034070300462085c41d01140841482c0e4800810b51400d0310240c4844000c00f0060041d41002c00040020f4180392004901f503240a0741c0e0341d542c0b001c8161101c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 855837895 1250 855836645 855836659
    0x20106050a0521030f1b01061a0306012102071407050f01050a050f0f04061116080a0305031306050112030e030c0a05040b0d06110a0e040603030f0c14070b09130c0e 72
    0x80303003c0b02070041d1500014810001070765541107444a00780b81d00b00c1e800143c201e52030a600003400c00000708804815a844a01a5045036a510015107684039441e0150000403030080b200011000284010042c0314801c44120004c2d101d00301c0b03030b07516000c40c0780c02040c007405588a0722899a83c02c1010b5a6600703110b032814941e900e141c50518180c40c000c52000302140d000204011458581281d0429800c600070400c48125101039001482049194854410b6a8210717022140101e40300d48004c0d5440186803081d03d41101441d502d56003120026441088407240402030041096409900b24468080481c01042e9140b81c1c440050082c11262281612869840d014222551288844000c420360051030030001c1c0b651085c11009070b80d100b011900001807a408480d2820326061040c40d081d2030709941c0b2944039403402d0f48260340c0850180790030b86507111841d082e05202d8a080207148040c15650841c1903c0f141440140803058101d4100d0482542c10001d0b6400c0c550350203400559580c0b0121041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 855839145 1250 855837895 855837949
    0x60909031c060b0703050403050c09011a0a0309020a0816061103190e0306190612050604030e0307031712161e0c0501020d0204150507051b0a0503061006020106050a05 73
    0x480060065070f00404444001281500034180c0000240045030f0080c0c094403000c0c55041c040080c2c40400740502075110002c0002e000c0f05034070303010280508400c142000100c210698000a000c4002c942c01615594461300100001449252448000307290a003040990300b00e90391503441d12802441189150a500c030303000e0001e09071082000c00b81068010342030b40c81900b8800b840141c44400740039400502030030043c000a241062001130906030f40c002c0c0217041350f612583c1d002c58507090010f800c20350600c2100404000b2580207102c4040b541c45401d81329a0300c01c641078503000311244c000c110640c0c41000805014902c1e4208003074201c00b82c6100400c1407030320307039a1509990b51000004064040e61010070443c9110200d540140f0580300246010014088035910880b074500c82c05c10f0050040d0403800844204001040d950850001e00501c4246c2d00c0341c88002091600000f1214282c2e050031401040201a03020f21440d0301414094071141c01c0d0030b003020013160400001914209000e076805801e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 855840395 1250 855839145 855839197
    0x301290409230c15090d031704030914030a0b010b070c0e01081c0905030604020909010e1203150a080d030504050c0402030f0406050601030e0d0503040c0b0a230901090b130810090b06090903 83
    0x401c901c2c082941000d0f049c1803c0c20001c1800125000e140d007409400b0211031241d2a0015100550651180d416422603003171210071007981c2c000400448803d0305518000c65042e03418102c20740a08000f60040c000890807401d00b412082c100f40e0140140700700008140f000b0f840104105074860b4040e501c0c1012902d449480e14010b00940310f618400d80243e107000129920143c0c01940540120b48a000075200100300b00400044103204d4002c8507809108403100443c0241c0203540d1090261054564800b06200030a01ba40d2080300c1507081041040100420000584a00354001a081c40c0070003c1c0d2580c200c0055442600060403003d0000210008082001c0c082c0003501030000c0c3d0065a840c1d80d00c40c040905941507990441c4000590400d001c401d180320f400655641d0306050351214506490309903544078650200c2c6541121a000280c0411554401c101d40c2003141c60040002800e216681007030440e1000142603a440f50b0799440602001400001c00d032010018001c41040c485014404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 855841645 1250 855840395 855840407
    0x19020705100203010f0f0801020a051608120a05070305090c0f01120204030f11010927020a0302090a14040e070e0f06030f0f010207110301290409230c15090d03 70
    0xd511207640c0000008900140d01170030943c1120920943c031342d10b0640b90501c060a0740a1400c00f0030014500f84070801c203076a6401400313140b2034091071031540b508800c0b1100282440e0120b814442d070035214018005665410311a9551288030076002c0c0c0011406800010300203040700300054104103120381081c400403141d90480d002103070b000110915031100c901d85007032a40ea09581044c04550207510024400c00f090041c0ea074194540c2c1c0d8030014407103c40107000000d4200e42c5105041560070b02441d11542c54640821000d0480c100801514203842010842902e14003500c0111a400c0320008002c507401c4c03845826000100f2100c4026159a8500485c0c68032071000b811000b40c0c880d04040b0405894194010f0840c2402000000c0da07040c003035000d0601342c500412510b2500f0741c0d80c00c0d50b920400f012052035145003400520105520725503494003400d001c0d003820540b03404502102c3c42d1340100d508100d33401244c042552a00e22090a441d09100700f802212030700c0d409540800c080c1020103100380 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 855842895 1250 855841645 855841663
    0xf07060b06070b04121103090f1003060f080105060102010c09060219150e0a061b020c12010908072a03020f190f140a0806060d0f02010c060c0c06200d1104080d022419020705 76
    0x1643700843d036501c80d10035010340b41c155402da025510341402c006420348140c0c2c0b683c0c00d80310b03950014040c4410707a079189809144d850700255030545c182e12620081c07900c107010b80c070b2060002e28000c0440c0842030601c802180d800481c10307040034250002c2507160a80200c5e802d480094100c03807551845644a00c040c1c050442d054000301805d80000320714080081c40720700d04082412202d20340300741c00840c04007599000441d000203036003d881c0c552007410a1070006a5204034420420524654a0707071503007014102e40c00b1380c00c6443c018040c03140540e400c3c104002c1c20760013002d42c54028402070600c0c0e008594014855000940344622403446802503900801c05040e1882c0e00240c02c105e81c691580c8000c00710319046030b0448145003092075201c0d040d001200c113140d01f54021007161f0320301600c2090413002000b064400c512024002c2c00b0001d0300c0d52040c82418590000c2d07402070010b00c8260b0706601c10900080310245840d5500d60305000000e6620701c8114442e0011000040c5d079203c0b20b041251502c0119 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 855844145 1250 855842895 855842909
    0x130c12020f041a0307090b040f0314100e0c090a180f1b03060f0c020d08071b080703022d0c040e01180c05150f07060b06070b04121103090f100306 64
    0xf041d009090600e07000250311508082d621034a465407502d241061503c01c80c1f01c2c01d146815003031000d2020905800382d50101140c1d68040b1103154140701110b1081d20101c4a1b06041500312812041d00d900b072185c0c115600203101c0b9010031100c1c10b60002c40e4419441c15030047d064100002c18941004040c8500320022109007144401460303903441e0900143c020451904440760900300201300c064000110301e8042030f101d031a81d03611075480c510100d58082c240c0380000104580c4050702c4020030031000080903154082e80c00b614074000200021495201c01051006100c1501c4540080120002c6200003140808680204030103601600e194050109460f055003950070100182081043c1d241100c41100c105669001b0450240da00314280c07402a150507840f010001c004401c0000c0143d8088264441c0c010010350810703400e07465582d0321800031142101c1c003003c0b00d0808000260810101120540710300015450a0614404105120103040c1d42d980220b21050109903002d0083e00200050f00d25 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 855845395 1250 855844145 855844169
    0x30e010b090f070c1b0f090216030806060f030c090405100612091a07020c0f19170a080a05030103030905060301080a0303110409020c101a0319061104080a02130c12020f04 75
    0x4017441d8030180002d0b01c6000c0c024071842200003013055690080d0f4204a041e581182d81103000c60b10180c40140c0c0003408940d0003e020000b61035143d80328006140184000021141c03034255403004e1000704e81c400f4042d001e240000c00c4042000543c094050f850030708440ca8045080c061a190009594540042240d410391000c400c1010b00355000448114a150481d0100a145148d6003807150b583c119000c1c1c14103031013040704140500c0e0700c08500c1c0d42c4580c41042c2151850b07047c42d255400b0b141c11a140c401c0c002040000100b00f4181d2201c144c001604003202e160b807955140c030144543e203141c00e00005060545806000c1c0c1c0e892081c01c103850041c06066400e540e00c41801c4a841d46540c3c5141d1644496490030500f40e1007040814900d200501d0090010040c81198103900003d15a50807021608203032039865a035642d9005001a000400c041c0c0003c0c40c080e10a4070400c00522080164410940c4c5029003140509601a14003d200b040350080181e4510600450358000e1149800a481d081c2d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 855846645 1250 855845395 855845423
    0x2090702061b0901020c19030b1306051b0304260406030e010e060403021e1002180f180a180204110310091505010e180c0a030e010b090f070c 62
    0x50007054840c8110038018140b6071a4419007051110b40c020407180c0350050380680800d13091400e00030800c0b4080c41800c5908a045d0f95a43da40200100c021540700446003090b0aa0000300100741c01102e812405000d04282d10b5216004001001d020003040980900c80714285401103000040384c641c0d40c8085050b080341d5554941e4000b0b000ba00604038500340755842d00c1d103a4541d510021445030f016903071540c040d121881a48400300e80c040148911080640200849903d14004610060101c001a510b00405826211040004c0c00a8092140c1e0240c03542c9025000c801c1031801d015a4407032842c12000654004101003a018110101402500189415051810307090340d800598400c0320145940700800340c4402c4e00400b03403142903420007200350400e0024050b035030081070840312803103000e001074040300b071000b01034000390805440c6a844107030001050364109500d400307100c0c0c40c041030340c0c002d000781200c280c041914030400811500c441c0d580750b000303e1881c61241980300200e40c4c10408040c0d8080d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 855847895 1250 855846645 855846647
    0x11030f0102091804020916050f0d060603051e01051203041a1905040b07152a081f0b09030f03030702071d15040b060409020a081506040b0412030309020907 68
    0x94081e081082c8103003c1c1420305510400740103005882141d020300f10329038a86407000d82ea1448a1305003440c40911109001034250300351460090440d140380284040350852a01358040d04507034001d4484040c050ba280742101030419580ea22034111030080e201d0040f08480d016005095018603080341c0000184861240d40d03c8401d18081d003144042880c600b1101814228161110310443c82144400300b01441300e04042034400c1040110700c54180c00209604041c1e291090840c09d80039001c1c08611404812010b2265114040c580c0c84110f400000f81d03950720f16240280380c50f9840c0318980070000006144465528203003c0c0d80c9004145a0850b03440341084030000c1d49a030400e014083d0030f064224a2102da50000742402030103100c0201f0b503d00703c0c5c1d81040034007010341f40b40c07500d203900303c40700b0040000c0d8441785200030201031003243d56031609418150f0f45a000484c4003140207204103410b00c4184111b601d840d084078222619260695114181c2d490181c3c01781c091060003075401015681004541 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 855849145 1250 855847895 855847897
    0x2151c05011a120a050601020705120307060e420108070e09061012050708070f0503010f0212010623121609060e01300e1603050d030911030f0102 64
    0x640c0c001c100c0100003140c03845001c01c0c01e00420a020f0100d00e43c1e00c001c2660034200790f1000e50084018410303290043c0c0c1341c10129420030a0100d01212650000030f000007404213510482c0e90340181e0b200500802041c1625010351003400094820742c086d0f8550003c00c940a00301c418407030041d4209110066903940c0d20340c01f502d5894611810000d003200130300041d00d144020503414031880229070b0300201181044002081341101d030404031101d01c1200c4010400c0c01003000800000d003070003003004400c03900784414542035400e4141c5188489006001c0d051050f41c5914206064800603d01a091041601b00380d800300c400124003d12444000101081c030b4866030b0b000310744604c00146601e540700c0d2032004112500852440741000003044103103051386941c42492182d50348001070340c1c04100800c0c1800e20140f00200d00411100465440c00b4035404035005025403c0ca4144a10210390f0003441c5890702600c91652000a404041e62104224104044101710680750b89000d0300302c2e40b030f00206004650007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 855850395 1250 855849145 855849149
    0x513080d0c17070201050409180f2303070b042a0617010b122e0807031407030c06050d0e030a020714030a0201021b0a03020d050c0103062102151c0501 66
    0x8101007014080081049a41103c0310168113079161460f092500c0c42d00d00062aa04009840b0007109058a030041a40040c0c5140c40390700411144260070741c10601c1c0c880700c12190a0030541600244900008954101805030703100d40c00c42e000c4c281245003510100c0c0d005040c85841c10980915110100303003594440c5450280308581d0010190590701d40703030440b81c2400381419000c20440d030b141c001a4456108941400c00b07039202c07544202d0748a2201c034036003a108800d801c0441181c0c0506020402e1021124020071181c40d20303405401402c0c2542c99503e440308c507900505003800340018081159a40d035a01c031f00c0c41c668274402602c0d1035107440b04000f03454409074401c11000341c80b00da80c1c075500d91401103200500303242e05800034056400c4801a10380103000c0d85090300e5000242e0800040580c1320303904040f42d40e91156010b40381000c1c03030f000050125880f5401690b1844808010154003400300d4410010440e0102d64544080c110740c0700b1607600d40b01d8585285c2408a15200d409501a015040941 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 855851645 1250 855850395 855850403
    0x111c03030906050f2202040216060506150a090306180c0620010c2a21080702061b0306150a020d09090c02070e090a1a0708060108010e070513080d0c 65
    0xf00d00e07112002c0c40300501c1c03015104034213007504000420700d00326071000030002241d102a0025043c142540e1890f213522805042c01ea034015103417402c12109140040744544800520002c00742010f070000c5005011821b2808000d1505680b084546030300c00403090941c8480d907018401c0c0c01c0c5c0a4607400002c1060680c0000c030803c807254090319207144072040c05031f0681c04407a035460758a0080d241d440100320b0441480c0d1075028000900120000c54614900342c141c0c1e0200551990b400314101c4030043c82c56000901c2541103401510510405004401ca444982c42c65840c066480c0c1d10749a00040e0852000b4680f41032401e0300140d0540e12130b40101c3e440c8403050407502d5024066544041580549102615690042c2c00c25602840f19508480006801001500c1210300d0034801c1e598181007510068881d60100d10400d04000c10035520a00d2203500c6030003840e2035440c652418a5203400030303801074038060a2080101d910038800f9400040700e03000744840c404982c00d100303403a0030240c1080e007840001c1d5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 855852895 1250 855851645 855851651
    0x70e030a12030c0e011d010507050f0703150207020604060c020f1e010909090b01090c140304030201021b0d091503022701030c0212030403030b06040e15040b040b010507111c03030906 80
    0x10078018021210010410703114000783c0d801c0c6c04030304000510110a41814440240701050210b8001c00036900c2e124603040c018141c45003107040c440d00302c4649e20b1100c6003007801080080016102c100c1502d0443c2d5141c20300401e40200c9100085110608008640e00140c0d02c5d44c01d43e00d00c0071605040e904410007071700c1e1080c80c00e840c0e4000c0415143c81e040301500d206803010040104045503440184071041e0381c90204403030180104040701c15071050700c050303005039000314003001c01da1102c8040d44d2020a00700010b10071500d1141016115030080d101d040c14081c6982001032820740613804460341d07449009503e8001403002d4960040c0024006c848030300103841c0c490070044090000a03040f1a02403a02105411540c650358128041d2484820803600010140300020b030450f04511054054440c00c0a2803201a140c80c1c1400116000e01b060184038038103140392942966001001ca1700100c0d004007124400046070b9020450210582059481c0020310b0302c241d1091617496400110058412a428 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 855854145 1250 855852895 855852911
    0x11240604090813050f121e0f060a0f0606050a080a0506150403061d0a050634020303181f020f071e06180812040303060503010e070915140603070e030a1203 68
    0x4000c501e011b6400c40304169001840d0fa600980c101011040c84030301c444c0440303801c41405810701e410848191400d0f41c0c030720344402c3d07000c0c0d00d0241070007124050304c0c651818601781319020600130b0100c0809042ca6090b550b03110080307a05a145c0d200d00308000c920255001b03a40344d640b0301d0400b0051150112082e1001c916400789000d010020132480c0146030488000c0c0810344a008007100014401c600c030103140040600c10314980c8420005001242c0c0494001e03680b207140004000419142c000c452504540011060511a500640000b01342e80c0111200680310240d03001c015115203c0c6407030103048180c07407203100300c540c0719040c080c504120703c501c0d400c1c0074040340c942c150078004400d13907030050201d201440b130100301501c00c2c0c900f168050300134900403c42c1551400031900b1200240401509030304003c80a000f41061401042c02e030050501030305000da03142c12100b10800d5a0000800e21560b000400b041b0a1303807042d9041882c0000c000c0550f8194120b500e044122091034100c5038021905041b0302e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 855855395 1250 855854145 855854149
    0x503071d0a0216021003020c0a030807170403081b070203030d090314040b03010603020702130c081e0906010302040e0a1205120609060306040b0901180b010611240604090813050f 78
    0x3da900c21460201c60060b5502c1d940d08002c0045010384400d000c2550038030a0141000081045038071442c003a40b00d0424030b061564005001544190150750440918010302c80041d6000c00c400d076101c029614400c888010b51000c481c5a4400c80304080d5151001098a00300781101d544406445403091300d544005c00b1010605041e280114030460903090070a00041055034000d4008124040c802444c0c000140c11803582001103901c0c180b4488001030060042141080c1180b000140c0d9184103090350b029407820305c10090360344505000081c010364139900040780e400c904020800b01e96510001d10301000d185104000d210390406031540c00400c80d050f000c949e481c2016440c1d503000704000350103030080e60b9036a25061700d84940500341600c3c965903140107105403404102c400014601c100094080340d458200c0060401c0440761051183d90401c20b91001c0100b100381c4103c000d1002d0341d8400c509a03541ea00010b0091002d4040901007010001c1d41020072003c45203030400340e40c401c998001c410090a02 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 855856645 1250 855855395 855855397
    0x40e06100203030a02090604050405130201030c03090f1e0804080307291317160203010507090b04090f1b3f020c0c10091d1312090503071d0a02 63
    0x1980c140560002c03c0031500c0100300350003d104440f4080c003684d20f055581c40c0403070b049450440b0328114080765400d05000310b6905019443d440031980c135091248103a05e40f01d03140140c01a010040080d84c0c6604080c0740e1454000c641c4649513002030300d440d219503a030240c3c15240c1d844920101c50481091036078643e10f000360320b01c1d44000002e150720804d46507210030481c03120300f4150301c0903106202e4048010055102c440018034820074486203402a400252041c10709550000c0e0a24040c442114018004040360310142e40c103d49400c01d011403003060822080c001042d43c651210b0340090504a40c01c000c1390407208000c102000c8030070030030301e10707842c5694254100140e50030a5500041000c81052008503500908082884141922030705078480b40001c80010040d40d501c804203280f60020044050400103003412004014040c908034540f40d4100d44002c10701040081c444c0307620748449410144030340c0c4030a000e04030140499801c00d407204410401c010b62008241c0320f490300080013030324000481c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 855857895 1250 855856645 855856669
    0x1906140403080103140d050a21051005010905030c031c270302180601020303010603021e03100e09010908070821010b0d0c0903050c0607031b0f0210051809090c0a0b040e06 75
    0x1d0307100c40c10429241012aa8a13052001002c5089c4c22405c9100402c0c8a40c482c7c10300900c21141d5000f00c0794948400940f2446003640a5032207074000726040d01107520041070062090071100b504508102d01c0c800c041d100c0d0401342281003c01d1084009402d41c00e076021201c00c041d03d00845010032271100c4281d180d01611000c0314100d0041c5c00034001048264040c1e006886200700c2c01000e42c03c91050a130700c180c0c182d04111142240100110780800800801700701d05508141c1c480000d00c501602515601d0603403007a050b0003000380c000050b900d44004010410f60305034507500f13030011101d56540c0d00d800115401054980a0140c9814421980140152440070481c1d0380a4094444400e4002c00c10103260007501c019000c0c41240d00d241108006003001e08010288a2209164514258010302240030318102c58103050010804c1904c80441c911074901030400341c210f600ea8403654400924906154401f140c19030070800b40c440c08110086103d000e0416241410408103440c1c2d58401048071203c221 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 855859145 1250 855857895 855857897
    0x181d0603010902100503131506030c050a0f0302011809020c0f010b1e060a0e10090816120204150902070c0305060606030f0c09030a170306130e1906140403080103140d 73
    0x84007404e8060082e009140d102a8103440112000000d4543d240800c81d50056080499034540084c01040a1181c465018100aa8150300c9644c00c01126802c0d0f21907602010b81403109154052811710202003c0d000901282041036480741c5000403920741c0d0f048455901c50381ca50a2904c0e408041c10104200481c40b000b100d01043c0700e103585400d0087d01e500804001c810080b031010286095100d0810000c42a40e19580301c1075070900c1c1c06c114508114080c035212942d5400d19008026100c42c4800d1000b80c070780c040710000740081505004103001c61080e03010707083e001d0000c50030005100c002d05401d8120b07070060b0240e403241e5851004220551208658a180c5040018007003184241e103440600360012010b4101e651018235a1030b4141c062818105801648000004100d1242080000d00e58000c41c0b4030418800c04401c0c607007040d26910b2213400c00402407626202403080c0304164008030111403801c00500c805041500f0b005107418070034041541c01501502c1d000014602c0042c0310100c2d8412 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 855860395 1250 855859145 855859159
    0x20a0e060a0203040501030518060702071701050106080a0c030b090a060e0c120403113a0c0503160309170102040503060f04120818010c031533181d0603010902 70
    0x3004010740c02440058070350209c2ca9110700d16000c4100041145a014107400e400400e4261b103400c01010202d02c81491602017a4140b0f801005415000340035543c1100f02c1000c04110900e07921381c200c0043c404080d0f0950310415004c03d001d0001c00c41c1d40f0003400d0750480d00010949982d40400c4222034894020b400840e07099420000d800300b841600301c081d080c01040160f45942034100400942101412000c00d20389041c218043c12400d19030600703e10114030350404554046258451907281e024110319441c03036012178405030080500c0780d40c040d80a403070118100303244200001d840c14000c1d0401e0103418068811070000c980001e00c50109a4170032580b044100c0d03004581d0010454003080040d1032142d02000201c40d5000150f000e0041c5040e40606541c00501070031001c800484000c0a0f501115001c41d100300440d107524001c00a071008071782c0c00d80400d084500301100032101b219032600070120802c4441d101241020181e80d0303034512564180022007554540c50704242c01c813204440000e610000c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 855861645 1250 855860395 855860399
    0x60c0e15030402030a1712090c01120e060402130e01060801090302160b030103020d02040204051e03060c0403080d0c18090c021011070320030409090209070306180203060d020d030201020a0e060a020304 88
    0x4030700c6c3c0400e148070500d6200d9041c00c00022000003a00015203900740141c00494041106d03591010740001600350a0105024100181a9668840901400180c00b590300f00c009100c0841e0513401114513039089000800c51642c3d01c109050003018004000c81c010b0040070704003454030b00350070b8030041954104e02030180746034039503401c200042c0c00700c5104982082d0244000201c1e81d80b2200391a03104001c8203019000030030450101030425500800920701d0400601040c004114800140c1c0e10300c01c2c8070500000c420500030070603500b061800d007242800c02d03995100070492504540103411a032900c0e40031100d00484104001080e16034040c601c4140d8403050000d0008031b4420144541d9aa44d1031040c7e00d01c4e41c24108400341540d00581050100179210b0b54400300b141011680c1c168455030038541040100c1c1090010005080c2881004103102d80101c00709403540d4800d12203004842d4006c4c0080c54003421454080c0c042e4210f0600c04000c80c004800b950801d04050040321680e5059901540ca424 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 855862895 1250 855861645 855861653
    0x24170601182003010909050709231015090801181203090201140412140c030703020d03022b1e0e1003060302060406081807030b160c060c0e15030402030a 67
    0x4011860094589003010800c0790340b18041c000b140a020849808a000b01503402d000e0701e04042548103c00d071618103c1804d202d80781041e5042c00c680345c40d59403814181c1380d1030301c07007900171607035030070007441600a00d12074036603580c012640c40708481000000388600f00c218044140310500060001e0070841c4640020b1003883d210354850240e207841414540d926540d01c5010382159005504242c10070b080342018402802141c0c02c0805e041803090b4018061704d61480e0109403500e046100080c0650130b20480103003094000c0c001e40300c02a10706486070300b2101030380c0444811101440710b80030106111000c0c0c06a0000001c0c00d0005042c0c0a03103e0106519050b420b01281c11480314082081550382d90000c4016a205c1d4020301c000d004035542d0040e40d06000c455a1040386442d40c0320500c65000440400009030b0100c45141d1002990789024046204c1940598000c101c85000400c0300c4d00e401c0a846005400c8070050003100c0e002d54450440b400c1c1102d4420b828031050342d01941c1584442c42c014001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 855864145 1250 855862895 855862901
    0x7180207081605070911040f15050f0a08060108090f12090a03060e01050403090b16080f0705010f05010e06060c030405090604090210030b04140c09010305060102012417060118 77
    0x510311a14050b803512060300d032211068640400122800c0d040440200020074250184800312820508400d15291030100d1031a84440103100d444400c0c036141e003244610360301400030b40d1003003002c501c8070995075004c000780240b00340c80c00c82d20240401c0071900071540c0780400041040800e041100101000640b180c0c00190305e401c402d02299001d010003d000c40000d050307006880c518001380340045594202460301800820560300b000441c0075051040c6214403110403e03680c41d164110020030f41e2502c84614242092207912000b4202d5800e00d0500b201065060b0701090417106190384030b013980c1e00c41e0300070040319204490629915610070301c000c0c402403030700c4ca803001c0e040140200002a0410035501246880300b482c2d01e107002003613584008400a040c80d000e0760050600c11002c01051b8504850b02155900a11807981d04061303660002403200d9000f54000e0018030142c0740c45903540c015030708260b43c011816002d80e8a0849002911140780b200000300641130368240100c01102c0c0c0c40c42a003003401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 855865395 1250 855864145 855864157
    0x30e04380a0f030305030a050f2403190f02011d21070801050138072a08210322060207060609021908010b03060f150d021b071802 57
    0x11181c04640000740000c5420501001540300c0c0e150b10351245000f2251504540d401810355800b06041401c206c071149807450044801d0303928202c002c92107548003010900d001c070000c00d00c908503400b042840307044c84050f01c3d4401080d071003640c0c0d10360100200091034a181c0c1079000410b400c10741160035900c18600401c0880d00d15840241111403940c0c0d1610140c0c01d5900a0740701030100c144406c112b900400e10380c15180c4220b410222860310003500a00c01201c0742c85614006411071040422080c04a80941a0104180c6402d440d1898903500d031403000d503d0f00113035070039068840265043c001508913050103403031042002d100749000b94a51554030218186411703130100d0f840340d42081100d0004000e44182e501516100300c0060321030401d5642d44140024103030340d00c014000392100410202d454071003101d51040e4140e8241c551104210041940e50058440c44001004081b440d21550441e6a02500d034550a1010b00007a46009541c3c00d07031036401d41d000b001824580420760a41190040e001012 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 855866645 1250 855865395 855865399
    0x6090f010e040c05130e0c040b0d02070c0311101b020609010203191e020109120509120106092307020d0323090d03060b0a09031203020412030e0438 65
    0x106520708180001c0484841e02207032000b0500c081505c1d003140003481640c00150001c3c1c0402407480c10200a1171065000d98440e030140148001101000000c1d10f80644010a600500c0c00800d1522480e01d0041c9080c18560305015000710700c0c1e6513110504c6030b8808152800e5402a0301620090307034007848481c0d805a204141940b1041040e12000085411a403003c1141ca40c0e4809103022041075506034485914900e401710381c100070740c0001180303080092007840e00c51400c08581c2e9941c00d4000c03841e02048038514550310b51801700c000502e100b154000d210021080f449490841c204141036a042e080c00383c56280047c0d1015440c5510b460082e48407000843e1180151944c2d85c043c890740031040c00342100c0b402c0c041d4205400803c5800e0700f5005402c00382c4204925107042003021440248070510074030000d0100701d1400c05102c1454087c1c0d04540c040c110221000d101c914a605000c3c0c8580d03000003a25000340d02e448040350800e406580015901c1c68034401058404840080000041c060000302503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 855867895 1250 855866645 855866657
    0xb0c0106050a08101404020f19050607050f0d0c0c06120b0a03050a12081303050d0905030325020c100c0606090204081005060a050a0303081005030109030e030c0102010b06090f01 78
    0x40780c590740308000c0c48010120710008008440020313030351006880303115030f00a405148090038072006a0350384403001e106a0781560141c207107101e203650102105900c2d0f406980c029000060030400e09c074011529005e01000042100c42d0345040e0081203543c0080b00c08003800a9090a40601440e480703140b00c0b82c010b1045020101d17885d007960f130000b802c50307242c0d80c000c46099001040300c004226400708800c51507131550074000d0356071a003110819000510386000908000d000a010044081680e000d101400d8111040b44e07100e04c0d0043c0b1191207000706800070840b040c0744540d03c0f0682480098040008140035116040c400e6410000342c0b8040c0c0300c1c490481c2c01907243d03040407403030b2280c52010700002c05000c00240000c120b1288144219880a0446406040010824003035602c810103000704999061400480b140e803414040c80040f0701e00e4201c0c3da0705500f003140309070505a2106280040c0e0304105c0a0b1041403051000581c22600141e03002c0c1d0f000303002841304034007501d071180c9101c48160040c1480 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 855869145 1250 855867895 855867899
    0xa14060304120e2d0a081027050c031009080d0b1c030503011a27191202101701180906020313120903080906031314060a050714040b0c0106 61
    0x5103074900309400d00c803145858200e10900020012218003640034007607441c04000d9081c428178903141c1f02000c41358914243c4410101c03140c4801559000712602c400d44100701001140d2501079280c609000b9000c1c400d100d540703002c0300030701102d114140d0081d912008051038414085a03840c050405100e0039544207680402100740a4005064400214400d64441d5036960422071020348d841c4122840e688800000c0c407c901e080022008589424034041180000629228001650450300219a52810040d032a0700041e03144140d0320741e0594501c2224070505508448808031444502d502070071440041d002c0c0104810002842121038600406001050700d5006480b070f9401e0380d00c1541c1d4140303a481000302c80c2040c480c030000c1c010200022842c181030000e2460312248141d0040d080907a21491001004c83d01c1582114402e02c0b4850340080103807606c80d0440304494488200300d446100383ca0034807000416183c4a21398075510740d1820b0000c00d05080c1445100445034002d101145001e640e50000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 855870395 1250 855869145 855869149
    0x2030a08100803070b06090907030507050609040e07030302010c0212090d11060408070e04020a05121b0a09110703110f0a030309110301090f030215061302210a09020a14060304120e 79
    0x11301c0030313601501030168281031001c14040403000092403801c06400007d0240001030000c5000780884004440b09511003011400040080c0050400e011191041d414000109074041d0081d01c0706041503002c0e0b036200d19007000500c00750311601a10540c0920b500055000203a00d00c2c0c4094400c42c8081d0a09043c5619064003528200321074000340310551a550400c82140b5001c6041c102524096800c0030306000110410303030b5100368440c2c039101e82c40006600000f8a8590240803002000c0614051284401c050021000d691100105400240448102c00002c210000e035100d1a4444e080040c0002c2c41d064404030000e10300c1103c206c90780c1c60703481c0c4411001d55003405070a10050042024039141c031b80500d00645040006c40e83c0e6450b01d4008420040666900074041c0b505070f80d500409139585001c407040212038950040541d40c81203c20382481000041548142c13106842541e640c90b01c580c5550007039114252403641585d1002c010000180000c1441d400d0f40c2c403290a0f4285a4155121440 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 855871645 1250 855870395 855870397
    0x3050706090c0807050307091112070c05100f0f151503020c0604032106052103070b07270806070c051207050604031202030603070302190302090c030f1602030a08100803 74
    0x2110f190960700c00041405203103010301420000740014642084001c1c66601400c00d1401082c4a8611941030b480026038040d01492141c0d121030742c0101903078502c4403032048290040114800b003d03280d03850705441c2c10049a45124080c880780354100081c0d1240c1c607004c0703c1c00c40c91f04609041400c041d002c1c07085160030082000b40758000ca102c1d440d00b000701c05086208094600d01780e0b020380e83d03040c2401030030841c603210314500da583d00104241248130101d21a0b03660f491403003583e0b0010010782c1c084c030402c11036035440b42020700683c08028151044030701c030018020a04d40d00307000d0900981c00c40004121400c1c0074041c1205064852401d0340c01a100c483c0030b030341e03680c0c1108100b550b8940018040008140d4815450105407409840450860910708003003581c48c1c10301e010007030003446045250f05441c01607040c0e0700c0040d079009203444014070b071001196446410946524141d024204080340c04806e45012144001030316a00550902a40030000c0f45d1954000d8200c00590080380d8000c96000800c0c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 855872895 1250 855871645 855871649
    0xa050903011a09090a0b0c0d06031a01081207030504090510271d0a0201080a1e0902100c0f060507170c0a0207060827030c16080105010905040f03050706090c 69
    0x310420342c0d40d4208414030540401c002c01c1002c0c1900310581900c0000e818141450308004c8130a9241e441c2e80c1030518080040802c0d400c058107907143d2003090410343c2c0c080d491380e6050307645d034106545c01d00c68002040303c11802409070040c04217405000500041c00d450313101071750210f001005900940d80c0ca400305480c1c50750f0b0a08907581c8407259006030141c24480c1c080d51600c13030355000b2800c10b00160148140e0311445581002410840200003150340c0225942040525001554481d4600403207188024000c0a039841c00301d001d62801c030140800b85000d160411030343c40d001204c1e107644031481e43d01d170700c01048010040c609018849500c003032040c41c2d0544c640c0c4541e081d11401030b031741e00b401c05000e0714117070941e48000d0402103070008006552101640b1102c1c0c04e5241c0c00c50b0b5560340060301039241035000340d000d9414540b02d07400d0380c104108004413000089526200c000c203c1662240041d209540d4215006082c1c040b4490f05003002030320a80042540e2801010005030240007a520758081600396 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 855874145 1250 855872895 855872921
    0x13180605041b0809060402210a02150a030f0608060414071e08060a2d0615080f070201091205090d1a06211b060d0615080702030913020a05090301 64
    0xb80e100100d03002d4025028982015403440149807510341580054100701011a440700496440341301196810020802e01405690081c13508103861075480317240780b0580041e0078810010741420707020301810f484d901c50001900d80f80e00180c0b500356190307280c1d84406400740d41003c40b0f134890140300041401081c072400f80c40380c840d01d00c0303806a00e1130003910a20f4079034050304814803245056016400400960014080203601481c01007454440104140040c54582c0c8418007806121350042c0401d944203500380c1c40703071100103d03800c00758860a604908880860314001d06a406040801000901030b10282611043c020000702a24103d540d42e120044004144080040a40c109105151030308120918225080c00480c014170420460001d035103008030808002c8206107034900041c0d50f01d5400c12182099000e03503040c04416540c2c40c00d082c50108010414000844010200780c0303841c4003000300d42070708500500c0c445802141c260118001c1d0302c100c0d240424005c0800c0140c540391000e01840351500c040e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 855875395 1250 855874145 855874181
    0x2101020c01020918100e15030a0b06100f02030403020108180a0609060c02030703270317130e0f180708012d051e040201030f09050c1003021318060504 66
    0x900d070144420a11103070113501c046103100d400c10202c0e07596a00c100c4101c44d4107078040003044d200d103094440c4503040200d03070a425018a801c4c50051002918500e405070f54245c9201074140e40701c1d131341260841e070950043d2005800070801000558415444645c02c485148036120000360007010071840c0131040e050440d801e84d01d589603041072100c0303403003964003031030709400a0761800d205c84d41c0050169580081003403155026a01d421111a00709403100b001d10703805283e0604500075120b104c4029000160303003e01d174680a0801040c09415100d142c0d000c0c29100c2c1d074512440d01c0b41c4654101401c0e0042d40f2602354450300c40d000a8415007405020710b81c000c0080302240c00b80c907e0301c020441c1c0f0320f0501e12201c0d807414601802260240252480705001c10505018125211440100c0c05882c0458551404504001000c0c05001d40440c0b10310080c0300072036220311500035103c4181d00360b0281c80389100d4100090701c4104500e94041c81d0b0141c0007540300c40300040171522000014111200c4604495903152 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 855876645 1250 855875395 855875407
    0x11e15121a16020727110c0f07060e09060f0a0b04030303060b031303140405090f0108010b0301111b0a0804061e1103250c0e071701142101020c0102 65
    0x105401c0540d04140320188208a0142a0790082d6843c0e1040c03080c00c219402d09041d0103d503000191010380321000c108020b000c5100800441c6480f90001e4126100740d0048094804007880000380b00c100711400c80d160b086500c03050301d0070000e110340c005050300d40081144501501c01e564220152014000051155840e64210308004007113424603008041e248000b00288514264014210451640d151800d031250305000c2000204034041c41d803010350003a11140520003202d980742440d80c146c03650403008000302c0f4030030707004c160a807a0920701c00b070240751040001114406650046801e080c280504079a070b0480e8558400305281e00590181e4001141210410b210108103036a15500d0500b6150144003060300751181c039103a2160011005e003e45802a405036544031409404807455009610000c1165641816071407007241202c0000001d502042441040321300e00405a05880d1040d94a5403d503400c1c030300380407500a00304200c40130700a005420744055003090000f0603c035407080e400035071a68 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 855877895 1250 855876645 855876683
    0xc0a0f020105010b191806020106030308060d030c1101090e1f05060310090f0b060d09050706050c030403150e1606091a03130305091503040c08011e1512 67
    0x1602048166046904000040046403130004c1a5100410418110009006142c505846441104130000351120000100150720394040d40708104581c02900e501ca5075546400800042414201006000c102101d80d00341c0416a110210240043c040c1454407485444241072800500201c800305520030180c2d0541028181c0225504c0003400155025411410050390070003443c000350042c00d020703a07a2807040c1280c10b00340340c018090040c00a0505980d60074011101409010945010b496070f11407140c00141d014442d604462041e400340c0d024600300b60031552826014107007018030740c51003510341382d102a80c182c1c2032100c8004101410f0400c2416481d102d0040c00c1c1d44101c0c1e1010300a81040080e8035510082042202e601244644140400000e0341c036058410f80514184d940e0817419040c141035aa2541200840c0120300030b0b400c98602654130001542a44c0d100c0301035211101d01309030034248403150350700700810714010407600480050320b8200c1c0d65540c26601c0002c2c1d074101d0087c1010a00f603 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 855879145 1250 855877895 855877907
    0x111c0603021306080316030201060b04060c0606050a05010912051e0f12030c040e040215031e010510090e07090801020315012019080d0c180806010501020c0609040f050c0a 75
    0x9886a000a021003072500131419101e0080000080d8010a0381040700d0805100f90300c808042c00c26040511b844507100d250050028a00034021200240742100c04941440c01c025000100e400c142c0d904c07008a824102d110342c0515900c01d04407018812041c042c092480d21400c442d030403182d4040200509000140381514184846851040307040f0208144540d80411000302c4060ba00c109035a68143d45651010070106a0340d02c4849020b95000b205000c000568130fa102818001c1190032001b060341c0702d4040000c114480720005002c2294003400f0400700c03100081a660080b030b44d0608811044d40d4149960a9a1045440f02070030028190803407055a0030001041e652413105c030000308181c0418501903501c2543c400c00b00143c1c001081c548040110700c0c400c450804885078000d01c084581044041c082c180101c03180c504c5104580404100f8030f000045603412140d050b0300070450030120300c0901c00c0b5517004560082c1c010342c5640c2e43c00c80b100240d00403d4003a480b07884800381c0d2000c10320360003090703 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 855880395 1250 855879145 855879169
    0x5030715021b010c0204050702030c0609071502070e04061d0304090b0103230c09030321010f0509090d03150e04030f0e032409160b0306100509060706111c060302 71
    0x14038105804031281640e01143c5122000c1d0705035000031f842d86400c0d034142d240d4010114007201030b00c110b004000d0f0b03004012680368105d51031b2020440031484401400da0316420a401140f00303144072080000e01140d5503402c810100180052614604081c0180c400d00315402600085030032501c548480d540781d6072510552411007400e41c0304c0e04041ea4219a55903604002500410400780041030031a080d5070140100c600c87c001070217981c2021000d101c101000203909108220f801e1406000014003424000f01544c800c1c00c0e418040c091025642c1030a40041400b2070154514504400c0040360880c2a1038849004600946030018040f50044005005941018260340207402c0240c0301f0b40f507076480400c204902040940080d25a54840e0031881c07402c100c0a1040382d41400c12000041d80d00b844200860180d08103849069020b04412070641d80c2c0e11800c00c0c40ca40020f01040b010002c0740c0789601c0514000d042e821154505090030b03541c084550440e1a40d20390303603a85e840c0c6c100118603041443d950 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 855881645 1250 855880395 855880423
    0x31e0406020307060b040f0f05190509060406111209031207030606020a03120b040212010806060f1c02012c040b190b070c0b0403030e090f0f0c130503071502 69
    0x4a01030410200035164003c0000041c00d064950b5141c21180e50b4035080f050302c0700e0260070200035000c0c80e5041d440240105403000000d250b290403070011404640d010b00344c881c00d04a402062542c60301d50340c20000300300c0b14040111a0109001106014840440003070007003180c1e100035601e41c0d2500015450903200130b408035050518040003001095004030b2040342a9825041ca000c0c00a490b6500e200945a0b4104155006100048c0d0b441020405018030b03059a00382d00480e02c1c2a60340c0414800b00d1091041407580c850000003140c0464501401c0341d100c0c0520600d07203c0e606001d0200d044040401183c40081c0c40d031072002c6210036a00301481007170b1601608070350f001c482d010047c0021840d10b0350350041e40b08070000040e14106028040000e0002007041c40d03001642e0fa03541e401c2c001d0100003c00780e0320f84113042c1c00d8046040101c00d50011800780c020301300074064685441c20030780d030b00307030701c0300c90581048855000c0004040e98140150740092665102c00c03050b031405604c000b8100a88004084 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 855882895 1250 855881645 855881647
    0x80105070e091636170a11010201180605091002040e070507081908010f080606030c100e15030603160e040f06020d02030a090c05040c172502031e 64
    0x450903644406907030f030b00110038000c8114418500d2100701c0c1c5609035040110b0031550322100006000040e40d0740c221414030024803140409442d641162224807180390059030070b603c1000c03d400460704450248441c3c040500002500032141c400c04143c080c00c4a10039903000b0b9841081250400003800203420009a5240c212714013410540000904c0c507000d42010200f10000c20303040304000187c0c049602d8083c0d500301d05109907140010080c8403190074080c2c0314420b81e12000006040000280c00d500640d0014042d14146003560280b0102c8074070300310440200151402c1089594440c500c003901da400600e140243d40745420401d040c43d00d418001c0c43c8859181d01502000010088158940c010f0f601c404500c0c4007a1072410000c019005465440c3c013514400014000e1030f045507030001da80030784605248644155a4801c22044a82d11480c03100480c008a800840492104281c260701804440c4443d002d0008034180301c0000c60200303034020140c0d000050000072070300c0720701c181002d140c1c18400361 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 855884145 1250 855882895 855882917
    0x30209010801180f08040e240a270b060a121a030a080702061b030915211009020708030a06090501030309090e0c04050a1e0203010303090b0d090f060608010507 70
    0x1d500c056443c0300b4040c0000382028080300420001d0701c210380060441e021800e5250400c0106500900340d0b1100c0200254684032410200307040c064600d4089034550881003032041284a401c01c80c508225010319007460351098501800d6440c90080c00e14907003559a1020074001182c4040210740780746007600d00308210800b40c81c6043e9000110310503443da01500d103079210901480410114001c105098900c0543c68502c0c0881e4540000500000081182d000810360040100c540e450b00c01c40c80d10758214800c0501503041503003100345640c0c126551510709108555501030103c1242c2144d0030071a059003002082c05004451802054060a200a030401079945540e07001b5101a480e482007044094649242111000040c0290194844060f00520652a01c0f8080c0001011202c941c0000302c0c0c12a644001041d8003442a40c1c1601d60544030700c048641010140756068100b0090074240c076403038074184000211643c1d1560b00da144a1304001c5541410301c2030060940740024010010000c00d03003c8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 855885395 1250 855884145 855884171
    0xa17100f050c0f0f0d0212090d0f02100b0a0503070b0714031206010318061e060e01050618061e1e1204030302030a060e0c1e19080a02120907030209010801 68
    0xf11039210030366201c8240c3d03c6400e605034402c01d010728403005144a2020814001d0112008906441100c0200960701c02540d0744005807451801840580010384c082d444180008446502680020000401d0665480e5032140080e14040003500000226100820700000708580300c14040c1d000240d54000c5d43c00c00e104d4110303003200c07131070300a184030704143d02c03030044d206004828903441c40c081d5080304c018401c0c1c04603e4141e4094444508484c03e6407454600c0014401050002943c103892000308a18a003603c01941c203200c075661119525404941049442ca030302f00b0500041c4c080d011103000c0c09803650f008521108410054074981500100104808204821404110740d8856498280142c0717079111105003500074081e9801446506c1042010b1056002100001d06028010a06c1c44421600303424030700301482c00341e502d1034401d04001c5c08101814a0060072160360005600c0b80046c02e02c140500800101c440680300e101954020440c14020350500b809958050300980000740004070003122 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 855886645 1250 855885395 855885397
    0xc030d0c0f060b040e0d020607030c0c140f06070c1211060f19061706101206091505011701050106050a1b020d1403180a0f0308090a17100f050c 63
    0x800600300903250607180100080b076030120b204410090f10400c41c01c0801004d1590f07418040c00c107900584905000955201d100e4020b281c20001c1d00e03900c0300304000302540c1d0725011480e54994010b413405401c1032071a81340e0080107894071800850761010704500b603500f084165000e03085051001c00030700010170302c0440300020b0f003280c000207068405011640c0d4400c0741100c5490b003004082549092000002d4811360170702d00580402c00c000e080d90444c1d203c40b8065a6007404905c912031044200204c96000324071164810840d0a009003001c040d401c5240d01c200007100c809030021002107240c440f07100f40c4034109210b0303075001d0000c2d41041031402800c458058004201c0c0b4540500c0103000300c1e185001c6450710800c0d15201c6a00c03043c14504040030207421a140c0d00240481d07030070011030715103008091400215000071a40c285100114a0b0704548801d440783e0302803484d21382c00413081000000c102d0118543c20341c84440e0322000c2c103e09451804d92000b81c0c2e612062042040d0b0400f4240500d185c0500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 855887895 1250 855886645 855886667
    0x1023106260603120c0c010e090403020a031815080403020f0d092d0603020403120206010302010f032c01050702250603020715020d0c0f0c12031503020a090c020c030d 73
    0x800488141d07403a107000a1800c01e000c40700e01d041301d20100c1d40c0c40f650000003d014280903c2600c8100d0302c20702200900920250441c1c001c2c0c0164070036183c0034040b030700441800d40c124a1038101c2003881e684400045507010042020030000032021000c000c103040d418428580040185400f40c03100300b00911008148038214000c0204805203601c0045400c0b01d0b0612115030550f801c2182088142d035554003030000c1d0014031080d64100c95032010032003c2440401c00c2c86c16242e050310ae0000082400350110300801c10b10400c10318401d00310301413840d41007c03c5030b108000d24003240003140070328210b10020304098880111120a0011078a5104500c41740c0100e0401d448030b500e001600d8030350a0600940d842024000c1d082058400180c1050711402c80d000805218995100e0000f440b250017000c4841c108102c80203040d21241d900150b41042c480c1d00f16440c1c0121440050003003a440e031700021300030b04a96100050059039180020380c00d6805200089041404901602c1c4490040d400508500280c0e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 855889145 1250 855887895 855887957
    0x4050a02060a03020d060b072303120c1204050a05010609111c06170307030e06040b09220c030f05060a03020d11060d09032c0d0602030901023106 64
    0x201c0c0d0b040b0031600c60f038162a100e074403030001448515502d0031100c80940c03000500307888040710304500007452000b4020000000c8406401180340042c00d104810507078001405040b03402e4010003000411403401d2401e03174003da002d403010b01001d45280c90071130708460340e03540400034450a01c1d030b24040c0d199409040d00c0074540c54005000003004a0741a000c01421103800040c401040b56424400030880003018008040c440d40720100401d202e40104482070040e1300c103006001c141040442c02da801c12003066041d07090560300c01ca0340710f82c80f1010403065a08a02c070100020703598a12514180005014a0350441d07415101352307180900f035401103509903e001c6000742c0341e0b41050103444000d441d48030440701914045413081100401915000b05462640700c11103010801160340000310710040126003d4001c1f004001440d05080c035a40d400181d04020b1900e08075540c01e02154201d249510303659080c024620701400340d50111034025006200d02e90708101c00300b215106a4040349110b1805002c41010a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 855890395 1250 855889145 855889147
    0x19030305071e050d08150901050d0f061d0610060c02010f1b03090806060a06090909080d05010b0c060c070c0314031908070f0e09010b0901090321110604050a0206 71
    0x14104004070451400104114182d6a40c0980a000010034111010201a07070380030244e07103030300c00c1440901c10300500003a4040c044800400c1540f03070100350740507803900c18252100308802da03441c0e140895940c0540c1d40141280920208100e41040c4060ce501c00b18181801e40c1050408800910900c90000001c0c10b1200c00c104030b400e41c0c1e00450203144d00034509100758141c140300c0d04d00103140e01c20f070744198031452081d50041122860040c0d011010303102e6598400711a0f40c505401a0054031b0622815503116000b04050301c402c101c240500b50182c14003c26965844680503481444c0940c01404002140e00501259001660010000c4100d079000342c45400414210411141140704075180080f181e007100d0165040301350440805403066a05403580b25810030004400c0c4c0d1145c0c01140e00c180d00004101c0144050b82c4440080e101c4d480046c54842001030f160743d50700504013a1510740c58900145103a642d011079034010580c1d0b007001c404002802c26400c0079035540f540c1c0c20750098021300c01d2034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 855891645 1250 855890395 855890407
    0x1140411120615160c4103100b0f1c02061c020a090303031104030302121b070801020d1116030c020f0a060c050f0607080f0601090515090f19030305 65
    0x2a07400c000340d101c10341c02003040fa07840c845001c102140c3c4810f604101d440310100b06001806444401c00213071030b03003200444c00c0100c1700143c0d944207801340289043c43d12503c3c031013060311654604208e01090012200800210701030ba0204006820b0034120b44103128250901c035524440c01400094200f055054500e40c0d160b815142c1c102c1140304199101d0140580b0100ea200f840307070350080701c07082241c0c080e88003004a031449030420ba02c9446980000350160348841446800c1c50b25401c01050400e070429460200350726081c120606189640d800003046030340108004401805a2003805012411a80c00320310b0001c0005940390741445c4100b020b404d0012014210081d500c582c80460a0f40c0d10040c01c0048054075110050250301320a0342c180c481e84903d9185903041c660000e8841d0040d001d03610b4031446079403010050703604c500c0e00a1059040080c1d01200081030344881503180c8a058500d0045a00d6400c600c041c048104800d11a4500c9650701c21618010f0001000300041625007528120355108 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 855892895 1250 855891645 855891649
    0x50a0b0901050f0702180411090c030601170a0905030307050c25060c15060b13080f0604120513090b100e0105030a1d0f01020318010615110a0b0f011404111206 70
    0x180d1b95a29041d5842c41d0004100401c40141070040b1001011200708580c0d480c1c04681d200280000c80d01d203404603c440004511903161032041950004d4004408110300082e6a9070b00c0c00d5800503180100400c50200d9800c0840009200e025410500c0c0022a48604041010300c5041c02c01880741809216407201c951041c804041d15502c0030410411017440100d41d50003019909034803600d1031303030000c1851140205014001213018981500b03001c006250503190f1380c4400b0301010311448003205100040155607603001e01c0b00c903e00020a81c1c040b00080c032021040500101c3c840700b0450710100041240340018603038118003075a0700541524400101946044410504842c944a0b1941c031031054030a01c0c10300000c150001c5100d100068900d4000062075101c590903500140a010440500240e0868540d889640c00200516a090071100c2400054540d4039406505580d81c15506100c000180101240b40032100003d00082c0c60401c4410036410101100d40900e9000d64401400ca60106140d6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 855894145 1250 855892895 855892909
    0x105070e090a1506020706032304170706090b06100e03070e090c0d060b0301062403020d11070b1005030f0304090b0607020307060903020a0905090d200f07050a0b0901050f0702 77
    0xb40d04048800d03030f14646842c00a503a4621612a81000909010039242c555110b89803200c03000760451554261a129540c1c0e0b100204400001040c04480074029000490b61600034042c107903002e10b50400e02401c01d01d003481450114405c40d182071181010000c41c2d00e440001d4101c048604001ca1030046445801180d41481d000598065001ba1620200d40500c0a9580403178500e4004070000c01c800782e50703155000008111440c03865070394594500da281e0014082d400512100510700c800080d200c04510820f4203940122105440c151100d00030446a416032089100140034100c2c020f1540001e095800383c1e0324801d13800b90a1041340c483c80c21040355100d401c203840200ba80101624903540e1034000c0244001c0003031000f40c0c81002d4840d03000078a0102803246130f009541e080d002c0e180c2c08440c000280d03650011700c184043d851a00703c1d415803d03000305000708919843c4041c05010120300c0c01d010050400d52030f8000d6014041c081002982680c1c121044442141030803400a461300c413140001112 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 855895395 1250 855894145 855894161
    0x30302060f100b2b11040e07090e040f0201030e0c2b0c06080f240906010c060612140f0d0f12050c0a0f0807090909080c03041d090105070e090a 63
    0x1c08440400c83c41d07100300703000f14605510f10f80c3c0c4c55005106066514050242e9500350044481c3c0d44d0108010f0141004041010368025401e0034468261940c1e041030805001f0101c405841d040d070540064801c660303160103210b04400ca03543c028010603ea17003000403041e02299058507410030341c1c00100c1800050405580070101d401c094100d0150365904805086908225100f0390b031003603071500158258a00303240804070036407082c0540c0d60841048043c88901c40e0081c00b80340c140725600b6040d800051141c05940d0150110040d08401410715240000c000e2444482948141c0c02050007807110350800107080401ca241481d022030302c00c8036106d040d00d1840c05008800106030408040114124001c0c3c02021080c22580d9686036030740155078112242c4000b0354100e00000c800340010440c003011600450b0103d405036030f119280c4140d00b0078551030b503802070f44400c10a05240d4604e01c640010450341aa20407c07110007440f80c0e10345510001d0990703140b0028580720f440c40b400414000c1415900c400c1c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 855896645 1250 855895395 855895409
    0x40e0109060c020d02160b0f0c1f0209010e040204231207121703071e050c0a151107050a080f040e100e010812030a0207031416050d0306030302060f10 66
    0x2c41d051410002e480c0c19007980f603880548130f40b002e600389040138002c010040700c094010103810202c9402d030303424650784884001c2038903200380e6021000150420f082000c0d102c040d1070700162b50300c1e0303807000251101400b50340442c8954418841001080e04a92246150b414040007503440f000140001032980e00403d0071009840c841c000e00031500c84200c5051095203805080d81d820001040c100c44c18071413101301d69490024806003036480c24510b060312440b800c00e050781402805d1441d041d043e2441d00c15610800d40d048031408111160080c0c09200d03405c000403510524500e0b020081d1541c6139201000c0030300030801080021800c4441519100317a07400307021500c0c402c56042c2040ca20340d10314807015014a890100303a02e03000081c040381c005030440800141e07401c1c581c10769440d0082d020094002003426824400041c07a002003105240f8001c0c49021040c41d007424441d602030601926000c105100c0c07100341440d04005001007a0006100e960095000b000304050380e4801e241c40c42d41d0071143d40300d41 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 855897895 1250 855896645 855896651
    0x90f0312141801020714180601020f0312011809030c170d050403050702010e120703110a0f0807030303150509010e06040603060204080f1903081f0f03080c060601090b0405040e010906 80
    0xc02060440a0039000490b00343d007110030f000c0e180c441190001c0290034a00f0b5120f0040300304001c00b115180385007640110140142d41100820b404c500b825a440700c003900e0038140b454401808280603118000084840d1200c0030032845035660f5010b000308015400c0509441c80d41c1c480302419150180c1240c0c0399911191083c04142030034034000d4902d400aa604030b0125001c02c100070072904100f411440e601c203002c0000c0c4601c52541d00c030280c884000d4401150414165a004100080e2206100008144680003001950300e507007030040072160030326602540d014000700d080286594040040f81514103511014201d500e405000900810080d8801016035001107000031f1080e00c0850b0f807440c440d0356641943c3e1029055059007000c000c1040008000c41c8002c030101e0b09158803100c86a4912115100003441d40340c031368800785041034080d401140d500c02c1c001038482481c0020701003150800020300b41404424103114100740030703020754062603011366900c3e202c0601b5100f0940001000f00d0f0484010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 855899145 1250 855897895 855897907
    0x705120d060315050115031e09080702031c0809070f060f05090405100609090b030a0b0402010c0f1511090a050609010201090615031707080f0702010e130f0507090f031214 75
    0x540141c0030911440312100d480151b9912928068020040007a44449a14043c09507c0a00e0001820139100946100300244070580041c1ca04001400c000e20140301c1000001c0701a85009009030001401ca803100d40060004000c54541e45c49150103440d042c3c101468200c6403030000302d50030b010310100541d2040c201000d00c010440440216001e0340c001c1d507201801e02d0388450450702901c40803203085030154072200c0340c44003095038507038202c0d041441458003140c1000e00d41c49808112080d03010070b0302c981070601e841044420041c85400311450703801c05040d0138000700301e0008000b03501a01c5082d009260004044070340c0d038801e510248001d948284200503002a080200d1480c00c96800200c40301c204161100e0311840800040d14401503002c981c1c10718101d40004188941e4000180032410f102e9140e0100109079070b1003030000d40d9200c6c0420002208180b021000c0140c1e54050101424000c0016051010b9010450614250f0350001814008454152030840300e100801c02045098038010601d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 855900395 1250 855899145 855899183
    0x306041812210605030a060902061309050717011508070201060803040e041407032604030b0a0b011205070e060711100512011a030f151c170705120d0603 67
    0x701e901003404203a484000180546042d008480060040580c15407203a030031500069095001580f003280b0142c00742c1e003403080c002e21441c0004219082032540944030001c000640e540480c8943c48052402c0d4a4451540341000300b540f0b596006e8005000c00604400003100b0038000d40000700100b45285c12240d0741c0c0e54548002142d4072060302e08239412140c0c55071000784448005003140503250050000c10181c0004103041c55044400400201000010300c80000401c11180201c1d01c5403030041004140303100e1400004010f02d0840071042a00c5113040706002880c2e5005c66095141c55081c1e074010366440361418103540d84d21160000c3c60f400141e80030360f03070405544203000d84003d41172100198402d0742c0725010802c60250010481810000c14000114100304a540c229040314660b54161445c2074440c02142c0685646102d8041c07440703c410341d5808021007e080c5801061921214505141d003940d51903882c2d040910b0400d6076410085110b691100066104c08015684040c03a09054100360117 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 855901645 1250 855900395 855900407
    0x90f031903020f060103030905010c030e040203102103140a031d15090102031614070b0a0b1009051302031e01061701050609010e061c05040b010302030606150306041812 74
    0x114010f0145a0b5a50841c00c03000038118180c0364191201c00d001803c0000445903160950340c01c0d01040784212110034562645e10003540a80c80c1c040e503240071a07003008444440010040d600044c0004103081d0380c07002c668052041039880c0398004645989142c45038003140a0010420514404583c40c580c4e8100030f54005034440044500350300c41da03050303654420070038203d01045401d11010151908680c940320311039840041c038042058821820003003c0c5c1c1794100400ca04503590380c03480742d0701c203100c010310300d008041214020400d240100115050001103103000c0326001c004202c003500800070036039042899004440384072801152038802d6940340b50041c01c400344030f01d000051148990002c981c0e42845421210200010707110440095400810700005520001d482d40d2007001c0f107040c0864100361401458000c5010b44c05081d03d55056004150601c9005401d40344142c14600d44105d500c4444401e503680000304a900044170310303a44a1290b0303030184444009100000f0440d032840d010360800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 855902895 1250 855901645 855901693
    0x12070311010207061b150f09061505010903021e03030d0209040513020d0b0403032409060510080f07140c010f06050f01090b39060a020906040b090f03 66
    0x30005582418140300680c2c44540e0b5000d914000381c04050888400b00618900d584814840c0342092001001c00041d14100e070340031600d07801c2c12900c400e0315009010306030256004040e9242007000a84c5d1414001801d00d00711480001d004040e01c1040700c01c045a07010219950003405000d0342d0745c2e2080e113026035000390301810b051131003a480d200119040c00d40c01003004030500c2d405881010700480d15140c003202118010011001c051712000c01031040d107244401244a80d12003204454020f081c800e04806445864000a0081e0402e501112405a02c49082038022084100d01c851588544004440380f648400200c1700c08a40000c41a40003041513100d00c1c249401501d080180984450400580301211031040340012001c1c10180410900200141000588100c4600c030401c05407510300c0c11041d8000c408004c1ca2001581450440320910155a1020003030b1811803806ca0b0076030008115002d68024814807a4004c100041c1c00d4460240c3e1040c01d880c001c084400103070f5103041140c4107200300d07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 855904145 1250 855902895 855902903
    0x120a050607050a110705090a0f09120504030c090515011805040626010b061b07051804050d0c05070b0901030f1e0c0201050c190212180f0d0302150c09120703 69
    0x104e03020303000301001140c2d4600751003008002124945603070710a84003821400c2e03107104006960b146035800148800c160740038058000c0e00c400392140e25505045030324200319403002e5961828282040300d04200402d815099a0702400e001403420041507102c000c20314a90440d60f00280f0f03007440420000c001ca16518030320b07140f107034005a600059400301400c2e181e103c200c9070382001040c404030008406062902d4220070b43c000480320080c2c0d650000510f801316111030b80700d00450400030312050000a00444012407142d04100641a42d01d9441c0396641c0098400c4150030040480c83c035010743e1083d0400c00690b10320440900c403030b4610307041c071200d0350280300da0240d4010b2800250785941801800b80c0f074491019612811308100074003001d21500142c8100346002c41c0155640e01380f10720310340e40140c0039000e08090300014201d90402401403640140414521a0420682500c0000c1c0c0c001110f120304406100c80c5411521030501d000ca00d400b81b5203201d54042101c0d04440040300c2c0000d00312003100d006e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 855905395 1250 855904145 855904157
    0xa1118190b0d2a020c06030a0b0306010e07080906090c060703030b0d11130b180402030307140609010b1507110625050d03020403020604170a060504051e1b120a050607050a 75
    0x2681c0b002d075400f0b120008030140960480c40003451645040000365501000000c0d0209000aa10340001d041c11008d80000d000906000f05001d0703540e030700045066011091100600d05401c1180301e066403071464850083c4a4100040c040d02003602c02d40040c990b1220107441c038035580784145004078042c00303080c85490047c0705540402420340501d00484801500107000040183c1c1045806001070000500c143e0b00f520040000750700041d00d4800d880360b007107a0f40010f40b000342010503001c0e09454940c4115803155600040c00c01d0000130710f104441e422507011420102204040e4081005801040c0c004283c001403686207030030422281042c8007015201d28103645582000d02c00030f40407406a80006900070b80280010b02161940c0b4403a030780001890000c8800800465440030203507041203500f16095084400b202e101c814507034050903903074610300002d071565003200600d2001d80000442c0303e0748181405240d0100c082c6040c00011015900101030303604ca854000340152543d40301121a03400901 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 855906645 1250 855905395 855905441
    0xd0809030111031603020c0f0312011503020f030c0a030e160305010e0f070e070509040f06060806220b060d02040b040609140108013005060a1118190b0d 67
    0x380c2d02085900c10080f41402403d480344840044000750801b00c0c0c0c1c050b191007034845201710b1010410103040130707851141050400c0c2d0305000e543c0c220840040e025a050500601002c01141c5001083c0c90740030300440c11698071110311400c01c030040d14101c0341e10301030390182691282407205001e4100703040c0c0340908024884410308941e0300d6503c481c00c0003148201c1d0401c81061021070042c0308210f070004814941035007864503540c00541254581080100003039615002003100e282c0001c54641d0201049814400e081d55005003143d80603c0a1459042345680e030a100f2403540d5542c066503071103c400b010854075103031110200c1041c0c0d8028002c5a0114010074000107a01400081102004c1010703541c0c00ea5507407030264040d0380300446015500e81c040b0340c1104002c0c5121030506080166000760300810440c00c100850708225003034070500e405520000c100003800c0c00e20b400c60030130381c1000a403000d41220103465120400f03400306401803d521400003e0000e80310300250070081c5100078540c08044009 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 855907895 1250 855906645 855906671
    0x90501020c0a03020105031b0d06050a08010b011d031e01090204060b030c0f0901030b040e0606041802031c020a08030103061a06041805060f181b04030b22020d08090301 74
    0x1d4081440994803012062040c4015413180c6c001c0e50308020380c511051250135000780c074003200e50011442080c0c00d0f40ea60800f00b1107403902c21076203001009900700070040c2805d2140001d00007055054000c00c10b013070203448004992800c004100c03500001c0c60046501c0381018202034083c00d5210010b038440d50610f000851804c02440840e4060b040d076a1b40380c0d207400121500b003202c681041c00481d05050742c421a1150985487c0120301e06082d0032000f500321498000e04102c1207440070b620b4140c1407121652008010b80b4000340403298121f0b90308101c0c549007440c00040703150a49000c002464040c01100000800000c4d4110382c0341c010074a0003081d85a1f507018207221a9001c1e078404c000e1416100000710740569400c2e44015042172003c0c00391810110544089401803d0f204520440c9284110070841c0340140000b04d1a081c0018042c80c0745001d241d51160041120084c007000c02085040d068020407a00d003052080117030fa80940785000c01e00b00c505041141d0342060340e19500035400c00803599406 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 855909145 1250 855907895 855907903
    0x1125080a03080a0507110307030e0109031e060509120a080c09120d030b090f060d02030a08030129040312210921020604050721170403170702030a062a020d09050102 72
    0x10039401700850420640303480030ac0e1414032503244141031154112001c40810441002c03041c95207a0380c001030518020a02c0d001c000c5403001060f030701c0e40b904502c80500b41043e45604031b0300d50900624040206440da01d507111315620130000d00941c0901981580148500e000c40c42c0d0a03600220b440401c4185445818802d03004411911551981d0402000880701d280202c50a402a40040c00300d626085079907031940c600749d0007070704007240070420301b05841040d0352540001300840301110502c5082500d59034030700f045200005010340511840c40c080d84074065000031f50072a503d2104e601030001c2201400c146294640000d1000d20090b080b001e03401e0054000118a1301641e0311100800d012490000d0310404c032001c036900e03000303494056081100030402c8420560045291400d003a642c4c1d51946c584000103110001a203c0141e005100d5000075035004142200c0309901300c4c8002c52003910b0f603103220f01c8001c003040e14500b480c28900d48407031030a980001c8052810b41d681c1c0b64500c090361150010380c3c0d1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 855910395 1250 855909145 855909167
    0x16140138190f560c1216390f0501170a0c020a060f050f09062a0405100c02040506040b09041205130b0901020d1125080a03080a0507 58
    0x10814942000c9891108164114080b4410f10700c550100e00c251403400e0400c2c05003103c0314071032000d03011401c02c00095040c4446100c100711907031210720b8a40b200c00400a5800f01ca80c014000d0701070389034070855100c511642c6420742c40521007200301c615026540381c414034501e80540040ba82c120b81c400b080d9540142c031a48801301c120002d441050b5200b41c00c003400b1f4980c4114403011030046003030700710006015014a1071300412180001c1000e16014031854600d4030000d0041209611007002c1c005444441c1216160a01030308140c0b0042a000c4d1220f1259803240340d20407900300c03401c01c507414040c1c0d89c0b0551040b80c4034404c0310103024a88500c0100420f807281000740c942e003e0f0b002400328001484252070b28280d10f9041c14074a00f0005800c5e101c0406940d02c1d40400074030a000030302c5e141c4540e0b041c0581400c2600034200882c1a00b80c0007402e030ba40b203420410b42202d444c60309201c0b84180a0b000800c400030401030742212081444c07803500815100c025111a1031b000e0414002c2901039019070081c4038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 855911645 1250 855910395 855910439
    0x30708130201020c040b030304090612020f0d0c0e0c041701021216050f090d06060305060a05130308151201051603061202060909041716140138190f 65
    0x10900c5130140400000b404001942c40e07061000b0440060041ea26010f0704000b403440b5403100e0700038030716401403240360074144110320311450100b90108002800380c00b841041c0d0b444110314400d40e035a072000c440d1580c42142c110006614072822541c1003e2415001014254420109041a5207594500301154803050034000017280c414031107040d070f03100081d01905080c200102814100d2045031900c8003100c01c50342040c1d41c80d030451403c00035110154000d06402101c580c01e003001b00400c1d92001048800c0c0030f031101949500b0240c009405d40d0b40c10550b04201e0420038000c00190a240f03440424810038400c2c00d001107801e100c00025203101140b9202c010503000307081c161400f2600e10400a54242c014011190211042c0c01000b059811501405240744408503110f5843c0072414008070f104100880f042c1c0d20ba0500c0307500300a400001c01484000250f42e2000184440c0380350b0303408415035400300c03115000701c0002084102c4820000c00c42d000c0764007400b00c0c02210340e1a10100c0800d5046458815 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 855912895 1250 855911645 855911653
    0x109060c0e010908120a03090f1a130b01060507020111011406190305191b081b220f020c010e060f0903030c07021309050307060b090106110613020a050a080303070813020102 76
    0x506020455402842a06c4207890700142038503e82c1e035048280f05031100b069034171024549540c0c2400004114068000b91030382110703040004141d4548030344010500410080000104810003164010498904100d81c5600240403114428000004002c0120784143c0302d1403401c4450407004252151f00e5042d42d0b0008003034144002c1c08003007a1500052254101c0380c0e1510602204002110340144002408629003d404030684440c21020b510f900d150391584103044c3c29420742b40c03681035101203400c0b0184101011a480d10101c03501c400a02444049003051750821601003954000880e1462245a014000030856120010490fa490000f11100682c1002c01c212017005840c05204040c14081184804144640c8550701e00d402c0d50850a0103d0f8410b07183e0b80400c02c10f141c003982c1c080c0548401d2a14848000501621560311400905a190403504010b5018150f481d074241c504043c02005c1c100103446641c441c01c09607a5031040354204006044840130440050703010540882c1c1c280c05038020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 855914145 1250 855912895 855912913
    0xb04050601090e061f05060403030201020d060b0c060a0504060209042a05030115141b06070311031018020405060a021f150302040507170702030c0f0304030b2202030109060c0e010908 80
    0x4890410300070030307117020529600c42c0008503075890000500195109900250700c450310103010030240c43c0c1c5d070707000055942d00a00100d0000350000403202e910031341c0d140002c0b6140d100c83c203002000b4403400000980042c00c0500704450741c26036108202c070721103815200303000350010800d04840c1400f0a000c2e0040c1d42d444a65601003d9104c3c40c0e801503100c00e0060703000d2400404015600211076800001314142d082107041151082d090300c510000000b0b0f080c0d40601e50318120700b003222200c00a002d018082d000101146d10904001d41c103441c0600030184c1840c3e0380e0500148007a40d42c0018822040b00c42410381e05200700301590780030310f803140740745145c4905445003194200310103000000c29940c1006002140c1842c69040b20240d50701a0300070f50041c503034818984220f5401e1404070700340ca640d00d034000c220030030004001c00046a03004540000f50110036116030b01d0030001860799400079515608040010092000740e602c001d120440729103a105900382c1e550010340d800c510a208030010340c0c00180c40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 855915395 1250 855914145 855914161
    0x31912050703180609080c0102060411063f180d0305090f010501060503090d02070b04060c0f1b09060e07080403081e2505131203120203040b04050601090e06 69
    0x140060728030a0070084481d910b64500015400d010341c2c1302d400014102c0e00100008a020320648405000030f1018058500e0540c880a2a0890301001d1074010800081ca060803021081b0010139080801a07818840b040740c0c40d0304540e02c00c800c4912240d03c1c8040d602041281080d950700d11001d84c03020010f030642041416094000f400014096015070140901c0088601c0080c441c2078003030041078982e140c07607040c01c030080d51600c1b02c80ca5040b0f0a5501000381442030204800558040362000c0c41c02c11b2603400c540c54038840c0001a0b07030b0000e1030220a034514400c0302c280e14600e6800c3d180b0700c00040200302c0e0b07500d0001160700d0302683d0001c04600700b1030114012030b10400c21b45901c2048045200d43d516071a44282d130300800100c8000e0041402c0b281d8100650820900041c0685035524001c0c0c2801d003081c101a2840810b03105d1403400c040501a0b00040500580313001090000b00a000c64692074981480c05821500710780445042c000c0600214450006100d0ba40046289200800c2180d9803114 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 855916645 1250 855915395 855915397
    0x403050f0114330a032906040b010c08030a060f0f05041103060904060e010b0d060b1309031223160201061e0320030607050a0206010e011a0a090306020c0c03191205 72
    0xe03103d904450b81c0c1201002184c0b80101000c2c00440020086810b024210070010104002a15442c0309504010a0035016a070001807640c07156007064401d9500d071075002c50311000300041d174012103441d11128000a2604d400d0100041114419102800601c1c0307181d50321f540500c0216481607100152101140100303030b42c0da2141800b8007400000142ca0152100003c0c8003490714070040f90b5040d112a40380c0d60b00d060446444034660400e1005108040890307401401d585040840071541d0343d595030061f201084001902601d80c0201030a150160800301d030303201c0891621110810244d0b00304100001e4504c0010a03a100c045042e1074021130403829580d441e60600301762840c2c007203910845d1100c02c94940e010700106000d0050f130b072103155440d06030640113428954141d010400918622004000803000d0002c20b0400d14a4410f41540c2d50320810000c0ea142c44441e000906002c0c8003041001d09088001140351108204030121103420303482896540204030000c10061591150360780c90424240118 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 855917895 1250 855916645 855916741
    0xf0e040609020303041518050117100e01182009120f01020a0504031a04051902041409010c030e03030603100b0312030c13150f0f050403050f0114 64
    0x210003207644201da4001a2031034006412881c81c01c030424418000700b9030406040001410401024400b10f0301d04400607060600c07941e600304228444200051348030300c0c10145400a0035041d81d080026503103605d150034a055030b4500c001002c1d4034080186103c140040703032140801e41180580f52501028100344084410403003401c101500c543c00e49080191420f00150214080c1a941e0340d44992540c103000c80b80c00303505604540d00011001c01d0201051000c503d40c080d0b4101ca5140521106c03140c4040340091a080030050302c8240390000f8420052410740007104945190356080c0b00780d03080c190105032a440152412a803560007a000406c0701d6034550082c104803030006081e103103803600172254561180c6c000c60700f145804200050b203543d100b000d49003c0014103180780e00d59201c0c101e11100030b070401d045071070031105002001d5003003030410748203800b02c4018bd035102090f540651810007943d03001c1c00d4030100c081c40240410002031a00c3c0684806556240340483c0101c0c85030307503001040307650001c0701c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 855919145 1250 855917895 855917903
    0xa03140109080d0b041503030c0f0c030b04140123011a0f0d091214071113090c0305062d13120518060405060d050603010209040c020d02060f010f0e04 66
    0x19003905011441d02c50203080c0e042d04400d4082202103001c0d04100455901940e160010a0794100505c04244c0c04000511800e0703004101c2c0c0c40060003401d000c07000300d1860380000d05200f031540800c010403030613402044140f80070800a00560710880308907a04e54072510091004014080010031000c2c1003081c3c50010b076859003504514024401090150940c401100d8030b00040d00d88903000108a001c401056400720545048211208564003280c454800c0c8000546000050012501d190395081503401c1c1ca042c0340745c410007003550302e07160403116040ca5100a417202d01034500015010410403075100362000c0003946103000c0900110012080c108043e140503010842d15005d0f400041010740b405003503152944680c2e0300c0e04898185102818014030130903000c1c510504c000c000c6503e401086c1e51907040c0d6900301107025994400482e0090141700e040641c810b042007154580c0c0b90b004919400c480000e5421380b24181c1e00c14042e8a1001021300c1001c2e0410140039081220748100c80b41d90344c1043c03003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 855920395 1250 855919145 855919151
    0x312111c0e0a0515010b0910031d01150509060301020c030708070f0f0609060e010b060d020a02031c050613050c070321050903191d21120403150207020a031401 70
    0xd401809032400b0282e0780e0888660b40005126821440c420380c0b03c0d401400c0340c019040c07801c08036030042200e071f00080c0403020070306482e0150501c0450a070300c141706603030481c14020030030b0b41c000c00c90210485407184076641c05100104c010519606041c001c64482908030b0780158a00040340d500d17032040b41c0c040d4105032041284440d29600060301c1e061781e00c05080c06504081116540c904188017155082e00314501310360b00d0700392007088070780301e080a5529003500341c01c0042c0c80e448480016030070b500c0744e0103001e0120403101c4039000200c090350b8000307801100291040955802010808011900305450b2858035120a11a04c000244566600800424145001d0200301e02c1c0039a50016200d0035101500540c0000c11030fa900b1b45019605503800100e946442000620036a8560705085801042c0c14040c461884016102c03940e00808507002080060440700c038a00720644007659908540011072340d01044001e0010100350354003c0c0c2e04c1090300100003500c41803031a5031b040311501281400c201a552 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 855921645 1250 855920395 855920411
    0x1507110a0b2a0c0d12031103010b070b01060c0c030b0408090603090c040c050f1c090203030417070f08030d09030e030118150507051b0313120312111c 66
    0x305005040c003124041c845141201c003140c0c01d900080c200c12010400d6a02000b009485a43c44d5007210345040e0b00000c070220020a0400206d014214441d03142021031000400085c0075071141e8010543d440c061070280d406644c80324000c07030368956202c074040c01039110400305101003074210400b10f800c0751045203540d00d000900d50109801e40c00840d440d00c4241c008a014000c203046c580216400a8020f10b051450000ca105841031140100403101071880c85100143d0761004081d44803172500e54000301100d8485035100aa80104001000004818003621800003255429081042d05440d07030700f009076050a440561200003450107500580410000500d140c003e84c40a2080341144482d40e10140309088460401000803540300c880740c1074035413404041003c5039500034150b50400780181d600d0049282d5106141d890750003820700d07606400050550003c4c07070400268031143c400e8070036100d03001b038665050300e034074100c40b05201c0202d1440001c21040700940c51850405000810040b00010800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 855922895 1250 855921645 855921659
    0x1b0408070308090d170c0105010b0406050a0e0d0f080a03150b070b091e101b0801050909101109090601170105060901030f091a0a060503191416050f1507110a 69
    0x305d03040d9004900041c000440c01d9002c4002c0c01070f180945100d50441d40340c1441e009004150348102c182040420410400c011117544c3c0b81e40b48040030320780105402c83c40055a08140c400c0b0f0384a8000c10011a00d000d0550b045003940c0d45400045581e04030038a030501041c0d4803000303c0075400504503000390244c050340180c02800c40060040d0030b00c03200004d14141130100881030441c0c00c00c2c091009410400310040c0800d680c031440d01415100c060f201804651241c0305628a4032041c0c003032244400742007444440d0b2185110014060401086400c60300d81e40b43d00005454400d0402da0b1244014080401402103092190040c4a10750040c940002c2d80761004c4102412990307402000c4600240c04a048000d00d14241c0074160040c20580041249519001c00070391386403c41b04050345101e044001d4402801641707030b07c02c408a0f0219050320003500200709a441d4142c3e4038007442e4800c0d011040c1160b01400c025000f5484111001d8849107400c2a07a242c0300f140c0c003000803505500c0719070321101040b61 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 855924145 1250 855922895 855922913
    0x80f090a0336090605090105090105041d1c031a0a030321180303061a120402010c0206030f0f1b16050307081303231005060f12061b0408070308090d 65
    0x9a00c41c0d282d00148030700740325100040d50074a9100c10711901c4880c0c0188070b250f90310103516044030801c0701c002420200540c1445c40780c848020281915000d4114180421800c00300311540720300e620340d0108202d511203090321120000724002d00da08040c42120030301c0081d010b81c901c401a20062003a00700e034103406404000540c0d0441140341d407111049030b11042019058020ba031301a00100d401010540c00d00310080006003e80380d0b1002e690840a4042030070341e4081d0090119494000e8041685ca1524501003804090180c54220641a4007400a0b415205040d8104480d0111604891510301441c1018294901c01c80c400e072014002000848006031440c0002d02104080364043e4002d6403842c1071044d2100c20348807003501c036428031840c40140503d01040307845490808010000300c80e100e07940498040882500c0707460b00580c4542561b00f811000042440c460103407007003c54080002805421094004d81c451012140d112540038000215000e01030030754518042c0142c01840f80f81d0b00ca10080c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 855925395 1250 855924145 855924227
    0x120b0402100e13021201050904150504030c060608031207052119050f10060c02090f250509040b0d030e060a050c0d0c0210031b0c15050109020901080f090a03 69
    0x1694000743c45ea0110018148140c0140400c0340d0031412442c054450703042e036507081903a545920b640d40e00080d04050180e0889140301ea00040c080042c10f0301c42c801182d0741d81c84803281c6044032644031b0008a015100b4411189185106100355252001c2d03101094007040000c1c0c92103690002103585168141c01e584202440f404100e52440c605090100f1240c003031803440e0304410204242188501c000d81c0351403039480c1d0041c9400c8400002d680d14030822031504900daa45082400016a50f032061813540000901040c4074216030401c00c81d034a02041014401402d1030080c0861f07400e4090500928016018200b48811414018600b0004a03401c50030069148403031008144917040d48010b40c00d043c0390101c0a80d0b071508040203401008040c41f809a103000380c1a03c10024082c40c0c5108014240c014030380c0f030446582040c0070f15611404071102941000f102240058285000030b0000b402d040b10190150600401800c00201d4980f01140c0e8211010442c2440031003414201c051202d4540903904 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 855926645 1250 855925395 855925429
    0x24020102160303150602070e01180b040e060a0b061603030207081306020618010207033905010c0e09040c0306020f21070f02010608120a09030f030503010e01120b0402100e 75
    0x1841c041640044d041254241d003050f000c65102100c10302c0041090f06000d07056418212043d184044d600485034007400740424a81d821078209202241c00620020701c140c0580304c128401d02c4400007074002d104841c00740c08000c2d500700c00c00820080229000c2d600820020307015020840c68020764003411507041e040e96004000581c010000c101071079a405d452400e064814000030742c0352104a0710000c0c4003c0312000c491059803070041e601c034907401820002d51004501903120700000606030402d14000c09440c820000441c2d8001103e81a900e008100d85200720340c48004607161b5819510788800039000000e181250000400c0305240f0501140110849448100610002484e1601c0010503000406081c0415603041c004c040c0442040403c01c3c81984440301300094842d4520741049600201d1544050b281150040a940c14035a2081c02141030711240141140c80c0c1c2d036150118013100105601c09000c000300480410010b160250070303e04000c0c0c1518100e01405406400030b05c4900041c0c2b9114 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 855927895 1250 855926645 855926651
    0xe04050a150b0909060f09061504050a0807090e070608070e0409140a02032b0e130509031e190e0a030507141e01052d0403030906031524020102160303 66
    0x11203d841d0803035805a200a082e2030101e0410b5418000c69003c02e0b000c1c0095200701203102c0100302d4a86e0083c00d0300c0003000000d040060320b55403602c1c80e989444241c055805000d003001c8401100d941c00040c14003c4801d00d9948940d2031b40d810030222841000002250385c080e80302e080300004146585060b41c201e41110000c0d10704405c9a00c10540380c66803488400000482e04241d0b00340c0854100c40720480e1000c1410042d01034a182d000240502e0001255032032210f00d0241071260034030b4000003900f03041c4211258404801840c420504042c0904001c694009210080044441e84200005c521150010701242401a125981c450a25020b41c20480341c10052151101541c89c0400f051816510b10441d0722000b14003960000b44107205042c109022004000a0142116003c0200350f204034004010540c440783c507440c1c01442c0604501c5108006414000461610f000c5005884100c41c000300d403110f0b1072900005180320007800c032540170007595828004207060994500307034901c05502c02d541c00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 855929145 1250 855927895 855927907
    0x1030509030a02120a05043b0f13060209060309010e06010909150216060501030b060a09050c090909150c090a0602010c35040c05031540151b0e04050a150b 68
    0xc4004000b07032103c80902c44006000b07002c051304181c20450340244041c0ad440c0095500303030038000041e10490400ea1f4002e2000000c01c502001c040d44020890500c500c103880f956666504603800b65940703801d015040d11100c402c0b216030f00c0c0c441e50042205005910104960598545400e401c4401c00da105071860f00c2030400300311a901d051101d903005862420410007045c10446c0e0b4003881e038018400c41500038014040441d8035030a003002030030070405c14440d07500b50034602a030030080d6076008000a00e00032020184045101401801070010044060703075040000611a80c0f5021100e4140c0d401c3c910300d424901410b5901e0307000c950a68440d038001c81000d5109c03403030032040c1072400d009a0721441e1500c00a1050010200800c80d5242c821010242141180d0203551301e450444007003c012120200300075801da10802c1248500001114080d01d01000007809840381e40014054060a06001400800302e490b61840c0c69480355820445080d80098502880d414490040c055038011b05001c0c4008222 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 855930395 1250 855929145 855929219
    0x40510081b01180315021e0f0a02010c0c0506130201180806060a050a0e041401180b0906090609030d0527030c1902010c02040e15130201030509030a02120a0504 70
    0x160001420f888000c0724201e25540b078910500b1407a000349881160001070030b180c103a4500d0260303503590f0240640c0c259100c0400c620301025900c00030407a4055403c2210000c8100d0041d110a00403d401101030300e420303035030031400444089002030228140115040221450b11a4480110160541c20000c01240c00c1800801100d0f0400d80d05c290b10a8600000034814248a440d0700e40c2c001c2d0f8020f00c0c00503d0bd1100518a001d800c6038110324003041100890340050140c070304200c5000b40c1c101015510103442c0c402090782c50f0303041103403021807661080100315a03210056000c50b80c0695200480c404489103540d00704070f44400c107803210420307500c089a0311000400500803040d80100300c1b410b81c07411841070390003c0c020840b00c640291045555060180c040081801400d803440d07070405020803607240501c150030040b000144240d000920340000510700450002c00c03200585402c2c1c00900c17100610b2000088154040f01d110030030000103000005549001d0780c24030182c9811002c029251180b0444 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 855931645 1250 855930395 855930407
    0x10e04052b080109110f0d020409020d0225080f0c0f07060c050706020c030706030c020a020d061a0402030103170a180609060f0e0d080d0603080c0706020d051206040510081b01 77
    0x32440d03400e458100d03105c0c00d02480340110343d480c59683c0c09850320b0340c0380d500b21800203000b1580072001e080c3c00010307480d9160509900400081032101000303d840030103007100340d0b109418844010300c200c1080088001d20034a030340244c504107268200b00d400800805103280d080204580c00040403640760004001007104c10b020b2603000d03100b60f10081c2105d244d16030019644004c28802c0f501071680d5070308202d0009109020076840c0d260068041100000da0307213030a500800c0882101c4c200301030705100046041c03401d1300880b030490350030105d1000c48811081100b005540240700e4002070084c04601005941e409001e07000044c4441e40b261520145410409012040c58808407410030400c041c2c0f00d800c0e961062008040340790041701c0d15440b1003000030000020f0403150030240c04113002003020009000c1c0014082d05882c1c01e6030036540b503042d1042c1c06071031500034042c0c5a600c0211500018916080075807085500c5084030003c1811180c0d9200c8203410034140e0500754500c1c00b100d481342e110a5030445 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 855932895 1250 855931645 855931649
    0x4030c050f310615020c0a15090e10030c08031c05130b0c0c030c07050406080c09040b0402010e0907031a060915030a0e07080a030e0904020603010e04052b0801 70
    0xd038008007110340700c1080030b07581941c0500240002c0c811103102e40b1102402d900a0000e04222031031134001e445070600195035021b0b13181c0264466155140301007801d40d40c00c022107042444545640c0c48082c10310b100306260b024020104418031740003c00000c0070070010442c840041c00c210025651341d00d484004042c141c642d0a03003c4038103501749800d021103208904800d006940d0404050703107081d20782d02d11100542c41f849280b80c010748008113410b0100c0d4004a00c510844004031000c100240d80c5a882e1070303d0b4505000560ba01c42075400000703000c0323007581025540c40b82c81490042c030310080b003200146043c41300f940d0704030000b07039a100700040840e8050103852006908480c0d40703003001c03100400101407a05161761012061404000f00e448091075402502e1300400940c10340300346580b1005c04c16a00c0c0c0040320158002803480c0c1d4026a54204041024003480d000f078030035461a801c08640913034101010f0400c0b901441070419a2005a80210400300c00703070000001007079642021040180b0658040e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 855934145 1250 855932895 855932899
    0x110c03130e010b13030f020135090721080c01020a0c0b0906010321140706090c0e1909260d0c0302030c030105010309020a15030b1c02090a020313060204030c050f 71
    0x30080e01055460031031394082100d03800400070325410301510040356001ca000c20300081218007100d4074030003d0189540d4518601485801001940d44c0030750142e0340b5030552195445240e100c01c0b103000140b8500c4081d104013402450b003241b80900b181325541c00c980c484140e600c00074107a070104d0410880e5100134240c105041400429040d41141c40b5880503603401c0104990308055124501403881c0241030040b08541041c140d203407110b42500340600641401403003194400003c1034003088506510081c14091a00c221054050100300c44c5074400a1210360700507140101d182e42d40607000130030710100490941c16500240e03201c50079509030340180c40001e031001084c1030042c010003100c4035065042d42d044031000d103401305044078a8000304594040903003040103815141d21207042c085401d5000801507090a90304104520070600c2c00c3d5950200c2e04038003e50200c1480b01040100500d60091500500000c850a540c1926070352880100ea106600480f010404400c04005500e03004d09000c10701001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 855935251 1106 855934145 855934147
    0xc0801061b020a18050f070c020910270b0103020405060702150f0a0216060f120b0411070501090c0e010f061115090c10030c12110c03130e010b 63
    0x82141315030b03881d504000108a655220352a1a0310407a81952810a04942a42000707902e080c0940301d40d8040701248008100562a800b0700038400c070f0645907a00c80c0070358041c651801e413603104a089041c1817041c00100300c1a1504021500901c3d4100c1e401c140d0f00700c0111003050305015a001c1c1c694034540104107451301540000302c407106010200600341500350381d004102e400745200300b07544000915501808078a00c070190800d6014a000070301c0810038040c400c46103600d603040768400f603510341e44800c0385a051003d0341310304101928040116909640c1050750140700025a486110708004100f100074040705030602c4440e4681083c2007601006003010301c8030340d54607a4031900c29403080421144031500a80a442001240d101c80d441c1c6a41d40c40c040380b407070030003440c0b141100001c081040010401c680824002410200e0b80704a075224010f0900c0c3c182c408c2810160099524848 = true := by decide +kernel

theorem cover : BRFrame.Cov 855755395 855935251 := by
  have h0 := BRFrame.cov_init 855755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 855755395 ≤ n) (h2 : n < 855935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
