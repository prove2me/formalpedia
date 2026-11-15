-- Prove2me | solution 1 for CodedSorting.proposition_7_1_transpose
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-14T20:08:34.551532+00:00
-- url     : https://prove2.me/submissions/7dbb67bd-716e-4765-9f33-080e9d81ca77

import Mathlib
import Definitions.Def_CodedSorting_Columnsort

open CodedSorting
namespace P2MHole01_d4581f93
theorem solution (t j : ℕ) (hj : j < 2 ^ (4 * t)) :
  ∃ x1 x2 x3 x4,
    x1 < 2 ^ t ∧
      x2 < 2 ^ t ∧ x3 < 2 ^ t ∧ x4 < 2 ^ t ∧ j = x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4 := by
  let x1 := j / 2 ^ (3 * t)
  let x2 := (j % 2 ^ (3 * t)) / 2 ^ (2 * t)
  let x3 := (j % 2 ^ (2 * t)) / 2 ^ t
  let x4 := j % 2 ^ t
  have hpos3t : 0 < 2 ^ (3 * t) := by positivity
  have hpos2t : 0 < 2 ^ (2 * t) := by positivity
  have hpost : 0 < 2 ^ t := by positivity
  refine ⟨x1, x2, x3, x4, ?_, ?_, ?_, ?_, ?_⟩
  · -- x1 < 2^t
    have h : 2 ^ (4 * t) = 2 ^ (3 * t) * 2 ^ t := by
      rw [show 4 * t = 3 * t + t by ring, pow_add, mul_comm]
    rw [h] at hj
    exact Nat.div_lt_of_lt_mul hj
  · -- x2 < 2^t
    have hmod : j % 2 ^ (3 * t) < 2 ^ (2 * t) * 2 ^ t := by
      calc
        j % 2 ^ (3 * t) < 2 ^ (3 * t) := Nat.mod_lt j hpos3t
        _ = 2 ^ (2 * t) * 2 ^ t := by
          rw [show 3 * t = 2 * t + t by ring, pow_add, mul_comm]
    exact Nat.div_lt_of_lt_mul hmod
  · -- x3 < 2^t
    have hmod : j % 2 ^ (2 * t) < 2 ^ t * 2 ^ t := by
      calc
        j % 2 ^ (2 * t) < 2 ^ (2 * t) := Nat.mod_lt j hpos2t
        _ = 2 ^ t * 2 ^ t := by
          rw [show 2 * t = t + t by ring, pow_add]
    exact Nat.div_lt_of_lt_mul hmod
  · -- x4 < 2^t
    exact Nat.mod_lt j hpost
  · -- j = x1 * 2^(3*t) + x2 * 2^(2*t) + x3 * 2^t + x4
    have h1 : j = 2 ^ (3 * t) * x1 + j % 2 ^ (3 * t) := by
      dsimp [x1]
      exact (Nat.div_add_mod j (2 ^ (3 * t))).symm
    have h2 : j % 2 ^ (3 * t) = 2 ^ (2 * t) * x2 + (j % 2 ^ (3 * t)) % 2 ^ (2 * t) := by
      dsimp [x2]
      exact (Nat.div_add_mod (j % 2 ^ (3 * t)) (2 ^ (2 * t))).symm
    have h3 : (j % 2 ^ (3 * t)) % 2 ^ (2 * t) = j % 2 ^ (2 * t) :=
      Nat.mod_mod_of_dvd j (by
        use 2 ^ t
        ring)
    have h4 : j % 2 ^ (2 * t) = 2 ^ t * x3 + (j % 2 ^ (2 * t)) % 2 ^ t := by
      dsimp [x3]
      exact (Nat.div_add_mod (j % 2 ^ (2 * t)) (2 ^ t)).symm
    have h5 : (j % 2 ^ (2 * t)) % 2 ^ t = j % 2 ^ t :=
      Nat.mod_mod_of_dvd j (by
        use 2 ^ t
        ring)
    have h6 : x4 = j % 2 ^ t := by
      dsimp [x4]
    calc
      j = 2 ^ (3 * t) * x1 + j % 2 ^ (3 * t) := h1
      _ = 2 ^ (3 * t) * x1 + (2 ^ (2 * t) * x2 + (j % 2 ^ (3 * t)) % 2 ^ (2 * t)) := by rw [← h2]
      _ = 2 ^ (3 * t) * x1 + (2 ^ (2 * t) * x2 + j % 2 ^ (2 * t)) := by rw [h3]
      _ = 2 ^ (3 * t) * x1 + (2 ^ (2 * t) * x2 + (2 ^ t * x3 + (j % 2 ^ (2 * t)) % 2 ^ t)) := by rw [← h4]
      _ = 2 ^ (3 * t) * x1 + (2 ^ (2 * t) * x2 + (2 ^ t * x3 + j % 2 ^ t)) := by rw [h5]
      _ = x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4 := by
        rw [← h6]
        ring
end P2MHole01_d4581f93

/-- Any `j < 2^{4t}` splits into four `t`-bit fields `(x1,x2,x3,x4)` (highest to lowest):
`j = x1·2^{3t} + x2·2^{2t} + x3·2^t + x4` with each field `< 2^t`. -/
lemma fieldDecompose (t : ℕ) (j : ℕ) (hj : j < 2 ^ (4 * t)) :
    ∃ x1 x2 x3 x4, x1 < 2 ^ t ∧ x2 < 2 ^ t ∧ x3 < 2 ^ t ∧ x4 < 2 ^ t ∧
      j = x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4 := by
  (first | exact P2MHole01_d4581f93.solution t j hj | (apply P2MHole01_d4581f93.solution <;> assumption))

namespace P2MHole02_07430dab
/-- If `X = Y * B + Z` with `Z < B` and `B > 0`, then `X / B = Y` and `X % B = Z`. -/
lemma divMod (X Y Z B : ℕ) (hB : 0 < B) (h : X = Y * B + Z) (hZ : Z < B) :
    X / B = Y ∧ X % B = Z := by
  refine (Nat.div_mod_unique (h := hB)).mpr ⟨?_, hZ⟩
  rw [h]
  ring

lemma pow2 (t : ℕ) : 2 ^ (2 * t) = 2 ^ t * 2 ^ t := by
  rw [show 2 * t = t + t from by ring, Nat.pow_add]

lemma pow3 (t : ℕ) : 2 ^ (3 * t) = 2 ^ t * 2 ^ (2 * t) := by
  rw [show 3 * t = t + 2 * t from by ring, Nat.pow_add]

/-- `x1·2^(3t) + x2·2^(2t) + x3·2^t = (x1·2^(2t) + x2·2^t + x3)·2^t`. -/
lemma regroup3 (t x1 x2 x3 : ℕ) :
    x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t =
      (x1 * 2 ^ (2 * t) + x2 * 2 ^ t + x3) * 2 ^ t := by
  rw [pow2, pow3]
  ring

/-- `x1·2^(2t) + x2·2^t + x3 = (x1·2^t + x2)·2^t + x3`. -/
lemma regroup2 (t x1 x2 x3 : ℕ) :
    x1 * 2 ^ (2 * t) + x2 * 2 ^ t + x3 = (x1 * 2 ^ t + x2) * 2 ^ t + x3 := by
  rw [pow2]
  ring

theorem solution (t x1 x2 x3 x4 : ℕ) (hx1 : x1 < 2 ^ t) (hx2 : x2 < 2 ^ t) (hx3 : x3 < 2 ^ t)
  (hx4 : x4 < 2 ^ t) :
  fieldSwapAdj t 2 (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) =
    x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x4 * 2 ^ t + x3 := by
  dsimp [fieldSwapAdj, interchangeIndex, bitAddr]
  simp only [Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero]
  set j := x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4 with hj
  have hB : 0 < 2 ^ t := by positivity
  -- low digit and first quotient of j in base 2^t
  have h1 := divMod j (x1 * 2 ^ (2 * t) + x2 * 2 ^ t + x3) x4 (2 ^ t) hB
    (by rw [hj, regroup3]) hx4
  -- digits of the quotient j / 2^t in base 2^t
  have h2 := divMod (j / 2 ^ t) (x1 * 2 ^ t + x2) x3 (2 ^ t) hB
    (by rw [h1.1, regroup2]) hx3
  simp only [h2.1, h1.2, h2.2]
  rw [pow3, pow2]
  ring
end P2MHole02_07430dab

/-- The field interchange of positions `3,4` (`i = 2`, `G = 1`, suffix `2^0`): it swaps the two
lowest fields `x3·2^t + x4`, leaving `x1,x2` untouched. -/
lemma fieldSwap2 (t : ℕ) (x1 x2 x3 x4 : ℕ) (hx1 : x1 < 2 ^ t) (hx2 : x2 < 2 ^ t)
    (hx3 : x3 < 2 ^ t) (hx4 : x4 < 2 ^ t) :
    fieldSwapAdj t 2 (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) =
      x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x4 * 2 ^ t + x3 := by
  (first | exact P2MHole02_07430dab.solution t x1 x2 x3 x4 hx1 hx2 hx3 hx4 | (apply P2MHole02_07430dab.solution <;> assumption))

namespace P2MHole03_00d68109
/-- Division of a multiple of `S` by `S`, when the extra part is below `S`. -/
lemma digDiv (m S c : ℕ) (hs : 0 < S) (hc : c < S) : (m * S + c) / S = m := by
  rw [Nat.div_eq_iff hs]
  constructor <;> omega

theorem solution (t x1 x2 x3 x4 : ℕ) (hx1 : x1 < 2 ^ t) (hx2 : x2 < 2 ^ t) (hx3 : x3 < 2 ^ t)
  (hx4 : x4 < 2 ^ t) :
  fieldSwapAdj t 1 (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) =
    x1 * 2 ^ (3 * t) + x3 * 2 ^ (2 * t) + x2 * 2 ^ t + x4 := by
  let j := x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4
  have hs : 0 < 2 ^ t := Nat.pow_pos Nat.zero_lt_two
  have hs2 : 2 ^ t * 2 ^ t = 2 ^ (2 * t) := by
    rw [← Nat.pow_two, ← Nat.pow_mul, Nat.mul_comm]
  have hs3 : 2 ^ t * 2 ^ t * 2 ^ t = 2 ^ (3 * t) := by
    rw [hs2, ← Nat.pow_add]
    congr 1
    ring
  have hjS : j = (x1 * 2 ^ t * 2 ^ t + x2 * 2 ^ t + x3) * 2 ^ t + x4 := by
    show x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4 = (x1 * 2 ^ t * 2 ^ t + x2 * 2 ^ t + x3) * 2 ^ t + x4
    rw [← hs3, ← hs2]
    ring
  have hj : j / 2 ^ t = x1 * 2 ^ t * 2 ^ t + x2 * 2 ^ t + x3 := by
    rw [hjS]
    exact digDiv (x1 * 2 ^ t * 2 ^ t + x2 * 2 ^ t + x3) (2 ^ t) x4 hs hx4
  have hd : j / 2 ^ t % 2 ^ t = x3 := by
    rw [hj, show x1 * 2 ^ t * 2 ^ t + x2 * 2 ^ t + x3 = (x1 * 2 ^ t + x2) * 2 ^ t + x3 from by ring,
        Nat.mul_add_mod_of_lt hx3]
  have hq : j / 2 ^ t / 2 ^ t = x1 * 2 ^ t + x2 := by
    rw [show j / 2 ^ t = (x1 * 2 ^ t + x2) * 2 ^ t + x3 from (by rw [hj]; ring)]
    exact digDiv (x1 * 2 ^ t + x2) (2 ^ t) x3 hs hx3
  have hz : j % 2 ^ t = x4 := by
    rw [hjS, Nat.mul_add_mod_of_lt hx4]
  have hfin : 2 - ((1 : Fin 3) : ℕ) = 1 := rfl
  dsimp only [fieldSwapAdj, interchangeIndex, bitAddr, Nat.mul_one]
  simp only [hfin, Nat.mul_one]
  have hz2 : (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) % 2 ^ t = x4 := by
    show j % 2 ^ t = x4
    exact hz
  have hd2 : (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) / 2 ^ t % 2 ^ t = x3 := by
    show j / 2 ^ t % 2 ^ t = x3
    exact hd
  have hq2 : (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) / 2 ^ t / 2 ^ t =
      x1 * 2 ^ t + x2 := by
    show j / 2 ^ t / 2 ^ t = x1 * 2 ^ t + x2
    exact hq
  have hp2 : (x1 * 2 ^ t + x2) / 2 ^ t = x1 := digDiv x1 (2 ^ t) x2 hs hx2
  have htm : (x1 * 2 ^ t + x2) % 2 ^ t = x2 := Nat.mul_add_mod_of_lt hx2
  simp only [Nat.mul_one, Nat.add_zero, Nat.mod_one, Nat.div_one, hz2, hd2, hq2, hp2, htm]
  conv =>
    rhs
    rw [← hs3, ← hs2]
  ring
end P2MHole03_00d68109

/-- The field interchange of positions `2,3` (`i = 1`, `G = 1`, suffix `2^t`): it swaps `x2,x3`,
leaving `x1` and the lowest field `x4` untouched. -/
lemma fieldSwap1 (t : ℕ) (x1 x2 x3 x4 : ℕ) (hx1 : x1 < 2 ^ t) (hx2 : x2 < 2 ^ t)
    (hx3 : x3 < 2 ^ t) (hx4 : x4 < 2 ^ t) :
    fieldSwapAdj t 1 (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) =
      x1 * 2 ^ (3 * t) + x3 * 2 ^ (2 * t) + x2 * 2 ^ t + x4 := by
  (first | exact P2MHole03_00d68109.solution t x1 x2 x3 x4 hx1 hx2 hx3 hx4 | (apply P2MHole03_00d68109.solution <;> assumption))

namespace P2MHole04_0db9687e
theorem solution (t x1 x2 x3 x4 : ℕ) (hx1 : x1 < 2 ^ t) (hx2 : x2 < 2 ^ t) (hx3 : x3 < 2 ^ t)
  (hx4 : x4 < 2 ^ t) :
  fieldSwapAdj t 0 (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) =
    x2 * 2 ^ (3 * t) + x1 * 2 ^ (2 * t) + x3 * 2 ^ t + x4 := by
  have hb2 : 2 ^ t * 2 ^ t = 2 ^ (2 * t) := by
    rw [← pow_add (2 : ℕ) t t]
    congr 1
    ring
  have h3t : 2 ^ (3 * t) = 2 ^ t * 2 ^ (2 * t) := by
    rw [← pow_add (2 : ℕ) t (2 * t)]
    congr 1
    ring
  have hz : x3 * 2 ^ t + x4 < 2 ^ (2 * t) := by
    calc
      x3 * 2 ^ t + x4 < x3 * 2 ^ t + 2 ^ t := Nat.add_lt_add_of_le_of_lt (Nat.le_refl (x3 * 2 ^ t)) hx4
      _ = (x3 + 1) * 2 ^ t := by ring
      _ ≤ 2 ^ t * 2 ^ t := Nat.mul_le_mul (Nat.succ_le_of_lt hx3) (Nat.le_refl (2 ^ t))
      _ = 2 ^ (2 * t) := hb2
  have hsp : x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4 =
      (x1 * 2 ^ t + x2) * 2 ^ (2 * t) + (x3 * 2 ^ t + x4) := by
    rw [h3t]
    ring
  have H1 : (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) % 2 ^ (2 * t) =
      x3 * 2 ^ t + x4 := by
    rw [hsp, Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt hz, Nat.zero_add]
    exact Nat.mod_eq_of_lt hz
  have H2 : (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) / 2 ^ (2 * t) =
      x1 * 2 ^ t + x2 := by
    rw [hsp]
    exact Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith [hz])
  have H3 : (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) / 2 ^ (2 * t) / 2 ^ t =
      x1 := by
    rw [H2]
    exact Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith [hx2])
  have H2m : (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) / 2 ^ (2 * t) % 2 ^ t =
      x2 := by
    rw [H2, Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt hx2, Nat.zero_add]
    exact Nat.mod_eq_of_lt hx2
  have H3m : (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) / 2 ^ (2 * t) / 2 ^ t % 2 ^ t =
      x1 := by
    rw [H3]
    exact Nat.mod_eq_of_lt hx1
  have H4 : (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) / 2 ^ (2 * t) / 2 ^ t / 2 ^ t =
      0 := by
    rw [H3]
    exact Nat.div_eq_of_lt hx1
  have hpow : 2 ^ t * 2 ^ (2 * t) = 2 ^ (3 * t) := by
    rw [← pow_add (2 : ℕ) t (2 * t)]
    congr 1
    ring
  simp only [fieldSwapAdj, interchangeIndex]
  norm_num
  rw [show t * 2 = 2 * t by ring]
  simp only [H1, H2m, Nat.mod_one, H3m, H4, Nat.div_one, bitAddr, mul_zero, zero_mul, zero_add, add_zero, mul_one, one_mul]
  rw [add_mul, mul_assoc, hpow]
  ring
end P2MHole04_0db9687e

/-- The field interchange of positions `1,2` (`i = 0`, `G = 1`, suffix `2^{2t}`): it swaps `x1,x2`,
leaving `x3,x4` untouched. -/
lemma fieldSwap0 (t : ℕ) (x1 x2 x3 x4 : ℕ) (hx1 : x1 < 2 ^ t) (hx2 : x2 < 2 ^ t)
    (hx3 : x3 < 2 ^ t) (hx4 : x4 < 2 ^ t) :
    fieldSwapAdj t 0 (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) =
      x2 * 2 ^ (3 * t) + x1 * 2 ^ (2 * t) + x3 * 2 ^ t + x4 := by
  (first | exact P2MHole04_0db9687e.solution t x1 x2 x3 x4 hx1 hx2 hx3 hx4 | (apply P2MHole04_0db9687e.solution <;> assumption))

namespace P2MHole05_a1bfbeed
theorem solution (t x1 x2 x3 x4 : ℕ) (hx1 : x1 < 2 ^ t) (hx2 : x2 < 2 ^ t) (hx3 : x3 < 2 ^ t)
  (hx4 : x4 < 2 ^ t) :
  (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) % 2 ^ t = x4 ∧
    (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) / 2 ^ t = x1 * 2 ^ (2 * t) + x2 * 2 ^ t + x3 := by
  set b : ℕ := 2 ^ t
  -- 2^(3t) = b^3 and 2^(2t) = b^2, so the index is a polynomial in b = 2^t
  have hb3 : 2 ^ (3 * t) = b ^ 3 := by
    rw [mul_comm, pow_mul 2 t 3]
  have hb2 : 2 ^ (2 * t) = b ^ 2 := by
    rw [mul_comm, pow_mul 2 t 2]
  rw [hb3, hb2]
  -- the index X = C * b + x4 with C = x1*b^2 + x2*b + x3
  set C : ℕ := x1 * b ^ 2 + x2 * b + x3
  have hXb : x1 * b ^ 3 + x2 * b ^ 2 + x3 * b + x4 = C * b + x4 := by
    ring
  have hx4lt : x4 < b := hx4
  constructor
  · -- low field: (C*b + x4) % b = x4, since C*b ≡ 0 (mod b) and x4 < b
    rw [hXb]
    have hmod : C * b % b = 0 := by
      rw [mul_comm]
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right b C)
    simpa [Nat.add_mod, hmod, Nat.mod_eq_of_lt hx4lt]
  · -- high fields: (C*b + x4) / b = C, since C*b ≤ C*b + x4 < (C+1)*b
    rw [hXb]
    have hle : C * b ≤ C * b + x4 :=
      Nat.le_add_right (C * b) x4
    have hlt : C * b + x4 < (C + 1) * b := by
      have h : C * b + x4 < C * b + b :=
        Nat.add_lt_add_left hx4lt (C * b)
      rw [show C * b + b = (C + 1) * b by ring] at h
      exact h
    exact Nat.div_eq_of_lt_le hle hlt
end P2MHole05_a1bfbeed

/-- In the four-field form with each field `< 2^t`, the remainder and quotient by `2^t` pick out the
lowest field `x4` and the high part. -/
lemma fieldFormModDiv (t : ℕ) (x1 x2 x3 x4 : ℕ) (hx1 : x1 < 2 ^ t) (hx2 : x2 < 2 ^ t)
    (hx3 : x3 < 2 ^ t) (hx4 : x4 < 2 ^ t) :
    (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) % 2 ^ t = x4 ∧
      (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) / 2 ^ t =
        x1 * 2 ^ (2 * t) + x2 * 2 ^ t + x3 := by
  (first | exact P2MHole05_a1bfbeed.solution t x1 x2 x3 x4 hx1 hx2 hx3 hx4 | (apply P2MHole05_a1bfbeed.solution <;> assumption))

namespace P2MHole06_c0e89f7f
theorem solution (t x1 x2 x3 x4 : ℕ) (hx1 : x1 < 2 ^ t) (hx2 : x2 < 2 ^ t) (hx3 : x3 < 2 ^ t)
  (hx4 : x4 < 2 ^ t) :
  (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) % 2 ^ (3 * t) = x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4 ∧
    (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) / 2 ^ (3 * t) = x1 := by
  let b := 2 ^ (3 * t)
  have hb : 0 < b := by
    dsimp [b]; exact pow_pos (Nat.zero_lt_two) (3 * t)
  let q := x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4
  -- Sub-claim 1: x3 * 2^t + x4 < 2^(2t)
  have h_sub1 : x3 * 2 ^ t + x4 < 2 ^ (2 * t) := by
    have h_pos : 1 ≤ 2 ^ t - x3 := by
      have h : 0 < 2 ^ t - x3 := Nat.sub_pos_of_lt hx3
      omega
    have h_bound : 2 ^ t ≤ (2 ^ t - x3) * 2 ^ t := by
      simpa [Nat.one_mul] using Nat.mul_le_mul_right (2 ^ t) h_pos
    have h_ineq : (2 ^ t - x3) * 2 ^ t > x4 := lt_of_lt_of_le hx4 h_bound
    have h_dist : x3 * 2 ^ t + (2 ^ t - x3) * 2 ^ t = 2 ^ t * 2 ^ t := by
      rw [← Nat.add_mul]
      have h_le : x3 ≤ 2 ^ t := Nat.le_of_lt hx3
      rw [Nat.add_sub_cancel' h_le]
    have h_2t : 2 ^ t * 2 ^ t = 2 ^ (2 * t) := by
      have h : t + t = 2 * t := by ring
      rw [← Nat.pow_add 2 t t, h]
    have h_add : x3 * 2 ^ t + x4 < x3 * 2 ^ t + (2 ^ t - x3) * 2 ^ t :=
      Nat.add_lt_add_left h_ineq (x3 * 2 ^ t)
    have h_rhs : x3 * 2 ^ t + (2 ^ t - x3) * 2 ^ t = 2 ^ (2 * t) := by
      rw [h_dist, h_2t]
    exact lt_of_lt_of_le h_add (le_of_eq h_rhs)
  -- Sub-claim 2: x2 * 2^(2t) + (x3 * 2^t + x4) < 2^(3t)
  have h_sub2 : x2 * 2 ^ (2 * t) + (x3 * 2 ^ t + x4) < 2 ^ (3 * t) := by
    have h_pos : 1 ≤ 2 ^ t - x2 := by
      have h : 0 < 2 ^ t - x2 := Nat.sub_pos_of_lt hx2
      omega
    have h_bound : 2 ^ (2 * t) ≤ (2 ^ t - x2) * 2 ^ (2 * t) := by
      simpa [Nat.one_mul] using Nat.mul_le_mul_right (2 ^ (2 * t)) h_pos
    have h_ineq : (2 ^ t - x2) * 2 ^ (2 * t) > x3 * 2 ^ t + x4 := lt_of_lt_of_le h_sub1 h_bound
    have h_dist : x2 * 2 ^ (2 * t) + (2 ^ t - x2) * 2 ^ (2 * t) = 2 ^ t * 2 ^ (2 * t) := by
      rw [← Nat.add_mul]
      have h_le : x2 ≤ 2 ^ t := Nat.le_of_lt hx2
      rw [Nat.add_sub_cancel' h_le]
    have h_3t : 2 ^ t * 2 ^ (2 * t) = 2 ^ (3 * t) := by
      have h : t + 2 * t = 3 * t := by ring
      rw [← Nat.pow_add 2 t (2 * t), h]
    have h_add : x2 * 2 ^ (2 * t) + (x3 * 2 ^ t + x4) < x2 * 2 ^ (2 * t) + (2 ^ t - x2) * 2 ^ (2 * t) :=
      Nat.add_lt_add_left h_ineq (x2 * 2 ^ (2 * t))
    have h_rhs : x2 * 2 ^ (2 * t) + (2 ^ t - x2) * 2 ^ (2 * t) = 2 ^ (3 * t) := by
      rw [h_dist, h_3t]
    exact lt_of_lt_of_le h_add (le_of_eq h_rhs)
  have hq : q < b := by
    dsimp [q, b]
    have h : x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4 = x2 * 2 ^ (2 * t) + (x3 * 2 ^ t + x4) := by
      ring
    rw [h]
    exact h_sub2
  -- Mod: (x1*b + q) % b = q
  have h_mod : (x1 * b + q) % b = q := by
    have h1 : (x1 * b) % b = 0 := by
      rw [Nat.mul_mod, Nat.mod_self]
      simp
    rw [Nat.add_mod, h1]
    simp [Nat.mod_eq_of_lt hq]
  -- Div: (x1*b + q) / b = x1
  have h_div : (x1 * b + q) / b = x1 := by
    have h_dm := Nat.div_add_mod (x1 * b + q) b
    have h_eq : (x1 * b + q) / b * b = x1 * b := by
      nlinarith [h_dm, h_mod]
    have h_eq2 : b * ((x1 * b + q) / b) = b * x1 := by
      nlinarith [h_eq]
    exact Nat.eq_of_mul_eq_mul_left hb h_eq2
  -- Final step: connect b, q to the original expression
  have h_sum : x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4 = x1 * b + q := by
    dsimp [b, q]
    ring_nf
  constructor
  · rw [h_sum]
    exact h_mod
  · rw [h_sum]
    exact h_div
end P2MHole06_c0e89f7f

/-- In the four-field form with each field `< 2^t`, the remainder and quotient by `2^{3t}` pick out
the lowest three fields and the top field. -/
lemma fieldFormModDiv3 (t : ℕ) (x1 x2 x3 x4 : ℕ) (hx1 : x1 < 2 ^ t) (hx2 : x2 < 2 ^ t)
    (hx3 : x3 < 2 ^ t) (hx4 : x4 < 2 ^ t) :
    (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) % 2 ^ (3 * t) =
      x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4 ∧
      (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) / 2 ^ (3 * t) = x1 := by
  (first | exact P2MHole06_c0e89f7f.solution t x1 x2 x3 x4 hx1 hx2 hx3 hx4 | (apply P2MHole06_c0e89f7f.solution <;> assumption))

/-- **Proposition 7.1 (The Columnsort reduction), the rearrangements as interchanges**, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), p.28.

With `s = 2^t`, `r = s³ = 2^{3t}`, `t ≥ 3`, split a record index `j ∈ [2^{4t}]` into four `t`-bit fields
`(x₁, x₂, x₃, x₄)` from highest to lowest. The transpose of step 2, `π(j) = (j mod 2^t)·2^{3t} +
⌊j/2^t⌋`, equals the three adjacent address-field interchanges of width `t` at positions `3, 4`, then
`2, 3`, then `1, 2`; the inverse `π⁻¹` of step 4 equals the same three interchanges in reverse
order.

**Formalization Note.** `fieldSwapAdj t i` exchanges the fields at positions `i + 1`, `i + 2`
(`i : Fin 3`), as the §6.1 interchange `interchangeIndex` with `G = 1`. `transposeIdx` and
`transposeInvIdx` are the maps used by `columnsortLifted`. -/
theorem solution (t : ℕ) (ht : 3 ≤ t) (j : ℕ) (hj : j < 2 ^ (4 * t)) :
    transposeIdx (2 ^ t) ((2 ^ t) ^ 3) j =
        fieldSwapAdj t 0 (fieldSwapAdj t 1 (fieldSwapAdj t 2 j)) ∧
      transposeInvIdx (2 ^ t) ((2 ^ t) ^ 3) j =
        fieldSwapAdj t 2 (fieldSwapAdj t 1 (fieldSwapAdj t 0 j)) := by
  obtain ⟨x1, x2, x3, x4, hx1, hx2, hx3, hx4, hjf⟩ := fieldDecompose t j hj
  -- First composition: interchange 3,4 then 2,3 then 1,2.
  have hA : fieldSwapAdj t 2 j = x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x4 * 2 ^ t + x3 := by
    rw [hjf]
    exact fieldSwap2 t x1 x2 x3 x4 hx1 hx2 hx3 hx4
  have hB : fieldSwapAdj t 1 (fieldSwapAdj t 2 j) =
        x1 * 2 ^ (3 * t) + x4 * 2 ^ (2 * t) + x2 * 2 ^ t + x3 := by
    rw [hA]
    exact fieldSwap1 t x1 x2 x4 x3 hx1 hx2 hx4 hx3
  have hC : fieldSwapAdj t 0 (fieldSwapAdj t 1 (fieldSwapAdj t 2 j)) =
        x4 * 2 ^ (3 * t) + x1 * 2 ^ (2 * t) + x2 * 2 ^ t + x3 := by
    rw [hB]
    exact fieldSwap0 t x1 x4 x2 x3 hx1 hx4 hx2 hx3
  -- Second composition: interchange 1,2 then 2,3 then 3,4.
  have hA' : fieldSwapAdj t 0 j = x2 * 2 ^ (3 * t) + x1 * 2 ^ (2 * t) + x3 * 2 ^ t + x4 := by
    rw [hjf]
    exact fieldSwap0 t x1 x2 x3 x4 hx1 hx2 hx3 hx4
  have hB' : fieldSwapAdj t 1 (fieldSwapAdj t 0 j) =
        x2 * 2 ^ (3 * t) + x3 * 2 ^ (2 * t) + x1 * 2 ^ t + x4 := by
    rw [hA']
    exact fieldSwap1 t x2 x1 x3 x4 hx2 hx1 hx3 hx4
  have hC' : fieldSwapAdj t 2 (fieldSwapAdj t 1 (fieldSwapAdj t 0 j)) =
        x2 * 2 ^ (3 * t) + x3 * 2 ^ (2 * t) + x4 * 2 ^ t + x1 := by
    rw [hB']
    exact fieldSwap2 t x2 x3 x1 x4 hx2 hx3 hx1 hx4
  -- Division/remainder of the field form by 2^t and by 2^(3t).
  have hd1 : (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) % 2 ^ t = x4 ∧
          (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) / 2 ^ t =
            x1 * 2 ^ (2 * t) + x2 * 2 ^ t + x3 := fieldFormModDiv t x1 x2 x3 x4 hx1 hx2 hx3 hx4
  have hd3 : (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) % 2 ^ (3 * t) =
          x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4 ∧
          (x1 * 2 ^ (3 * t) + x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4) / 2 ^ (3 * t) = x1 :=
    fieldFormModDiv3 t x1 x2 x3 x4 hx1 hx2 hx3 hx4
  have hc3 : (2 ^ t) ^ 3 = 2 ^ (3 * t) := by rw [← pow_mul, mul_comm]
  constructor
  · -- π(j) = (j mod 2^t)·2^(3t) + ⌊j/2^t⌋ = x4·2^(3t) + x1·2^(2t) + x2·2^t + x3 = the three swaps.
    rw [hC]
    unfold transposeIdx
    rw [hc3]
    have r1 : j % 2 ^ t = x4 := by rw [hjf]; exact hd1.1
    have r2 : j / 2 ^ t = x1 * 2 ^ (2 * t) + x2 * 2 ^ t + x3 := by rw [hjf]; exact hd1.2
    rw [r1, r2]
    ring
  · -- π⁻¹(j) = 2^t·(j mod 2^(3t)) + ⌊j/2^(3t)⌋ = x2·2^(3t) + x3·2^(2t) + x4·2^t + x1.
    rw [hC']
    unfold transposeInvIdx
    rw [hc3]
    have r1 : j % 2 ^ (3 * t) = x2 * 2 ^ (2 * t) + x3 * 2 ^ t + x4 := by rw [hjf]; exact hd3.1
    have r2 : j / 2 ^ (3 * t) = x1 := by rw [hjf]; exact hd3.2
    rw [r1, r2]
    -- Expand the powers of 2^(2t) and 2^(3t) in products of 2^t so both sides share one atom.
    rw [show 2 ^ (3 * t) = 2 ^ t * 2 ^ (2 * t) by rw [show 3 * t = t + 2 * t by ring, Nat.pow_add],
        show 2 ^ (2 * t) = 2 ^ t * 2 ^ t by rw [show 2 * t = t + t by ring, Nat.pow_add]]
    ring
