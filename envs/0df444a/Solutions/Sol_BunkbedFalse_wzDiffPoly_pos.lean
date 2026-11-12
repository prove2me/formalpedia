-- Prove2me | solution 1 for BunkbedFalse.wzDiffPoly_pos
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T00:15:19.575074+00:00
-- url     : https://prove2.me/submissions/0fea1c4d-49e5-4084-be23-f8b6040bcc21

import Definitions.Def_BunkbedWZPoly

open Bunkbed Bunkbed.Hyper

/-! Lower bounds for the graded cofactors on the unit cube. Each monomial in `x`, `y`, `u`
lies in `[0,1]`, so a cofactor is at least minus the sum of the absolute values of its
coefficients. -/

private lemma R1_lb {x y u : ℚ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y)
    (hy1 : y ≤ 1) (hu : 0 ≤ u) (hu1 : u ≤ 1) : -(14:ℚ) ≤ wzR1 x y u := by
  have N0 : (0:ℚ) ≤ u := by positivity
  have P0 : u ≤ 1 := hu1
  have N1 : (0:ℚ) ≤ x := by positivity
  have P1 : x ≤ 1 := hx1
  have N2 : (0:ℚ) ≤ y := by positivity
  have P2 : y ≤ 1 := hy1
  simp only [wzR1]
  linarith [N0, P0, N1, P1, N2, P2]

private lemma R2_lb {x y u : ℚ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y)
    (hy1 : y ≤ 1) (hu : 0 ≤ u) (hu1 : u ≤ 1) : -(101:ℚ) ≤ wzR2 x y u := by
  have N0 : (0:ℚ) ≤ u ^ 2 := by positivity
  have P0 : u ^ 2 ≤ 1 := (pow_le_one₀ hu hu1)
  have N1 : (0:ℚ) ≤ x * u := by positivity
  have P1 : x * u ≤ 1 := (mul_le_one₀ hx1 hu hu1)
  have N2 : (0:ℚ) ≤ x * y := by positivity
  have P2 : x * y ≤ 1 := (mul_le_one₀ hx1 hy hy1)
  have N3 : (0:ℚ) ≤ x ^ 2 := by positivity
  have P3 : x ^ 2 ≤ 1 := (pow_le_one₀ hx hx1)
  have N4 : (0:ℚ) ≤ y * u := by positivity
  have P4 : y * u ≤ 1 := (mul_le_one₀ hy1 hu hu1)
  have N5 : (0:ℚ) ≤ y ^ 2 := by positivity
  have P5 : y ^ 2 ≤ 1 := (pow_le_one₀ hy hy1)
  simp only [wzR2]
  linarith [N0, P0, N1, P1, N2, P2, N3, P3, N4, P4, N5, P5]

private lemma R3_lb {x y u : ℚ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y)
    (hy1 : y ≤ 1) (hu : 0 ≤ u) (hu1 : u ≤ 1) : -(692:ℚ) ≤ wzR3 x y u := by
  have N0 : (0:ℚ) ≤ u ^ 3 := by positivity
  have P0 : u ^ 3 ≤ 1 := (pow_le_one₀ hu hu1)
  have N1 : (0:ℚ) ≤ x * u ^ 2 := by positivity
  have P1 : x * u ^ 2 ≤ 1 := (mul_le_one₀ hx1 (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N2 : (0:ℚ) ≤ x * y * u := by positivity
  have P2 : x * y * u ≤ 1 := (mul_le_one₀ (mul_le_one₀ hx1 hy hy1) hu hu1)
  have N3 : (0:ℚ) ≤ x * y ^ 2 := by positivity
  have P3 : x * y ^ 2 ≤ 1 := (mul_le_one₀ hx1 (pow_nonneg hy 2) (pow_le_one₀ hy hy1))
  have N4 : (0:ℚ) ≤ x ^ 2 * u := by positivity
  have P4 : x ^ 2 * u ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) hu hu1)
  have N5 : (0:ℚ) ≤ x ^ 2 * y := by positivity
  have P5 : x ^ 2 * y ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) hy hy1)
  have N6 : (0:ℚ) ≤ x ^ 3 := by positivity
  have P6 : x ^ 3 ≤ 1 := (pow_le_one₀ hx hx1)
  have N7 : (0:ℚ) ≤ y * u ^ 2 := by positivity
  have P7 : y * u ^ 2 ≤ 1 := (mul_le_one₀ hy1 (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N8 : (0:ℚ) ≤ y ^ 2 * u := by positivity
  have P8 : y ^ 2 * u ≤ 1 := (mul_le_one₀ (pow_le_one₀ hy hy1) hu hu1)
  have N9 : (0:ℚ) ≤ y ^ 3 := by positivity
  have P9 : y ^ 3 ≤ 1 := (pow_le_one₀ hy hy1)
  simp only [wzR3]
  linarith [N0, P0, N1, P1, N2, P2, N3, P3, N4, P4, N5, P5, N6, P6, N7, P7, N8, P8, N9, P9]

private lemma R4_lb {x y u : ℚ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y)
    (hy1 : y ≤ 1) (hu : 0 ≤ u) (hu1 : u ≤ 1) : -(4305:ℚ) ≤ wzR4 x y u := by
  have N0 : (0:ℚ) ≤ u ^ 4 := by positivity
  have P0 : u ^ 4 ≤ 1 := (pow_le_one₀ hu hu1)
  have N1 : (0:ℚ) ≤ x * u ^ 3 := by positivity
  have P1 : x * u ^ 3 ≤ 1 := (mul_le_one₀ hx1 (pow_nonneg hu 3) (pow_le_one₀ hu hu1))
  have N2 : (0:ℚ) ≤ x * y * u ^ 2 := by positivity
  have P2 : x * y * u ^ 2 ≤ 1 := (mul_le_one₀ (mul_le_one₀ hx1 hy hy1) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N3 : (0:ℚ) ≤ x * y ^ 2 * u := by positivity
  have P3 : x * y ^ 2 * u ≤ 1 := (mul_le_one₀ (mul_le_one₀ hx1 (pow_nonneg hy 2) (pow_le_one₀ hy hy1)) hu hu1)
  have N4 : (0:ℚ) ≤ x * y ^ 3 := by positivity
  have P4 : x * y ^ 3 ≤ 1 := (mul_le_one₀ hx1 (pow_nonneg hy 3) (pow_le_one₀ hy hy1))
  have N5 : (0:ℚ) ≤ x ^ 2 * u ^ 2 := by positivity
  have P5 : x ^ 2 * u ^ 2 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N6 : (0:ℚ) ≤ x ^ 2 * y * u := by positivity
  have P6 : x ^ 2 * y * u ≤ 1 := (mul_le_one₀ (mul_le_one₀ (pow_le_one₀ hx hx1) hy hy1) hu hu1)
  have N7 : (0:ℚ) ≤ x ^ 2 * y ^ 2 := by positivity
  have P7 : x ^ 2 * y ^ 2 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hy 2) (pow_le_one₀ hy hy1))
  have N8 : (0:ℚ) ≤ x ^ 3 * u := by positivity
  have P8 : x ^ 3 * u ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) hu hu1)
  have N9 : (0:ℚ) ≤ x ^ 3 * y := by positivity
  have P9 : x ^ 3 * y ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) hy hy1)
  have N10 : (0:ℚ) ≤ x ^ 4 := by positivity
  have P10 : x ^ 4 ≤ 1 := (pow_le_one₀ hx hx1)
  have N11 : (0:ℚ) ≤ y * u ^ 3 := by positivity
  have P11 : y * u ^ 3 ≤ 1 := (mul_le_one₀ hy1 (pow_nonneg hu 3) (pow_le_one₀ hu hu1))
  have N12 : (0:ℚ) ≤ y ^ 2 * u ^ 2 := by positivity
  have P12 : y ^ 2 * u ^ 2 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hy hy1) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N13 : (0:ℚ) ≤ y ^ 3 * u := by positivity
  have P13 : y ^ 3 * u ≤ 1 := (mul_le_one₀ (pow_le_one₀ hy hy1) hu hu1)
  have N14 : (0:ℚ) ≤ y ^ 4 := by positivity
  have P14 : y ^ 4 ≤ 1 := (pow_le_one₀ hy hy1)
  simp only [wzR4]
  linarith [N0, P0, N1, P1, N2, P2, N3, P3, N4, P4, N5, P5, N6, P6, N7, P7, N8, P8, N9, P9, N10, P10, N11, P11, N12, P12, N13, P13, N14, P14]

private lemma R5_lb {x y u : ℚ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y)
    (hy1 : y ≤ 1) (hu : 0 ≤ u) (hu1 : u ≤ 1) : -(13024:ℚ) ≤ wzR5 x y u := by
  have N0 : (0:ℚ) ≤ u ^ 5 := by positivity
  have P0 : u ^ 5 ≤ 1 := (pow_le_one₀ hu hu1)
  have N1 : (0:ℚ) ≤ x * u ^ 4 := by positivity
  have P1 : x * u ^ 4 ≤ 1 := (mul_le_one₀ hx1 (pow_nonneg hu 4) (pow_le_one₀ hu hu1))
  have N2 : (0:ℚ) ≤ x * y * u ^ 3 := by positivity
  have P2 : x * y * u ^ 3 ≤ 1 := (mul_le_one₀ (mul_le_one₀ hx1 hy hy1) (pow_nonneg hu 3) (pow_le_one₀ hu hu1))
  have N3 : (0:ℚ) ≤ x * y ^ 2 * u ^ 2 := by positivity
  have P3 : x * y ^ 2 * u ^ 2 ≤ 1 := (mul_le_one₀ (mul_le_one₀ hx1 (pow_nonneg hy 2) (pow_le_one₀ hy hy1)) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N4 : (0:ℚ) ≤ x * y ^ 3 * u := by positivity
  have P4 : x * y ^ 3 * u ≤ 1 := (mul_le_one₀ (mul_le_one₀ hx1 (pow_nonneg hy 3) (pow_le_one₀ hy hy1)) hu hu1)
  have N5 : (0:ℚ) ≤ x * y ^ 4 := by positivity
  have P5 : x * y ^ 4 ≤ 1 := (mul_le_one₀ hx1 (pow_nonneg hy 4) (pow_le_one₀ hy hy1))
  have N6 : (0:ℚ) ≤ x ^ 2 * u ^ 3 := by positivity
  have P6 : x ^ 2 * u ^ 3 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hu 3) (pow_le_one₀ hu hu1))
  have N7 : (0:ℚ) ≤ x ^ 2 * y * u ^ 2 := by positivity
  have P7 : x ^ 2 * y * u ^ 2 ≤ 1 := (mul_le_one₀ (mul_le_one₀ (pow_le_one₀ hx hx1) hy hy1) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N8 : (0:ℚ) ≤ x ^ 2 * y ^ 2 * u := by positivity
  have P8 : x ^ 2 * y ^ 2 * u ≤ 1 := (mul_le_one₀ (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hy 2) (pow_le_one₀ hy hy1)) hu hu1)
  have N9 : (0:ℚ) ≤ x ^ 2 * y ^ 3 := by positivity
  have P9 : x ^ 2 * y ^ 3 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hy 3) (pow_le_one₀ hy hy1))
  have N10 : (0:ℚ) ≤ x ^ 3 * u ^ 2 := by positivity
  have P10 : x ^ 3 * u ^ 2 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N11 : (0:ℚ) ≤ x ^ 3 * y * u := by positivity
  have P11 : x ^ 3 * y * u ≤ 1 := (mul_le_one₀ (mul_le_one₀ (pow_le_one₀ hx hx1) hy hy1) hu hu1)
  have N12 : (0:ℚ) ≤ x ^ 3 * y ^ 2 := by positivity
  have P12 : x ^ 3 * y ^ 2 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hy 2) (pow_le_one₀ hy hy1))
  have N13 : (0:ℚ) ≤ x ^ 4 * u := by positivity
  have P13 : x ^ 4 * u ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) hu hu1)
  have N14 : (0:ℚ) ≤ x ^ 4 * y := by positivity
  have P14 : x ^ 4 * y ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) hy hy1)
  have N15 : (0:ℚ) ≤ x ^ 5 := by positivity
  have P15 : x ^ 5 ≤ 1 := (pow_le_one₀ hx hx1)
  have N16 : (0:ℚ) ≤ y * u ^ 4 := by positivity
  have P16 : y * u ^ 4 ≤ 1 := (mul_le_one₀ hy1 (pow_nonneg hu 4) (pow_le_one₀ hu hu1))
  have N17 : (0:ℚ) ≤ y ^ 2 * u ^ 3 := by positivity
  have P17 : y ^ 2 * u ^ 3 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hy hy1) (pow_nonneg hu 3) (pow_le_one₀ hu hu1))
  have N18 : (0:ℚ) ≤ y ^ 3 * u ^ 2 := by positivity
  have P18 : y ^ 3 * u ^ 2 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hy hy1) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N19 : (0:ℚ) ≤ y ^ 4 * u := by positivity
  have P19 : y ^ 4 * u ≤ 1 := (mul_le_one₀ (pow_le_one₀ hy hy1) hu hu1)
  have N20 : (0:ℚ) ≤ y ^ 5 := by positivity
  have P20 : y ^ 5 ≤ 1 := (pow_le_one₀ hy hy1)
  simp only [wzR5]
  linarith [N0, P0, N1, P1, N2, P2, N3, P3, N4, P4, N5, P5, N6, P6, N7, P7, N8, P8, N9, P9, N10, P10, N11, P11, N12, P12, N13, P13, N14, P14, N15, P15, N16, P16, N17, P17, N18, P18, N19, P19, N20, P20]

private lemma R6_lb {x y u : ℚ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y)
    (hy1 : y ≤ 1) (hu : 0 ≤ u) (hu1 : u ≤ 1) : -(21119:ℚ) ≤ wzR6 x y u := by
  have N0 : (0:ℚ) ≤ u ^ 6 := by positivity
  have P0 : u ^ 6 ≤ 1 := (pow_le_one₀ hu hu1)
  have N1 : (0:ℚ) ≤ x * u ^ 5 := by positivity
  have P1 : x * u ^ 5 ≤ 1 := (mul_le_one₀ hx1 (pow_nonneg hu 5) (pow_le_one₀ hu hu1))
  have N2 : (0:ℚ) ≤ x * y * u ^ 4 := by positivity
  have P2 : x * y * u ^ 4 ≤ 1 := (mul_le_one₀ (mul_le_one₀ hx1 hy hy1) (pow_nonneg hu 4) (pow_le_one₀ hu hu1))
  have N3 : (0:ℚ) ≤ x * y ^ 2 * u ^ 3 := by positivity
  have P3 : x * y ^ 2 * u ^ 3 ≤ 1 := (mul_le_one₀ (mul_le_one₀ hx1 (pow_nonneg hy 2) (pow_le_one₀ hy hy1)) (pow_nonneg hu 3) (pow_le_one₀ hu hu1))
  have N4 : (0:ℚ) ≤ x * y ^ 3 * u ^ 2 := by positivity
  have P4 : x * y ^ 3 * u ^ 2 ≤ 1 := (mul_le_one₀ (mul_le_one₀ hx1 (pow_nonneg hy 3) (pow_le_one₀ hy hy1)) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N5 : (0:ℚ) ≤ x * y ^ 4 * u := by positivity
  have P5 : x * y ^ 4 * u ≤ 1 := (mul_le_one₀ (mul_le_one₀ hx1 (pow_nonneg hy 4) (pow_le_one₀ hy hy1)) hu hu1)
  have N6 : (0:ℚ) ≤ x * y ^ 5 := by positivity
  have P6 : x * y ^ 5 ≤ 1 := (mul_le_one₀ hx1 (pow_nonneg hy 5) (pow_le_one₀ hy hy1))
  have N7 : (0:ℚ) ≤ x ^ 2 * u ^ 4 := by positivity
  have P7 : x ^ 2 * u ^ 4 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hu 4) (pow_le_one₀ hu hu1))
  have N8 : (0:ℚ) ≤ x ^ 2 * y * u ^ 3 := by positivity
  have P8 : x ^ 2 * y * u ^ 3 ≤ 1 := (mul_le_one₀ (mul_le_one₀ (pow_le_one₀ hx hx1) hy hy1) (pow_nonneg hu 3) (pow_le_one₀ hu hu1))
  have N9 : (0:ℚ) ≤ x ^ 2 * y ^ 2 * u ^ 2 := by positivity
  have P9 : x ^ 2 * y ^ 2 * u ^ 2 ≤ 1 := (mul_le_one₀ (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hy 2) (pow_le_one₀ hy hy1)) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N10 : (0:ℚ) ≤ x ^ 2 * y ^ 3 * u := by positivity
  have P10 : x ^ 2 * y ^ 3 * u ≤ 1 := (mul_le_one₀ (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hy 3) (pow_le_one₀ hy hy1)) hu hu1)
  have N11 : (0:ℚ) ≤ x ^ 2 * y ^ 4 := by positivity
  have P11 : x ^ 2 * y ^ 4 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hy 4) (pow_le_one₀ hy hy1))
  have N12 : (0:ℚ) ≤ x ^ 3 * u ^ 3 := by positivity
  have P12 : x ^ 3 * u ^ 3 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hu 3) (pow_le_one₀ hu hu1))
  have N13 : (0:ℚ) ≤ x ^ 3 * y * u ^ 2 := by positivity
  have P13 : x ^ 3 * y * u ^ 2 ≤ 1 := (mul_le_one₀ (mul_le_one₀ (pow_le_one₀ hx hx1) hy hy1) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N14 : (0:ℚ) ≤ x ^ 3 * y ^ 2 * u := by positivity
  have P14 : x ^ 3 * y ^ 2 * u ≤ 1 := (mul_le_one₀ (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hy 2) (pow_le_one₀ hy hy1)) hu hu1)
  have N15 : (0:ℚ) ≤ x ^ 3 * y ^ 3 := by positivity
  have P15 : x ^ 3 * y ^ 3 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hy 3) (pow_le_one₀ hy hy1))
  have N16 : (0:ℚ) ≤ x ^ 4 * u ^ 2 := by positivity
  have P16 : x ^ 4 * u ^ 2 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N17 : (0:ℚ) ≤ x ^ 4 * y * u := by positivity
  have P17 : x ^ 4 * y * u ≤ 1 := (mul_le_one₀ (mul_le_one₀ (pow_le_one₀ hx hx1) hy hy1) hu hu1)
  have N18 : (0:ℚ) ≤ x ^ 4 * y ^ 2 := by positivity
  have P18 : x ^ 4 * y ^ 2 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hy 2) (pow_le_one₀ hy hy1))
  have N19 : (0:ℚ) ≤ x ^ 5 * u := by positivity
  have P19 : x ^ 5 * u ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) hu hu1)
  have N20 : (0:ℚ) ≤ x ^ 5 * y := by positivity
  have P20 : x ^ 5 * y ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) hy hy1)
  have N21 : (0:ℚ) ≤ x ^ 6 := by positivity
  have P21 : x ^ 6 ≤ 1 := (pow_le_one₀ hx hx1)
  have N22 : (0:ℚ) ≤ y * u ^ 5 := by positivity
  have P22 : y * u ^ 5 ≤ 1 := (mul_le_one₀ hy1 (pow_nonneg hu 5) (pow_le_one₀ hu hu1))
  have N23 : (0:ℚ) ≤ y ^ 2 * u ^ 4 := by positivity
  have P23 : y ^ 2 * u ^ 4 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hy hy1) (pow_nonneg hu 4) (pow_le_one₀ hu hu1))
  have N24 : (0:ℚ) ≤ y ^ 3 * u ^ 3 := by positivity
  have P24 : y ^ 3 * u ^ 3 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hy hy1) (pow_nonneg hu 3) (pow_le_one₀ hu hu1))
  have N25 : (0:ℚ) ≤ y ^ 4 * u ^ 2 := by positivity
  have P25 : y ^ 4 * u ^ 2 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hy hy1) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N26 : (0:ℚ) ≤ y ^ 5 * u := by positivity
  have P26 : y ^ 5 * u ≤ 1 := (mul_le_one₀ (pow_le_one₀ hy hy1) hu hu1)
  have N27 : (0:ℚ) ≤ y ^ 6 := by positivity
  have P27 : y ^ 6 ≤ 1 := (pow_le_one₀ hy hy1)
  simp only [wzR6]
  linarith [N0, P0, N1, P1, N2, P2, N3, P3, N4, P4, N5, P5, N6, P6, N7, P7, N8, P8, N9, P9, N10, P10, N11, P11, N12, P12, N13, P13, N14, P14, N15, P15, N16, P16, N17, P17, N18, P18, N19, P19, N20, P20, N21, P21, N22, P22, N23, P23, N24, P24, N25, P25, N26, P26, N27, P27]

private lemma R7_lb {x y u : ℚ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y)
    (hy1 : y ≤ 1) (hu : 0 ≤ u) (hu1 : u ≤ 1) : -(16544:ℚ) ≤ wzR7 x y u := by
  have N0 : (0:ℚ) ≤ u ^ 5 := by positivity
  have P0 : u ^ 5 ≤ 1 := (pow_le_one₀ hu hu1)
  have N1 : (0:ℚ) ≤ x * u ^ 4 := by positivity
  have P1 : x * u ^ 4 ≤ 1 := (mul_le_one₀ hx1 (pow_nonneg hu 4) (pow_le_one₀ hu hu1))
  have N2 : (0:ℚ) ≤ x * y * u ^ 3 := by positivity
  have P2 : x * y * u ^ 3 ≤ 1 := (mul_le_one₀ (mul_le_one₀ hx1 hy hy1) (pow_nonneg hu 3) (pow_le_one₀ hu hu1))
  have N3 : (0:ℚ) ≤ x * y ^ 2 * u ^ 2 := by positivity
  have P3 : x * y ^ 2 * u ^ 2 ≤ 1 := (mul_le_one₀ (mul_le_one₀ hx1 (pow_nonneg hy 2) (pow_le_one₀ hy hy1)) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N4 : (0:ℚ) ≤ x * y ^ 3 * u := by positivity
  have P4 : x * y ^ 3 * u ≤ 1 := (mul_le_one₀ (mul_le_one₀ hx1 (pow_nonneg hy 3) (pow_le_one₀ hy hy1)) hu hu1)
  have N5 : (0:ℚ) ≤ x * y ^ 4 := by positivity
  have P5 : x * y ^ 4 ≤ 1 := (mul_le_one₀ hx1 (pow_nonneg hy 4) (pow_le_one₀ hy hy1))
  have N6 : (0:ℚ) ≤ x ^ 2 * u ^ 3 := by positivity
  have P6 : x ^ 2 * u ^ 3 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hu 3) (pow_le_one₀ hu hu1))
  have N7 : (0:ℚ) ≤ x ^ 2 * y * u ^ 2 := by positivity
  have P7 : x ^ 2 * y * u ^ 2 ≤ 1 := (mul_le_one₀ (mul_le_one₀ (pow_le_one₀ hx hx1) hy hy1) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N8 : (0:ℚ) ≤ x ^ 2 * y ^ 2 * u := by positivity
  have P8 : x ^ 2 * y ^ 2 * u ≤ 1 := (mul_le_one₀ (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hy 2) (pow_le_one₀ hy hy1)) hu hu1)
  have N9 : (0:ℚ) ≤ x ^ 2 * y ^ 3 := by positivity
  have P9 : x ^ 2 * y ^ 3 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hy 3) (pow_le_one₀ hy hy1))
  have N10 : (0:ℚ) ≤ x ^ 3 * u ^ 2 := by positivity
  have P10 : x ^ 3 * u ^ 2 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N11 : (0:ℚ) ≤ x ^ 3 * y * u := by positivity
  have P11 : x ^ 3 * y * u ≤ 1 := (mul_le_one₀ (mul_le_one₀ (pow_le_one₀ hx hx1) hy hy1) hu hu1)
  have N12 : (0:ℚ) ≤ x ^ 3 * y ^ 2 := by positivity
  have P12 : x ^ 3 * y ^ 2 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hy 2) (pow_le_one₀ hy hy1))
  have N13 : (0:ℚ) ≤ x ^ 4 * u := by positivity
  have P13 : x ^ 4 * u ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) hu hu1)
  have N14 : (0:ℚ) ≤ x ^ 4 * y := by positivity
  have P14 : x ^ 4 * y ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) hy hy1)
  have N15 : (0:ℚ) ≤ x ^ 5 := by positivity
  have P15 : x ^ 5 ≤ 1 := (pow_le_one₀ hx hx1)
  have N16 : (0:ℚ) ≤ y * u ^ 4 := by positivity
  have P16 : y * u ^ 4 ≤ 1 := (mul_le_one₀ hy1 (pow_nonneg hu 4) (pow_le_one₀ hu hu1))
  have N17 : (0:ℚ) ≤ y ^ 2 * u ^ 3 := by positivity
  have P17 : y ^ 2 * u ^ 3 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hy hy1) (pow_nonneg hu 3) (pow_le_one₀ hu hu1))
  have N18 : (0:ℚ) ≤ y ^ 3 * u ^ 2 := by positivity
  have P18 : y ^ 3 * u ^ 2 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hy hy1) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N19 : (0:ℚ) ≤ y ^ 4 * u := by positivity
  have P19 : y ^ 4 * u ≤ 1 := (mul_le_one₀ (pow_le_one₀ hy hy1) hu hu1)
  have N20 : (0:ℚ) ≤ y ^ 5 := by positivity
  have P20 : y ^ 5 ≤ 1 := (pow_le_one₀ hy hy1)
  simp only [wzR7]
  linarith [N0, P0, N1, P1, N2, P2, N3, P3, N4, P4, N5, P5, N6, P6, N7, P7, N8, P8, N9, P9, N10, P10, N11, P11, N12, P12, N13, P13, N14, P14, N15, P15, N16, P16, N17, P17, N18, P18, N19, P19, N20, P20]

private lemma R8_lb {x y u : ℚ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y)
    (hy1 : y ≤ 1) (hu : 0 ≤ u) (hu1 : u ≤ 1) : -(8050:ℚ) ≤ wzR8 x y u := by
  have N0 : (0:ℚ) ≤ u ^ 4 := by positivity
  have P0 : u ^ 4 ≤ 1 := (pow_le_one₀ hu hu1)
  have N1 : (0:ℚ) ≤ x * u ^ 3 := by positivity
  have P1 : x * u ^ 3 ≤ 1 := (mul_le_one₀ hx1 (pow_nonneg hu 3) (pow_le_one₀ hu hu1))
  have N2 : (0:ℚ) ≤ x * y * u ^ 2 := by positivity
  have P2 : x * y * u ^ 2 ≤ 1 := (mul_le_one₀ (mul_le_one₀ hx1 hy hy1) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N3 : (0:ℚ) ≤ x * y ^ 2 * u := by positivity
  have P3 : x * y ^ 2 * u ≤ 1 := (mul_le_one₀ (mul_le_one₀ hx1 (pow_nonneg hy 2) (pow_le_one₀ hy hy1)) hu hu1)
  have N4 : (0:ℚ) ≤ x * y ^ 3 := by positivity
  have P4 : x * y ^ 3 ≤ 1 := (mul_le_one₀ hx1 (pow_nonneg hy 3) (pow_le_one₀ hy hy1))
  have N5 : (0:ℚ) ≤ x ^ 2 * u ^ 2 := by positivity
  have P5 : x ^ 2 * u ^ 2 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N6 : (0:ℚ) ≤ x ^ 2 * y * u := by positivity
  have P6 : x ^ 2 * y * u ≤ 1 := (mul_le_one₀ (mul_le_one₀ (pow_le_one₀ hx hx1) hy hy1) hu hu1)
  have N7 : (0:ℚ) ≤ x ^ 2 * y ^ 2 := by positivity
  have P7 : x ^ 2 * y ^ 2 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) (pow_nonneg hy 2) (pow_le_one₀ hy hy1))
  have N8 : (0:ℚ) ≤ x ^ 3 * u := by positivity
  have P8 : x ^ 3 * u ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) hu hu1)
  have N9 : (0:ℚ) ≤ x ^ 3 * y := by positivity
  have P9 : x ^ 3 * y ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) hy hy1)
  have N10 : (0:ℚ) ≤ x ^ 4 := by positivity
  have P10 : x ^ 4 ≤ 1 := (pow_le_one₀ hx hx1)
  have N11 : (0:ℚ) ≤ y * u ^ 3 := by positivity
  have P11 : y * u ^ 3 ≤ 1 := (mul_le_one₀ hy1 (pow_nonneg hu 3) (pow_le_one₀ hu hu1))
  have N12 : (0:ℚ) ≤ y ^ 2 * u ^ 2 := by positivity
  have P12 : y ^ 2 * u ^ 2 ≤ 1 := (mul_le_one₀ (pow_le_one₀ hy hy1) (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N13 : (0:ℚ) ≤ y ^ 3 * u := by positivity
  have P13 : y ^ 3 * u ≤ 1 := (mul_le_one₀ (pow_le_one₀ hy hy1) hu hu1)
  have N14 : (0:ℚ) ≤ y ^ 4 := by positivity
  have P14 : y ^ 4 ≤ 1 := (pow_le_one₀ hy hy1)
  simp only [wzR8]
  linarith [N0, P0, N1, P1, N2, P2, N3, P3, N4, P4, N5, P5, N6, P6, N7, P7, N8, P8, N9, P9, N10, P10, N11, P11, N12, P12, N13, P13, N14, P14]

private lemma R9_lb {x y u : ℚ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y)
    (hy1 : y ≤ 1) (hu : 0 ≤ u) (hu1 : u ≤ 1) : -(2272:ℚ) ≤ wzR9 x y u := by
  have N0 : (0:ℚ) ≤ u ^ 3 := by positivity
  have P0 : u ^ 3 ≤ 1 := (pow_le_one₀ hu hu1)
  have N1 : (0:ℚ) ≤ x * u ^ 2 := by positivity
  have P1 : x * u ^ 2 ≤ 1 := (mul_le_one₀ hx1 (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N2 : (0:ℚ) ≤ x * y * u := by positivity
  have P2 : x * y * u ≤ 1 := (mul_le_one₀ (mul_le_one₀ hx1 hy hy1) hu hu1)
  have N3 : (0:ℚ) ≤ x * y ^ 2 := by positivity
  have P3 : x * y ^ 2 ≤ 1 := (mul_le_one₀ hx1 (pow_nonneg hy 2) (pow_le_one₀ hy hy1))
  have N4 : (0:ℚ) ≤ x ^ 2 * u := by positivity
  have P4 : x ^ 2 * u ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) hu hu1)
  have N5 : (0:ℚ) ≤ x ^ 2 * y := by positivity
  have P5 : x ^ 2 * y ≤ 1 := (mul_le_one₀ (pow_le_one₀ hx hx1) hy hy1)
  have N6 : (0:ℚ) ≤ x ^ 3 := by positivity
  have P6 : x ^ 3 ≤ 1 := (pow_le_one₀ hx hx1)
  have N7 : (0:ℚ) ≤ y * u ^ 2 := by positivity
  have P7 : y * u ^ 2 ≤ 1 := (mul_le_one₀ hy1 (pow_nonneg hu 2) (pow_le_one₀ hu hu1))
  have N8 : (0:ℚ) ≤ y ^ 2 * u := by positivity
  have P8 : y ^ 2 * u ≤ 1 := (mul_le_one₀ (pow_le_one₀ hy hy1) hu hu1)
  have N9 : (0:ℚ) ≤ y ^ 3 := by positivity
  have P9 : y ^ 3 ≤ 1 := (pow_le_one₀ hy hy1)
  simp only [wzR9]
  linarith [N0, P0, N1, P1, N2, P2, N3, P3, N4, P4, N5, P5, N6, P6, N7, P7, N8, P8, N9, P9]

private lemma R10_lb {x y u : ℚ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y)
    (hy1 : y ≤ 1) (hu : 0 ≤ u) (hu1 : u ≤ 1) : -(360:ℚ) ≤ wzR10 x y u := by
  have N0 : (0:ℚ) ≤ u ^ 2 := by positivity
  have P0 : u ^ 2 ≤ 1 := (pow_le_one₀ hu hu1)
  have N1 : (0:ℚ) ≤ x * u := by positivity
  have P1 : x * u ≤ 1 := (mul_le_one₀ hx1 hu hu1)
  have N2 : (0:ℚ) ≤ x * y := by positivity
  have P2 : x * y ≤ 1 := (mul_le_one₀ hx1 hy hy1)
  have N3 : (0:ℚ) ≤ x ^ 2 := by positivity
  have P3 : x ^ 2 ≤ 1 := (pow_le_one₀ hx hx1)
  have N4 : (0:ℚ) ≤ y * u := by positivity
  have P4 : y * u ≤ 1 := (mul_le_one₀ hy1 hu hu1)
  have N5 : (0:ℚ) ≤ y ^ 2 := by positivity
  have P5 : y ^ 2 ≤ 1 := (pow_le_one₀ hy hy1)
  simp only [wzR10]
  linarith [N0, P0, N1, P1, N2, P2, N3, P3, N4, P4, N5, P5]

private lemma R11_lb {x y u : ℚ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y)
    (hy1 : y ≤ 1) (hu : 0 ≤ u) (hu1 : u ≤ 1) : -(30:ℚ) ≤ wzR11 x y u := by
  have N0 : (0:ℚ) ≤ u := by positivity
  have P0 : u ≤ 1 := hu1
  have N1 : (0:ℚ) ≤ x := by positivity
  have P1 : x ≤ 1 := hx1
  have N2 : (0:ℚ) ≤ y := by positivity
  have P2 : y ≤ 1 := hy1
  simp only [wzR11]
  linarith [N0, P0, N1, P1, N2, P2]

private lemma R12_lb (x y u : ℚ) : -(1:ℚ) ≤ wzR12 x y u := by
  simp only [wzR12]; norm_num

set_option maxHeartbeats 1000000 in
/-- **Positivity of the Wierman-Ziff difference polynomial** (arithmetic half of Lemma 3.3). -/
theorem solution (x y z u : ℚ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hu : 0 ≤ u)
    (hsum : x + y + z + 2 * u = 1)
    (hpos : 0 < x * y - u * u)
    (h400 : 400 * z ≤ x * y - u * u) :
    0 < wzDiffPoly x y z u := by
  have hx1 : x ≤ 1 := by linarith
  have hy1 : y ≤ 1 := by linarith
  have hu1 : u ≤ 1 := by linarith
  have hWd : wzDet x y u = x * y - u * u := rfl
  have hW : (0:ℚ) < wzDet x y u := by rw [hWd]; exact hpos
  have hW1 : wzDet x y u ≤ 1 := by rw [hWd]; nlinarith
  have ht0 : (0:ℚ) ≤ 400 * z := by linarith
  have ht : 400 * z ≤ wzDet x y u := by rw [hWd]; exact h400
  have hW6 : (0:ℚ) < wzDet x y u ^ 6 := pow_pos hW 6
  have hA1 : (0:ℚ) ≤ (400 * z) ^ 1 * wzDet x y u ^ 5 := mul_nonneg (pow_nonneg ht0 1) (pow_nonneg hW.le 5)
  have hB1 : (400 * z) ^ 1 * wzDet x y u ^ 5 ≤ wzDet x y u ^ 6 := by
    calc (400 * z) ^ 1 * wzDet x y u ^ 5 ≤ wzDet x y u ^ 1 * wzDet x y u ^ 5 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0 ht 1) (pow_nonneg hW.le 5)
      _ ≤ wzDet x y u ^ 6 := le_of_eq (by ring)
  have hT1 : -((14:ℚ)) * wzDet x y u ^ 6 ≤ (400 * z) ^ 1 * wzDet x y u ^ 5 * wzR1 x y u := by
    have hC : (400 * z) ^ 1 * wzDet x y u ^ 5 * (-(14:ℚ)) ≤ (400 * z) ^ 1 * wzDet x y u ^ 5 * wzR1 x y u :=
      mul_le_mul_of_nonneg_left (R1_lb hx hx1 hy hy1 hu hu1) hA1
    linarith [hB1, hC]
  have hA2 : (0:ℚ) ≤ (400 * z) ^ 2 * wzDet x y u ^ 4 := mul_nonneg (pow_nonneg ht0 2) (pow_nonneg hW.le 4)
  have hB2 : (400 * z) ^ 2 * wzDet x y u ^ 4 ≤ wzDet x y u ^ 6 := by
    calc (400 * z) ^ 2 * wzDet x y u ^ 4 ≤ wzDet x y u ^ 2 * wzDet x y u ^ 4 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0 ht 2) (pow_nonneg hW.le 4)
      _ ≤ wzDet x y u ^ 6 := le_of_eq (by ring)
  have hT2 : -((101:ℚ)) * wzDet x y u ^ 6 ≤ (400 * z) ^ 2 * wzDet x y u ^ 4 * wzR2 x y u := by
    have hC : (400 * z) ^ 2 * wzDet x y u ^ 4 * (-(101:ℚ)) ≤ (400 * z) ^ 2 * wzDet x y u ^ 4 * wzR2 x y u :=
      mul_le_mul_of_nonneg_left (R2_lb hx hx1 hy hy1 hu hu1) hA2
    linarith [hB2, hC]
  have hA3 : (0:ℚ) ≤ (400 * z) ^ 3 * wzDet x y u ^ 3 := mul_nonneg (pow_nonneg ht0 3) (pow_nonneg hW.le 3)
  have hB3 : (400 * z) ^ 3 * wzDet x y u ^ 3 ≤ wzDet x y u ^ 6 := by
    calc (400 * z) ^ 3 * wzDet x y u ^ 3 ≤ wzDet x y u ^ 3 * wzDet x y u ^ 3 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0 ht 3) (pow_nonneg hW.le 3)
      _ ≤ wzDet x y u ^ 6 := le_of_eq (by ring)
  have hT3 : -((692:ℚ)) * wzDet x y u ^ 6 ≤ (400 * z) ^ 3 * wzDet x y u ^ 3 * wzR3 x y u := by
    have hC : (400 * z) ^ 3 * wzDet x y u ^ 3 * (-(692:ℚ)) ≤ (400 * z) ^ 3 * wzDet x y u ^ 3 * wzR3 x y u :=
      mul_le_mul_of_nonneg_left (R3_lb hx hx1 hy hy1 hu hu1) hA3
    linarith [hB3, hC]
  have hA4 : (0:ℚ) ≤ (400 * z) ^ 4 * wzDet x y u ^ 2 := mul_nonneg (pow_nonneg ht0 4) (pow_nonneg hW.le 2)
  have hB4 : (400 * z) ^ 4 * wzDet x y u ^ 2 ≤ wzDet x y u ^ 6 := by
    calc (400 * z) ^ 4 * wzDet x y u ^ 2 ≤ wzDet x y u ^ 4 * wzDet x y u ^ 2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0 ht 4) (pow_nonneg hW.le 2)
      _ ≤ wzDet x y u ^ 6 := le_of_eq (by ring)
  have hT4 : -((4305:ℚ)) * wzDet x y u ^ 6 ≤ (400 * z) ^ 4 * wzDet x y u ^ 2 * wzR4 x y u := by
    have hC : (400 * z) ^ 4 * wzDet x y u ^ 2 * (-(4305:ℚ)) ≤ (400 * z) ^ 4 * wzDet x y u ^ 2 * wzR4 x y u :=
      mul_le_mul_of_nonneg_left (R4_lb hx hx1 hy hy1 hu hu1) hA4
    linarith [hB4, hC]
  have hA5 : (0:ℚ) ≤ (400 * z) ^ 5 * wzDet x y u ^ 1 := mul_nonneg (pow_nonneg ht0 5) (pow_nonneg hW.le 1)
  have hB5 : (400 * z) ^ 5 * wzDet x y u ^ 1 ≤ wzDet x y u ^ 6 := by
    calc (400 * z) ^ 5 * wzDet x y u ^ 1 ≤ wzDet x y u ^ 5 * wzDet x y u ^ 1 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0 ht 5) (pow_nonneg hW.le 1)
      _ ≤ wzDet x y u ^ 6 := le_of_eq (by ring)
  have hT5 : -((13024:ℚ)) * wzDet x y u ^ 6 ≤ (400 * z) ^ 5 * wzDet x y u ^ 1 * wzR5 x y u := by
    have hC : (400 * z) ^ 5 * wzDet x y u ^ 1 * (-(13024:ℚ)) ≤ (400 * z) ^ 5 * wzDet x y u ^ 1 * wzR5 x y u :=
      mul_le_mul_of_nonneg_left (R5_lb hx hx1 hy hy1 hu hu1) hA5
    linarith [hB5, hC]
  have hA6 : (0:ℚ) ≤ (400 * z) ^ 6 * wzDet x y u ^ 0 := mul_nonneg (pow_nonneg ht0 6) (pow_nonneg hW.le 0)
  have hB6 : (400 * z) ^ 6 * wzDet x y u ^ 0 ≤ wzDet x y u ^ 6 := by
    calc (400 * z) ^ 6 * wzDet x y u ^ 0 ≤ wzDet x y u ^ 6 * wzDet x y u ^ 0 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0 ht 6) (pow_nonneg hW.le 0)
      _ ≤ wzDet x y u ^ 6 := le_of_eq (by ring)
  have hT6 : -((21119:ℚ)) * wzDet x y u ^ 6 ≤ (400 * z) ^ 6 * wzDet x y u ^ 0 * wzR6 x y u := by
    have hC : (400 * z) ^ 6 * wzDet x y u ^ 0 * (-(21119:ℚ)) ≤ (400 * z) ^ 6 * wzDet x y u ^ 0 * wzR6 x y u :=
      mul_le_mul_of_nonneg_left (R6_lb hx hx1 hy hy1 hu hu1) hA6
    linarith [hB6, hC]
  have hA7 : (0:ℚ) ≤ (400 * z) ^ 7 := pow_nonneg ht0 7
  have hB7 : (400 * z) ^ 7 ≤ wzDet x y u ^ 6 := by
    calc (400 * z) ^ 7 ≤ wzDet x y u ^ 7 := pow_le_pow_left₀ ht0 ht 7
      _ ≤ wzDet x y u ^ 6 := pow_le_pow_of_le_one hW.le hW1 (by norm_num)
  have hT7 : -((16544:ℚ)) * wzDet x y u ^ 6 ≤ (400 * z) ^ 7 * wzR7 x y u := by
    have hC : (400 * z) ^ 7 * (-(16544:ℚ)) ≤ (400 * z) ^ 7 * wzR7 x y u :=
      mul_le_mul_of_nonneg_left (R7_lb hx hx1 hy hy1 hu hu1) hA7
    linarith [hB7, hC]
  have hA8 : (0:ℚ) ≤ (400 * z) ^ 8 := pow_nonneg ht0 8
  have hB8 : (400 * z) ^ 8 ≤ wzDet x y u ^ 6 := by
    calc (400 * z) ^ 8 ≤ wzDet x y u ^ 8 := pow_le_pow_left₀ ht0 ht 8
      _ ≤ wzDet x y u ^ 6 := pow_le_pow_of_le_one hW.le hW1 (by norm_num)
  have hT8 : -((8050:ℚ)) * wzDet x y u ^ 6 ≤ (400 * z) ^ 8 * wzR8 x y u := by
    have hC : (400 * z) ^ 8 * (-(8050:ℚ)) ≤ (400 * z) ^ 8 * wzR8 x y u :=
      mul_le_mul_of_nonneg_left (R8_lb hx hx1 hy hy1 hu hu1) hA8
    linarith [hB8, hC]
  have hA9 : (0:ℚ) ≤ (400 * z) ^ 9 := pow_nonneg ht0 9
  have hB9 : (400 * z) ^ 9 ≤ wzDet x y u ^ 6 := by
    calc (400 * z) ^ 9 ≤ wzDet x y u ^ 9 := pow_le_pow_left₀ ht0 ht 9
      _ ≤ wzDet x y u ^ 6 := pow_le_pow_of_le_one hW.le hW1 (by norm_num)
  have hT9 : -((2272:ℚ)) * wzDet x y u ^ 6 ≤ (400 * z) ^ 9 * wzR9 x y u := by
    have hC : (400 * z) ^ 9 * (-(2272:ℚ)) ≤ (400 * z) ^ 9 * wzR9 x y u :=
      mul_le_mul_of_nonneg_left (R9_lb hx hx1 hy hy1 hu hu1) hA9
    linarith [hB9, hC]
  have hA10 : (0:ℚ) ≤ (400 * z) ^ 10 := pow_nonneg ht0 10
  have hB10 : (400 * z) ^ 10 ≤ wzDet x y u ^ 6 := by
    calc (400 * z) ^ 10 ≤ wzDet x y u ^ 10 := pow_le_pow_left₀ ht0 ht 10
      _ ≤ wzDet x y u ^ 6 := pow_le_pow_of_le_one hW.le hW1 (by norm_num)
  have hT10 : -((360:ℚ)) * wzDet x y u ^ 6 ≤ (400 * z) ^ 10 * wzR10 x y u := by
    have hC : (400 * z) ^ 10 * (-(360:ℚ)) ≤ (400 * z) ^ 10 * wzR10 x y u :=
      mul_le_mul_of_nonneg_left (R10_lb hx hx1 hy hy1 hu hu1) hA10
    linarith [hB10, hC]
  have hA11 : (0:ℚ) ≤ (400 * z) ^ 11 := pow_nonneg ht0 11
  have hB11 : (400 * z) ^ 11 ≤ wzDet x y u ^ 6 := by
    calc (400 * z) ^ 11 ≤ wzDet x y u ^ 11 := pow_le_pow_left₀ ht0 ht 11
      _ ≤ wzDet x y u ^ 6 := pow_le_pow_of_le_one hW.le hW1 (by norm_num)
  have hT11 : -((30:ℚ)) * wzDet x y u ^ 6 ≤ (400 * z) ^ 11 * wzR11 x y u := by
    have hC : (400 * z) ^ 11 * (-(30:ℚ)) ≤ (400 * z) ^ 11 * wzR11 x y u :=
      mul_le_mul_of_nonneg_left (R11_lb hx hx1 hy hy1 hu hu1) hA11
    linarith [hB11, hC]
  have hA12 : (0:ℚ) ≤ (400 * z) ^ 12 := pow_nonneg ht0 12
  have hB12 : (400 * z) ^ 12 ≤ wzDet x y u ^ 6 := by
    calc (400 * z) ^ 12 ≤ wzDet x y u ^ 12 := pow_le_pow_left₀ ht0 ht 12
      _ ≤ wzDet x y u ^ 6 := pow_le_pow_of_le_one hW.le hW1 (by norm_num)
  have hT12 : -((1:ℚ)) * wzDet x y u ^ 6 ≤ (400 * z) ^ 12 * wzR12 x y u := by
    have hC : (400 * z) ^ 12 * (-(1:ℚ)) ≤ (400 * z) ^ 12 * wzR12 x y u :=
      mul_le_mul_of_nonneg_left (R12_lb (x := x) (y := y) (u := u)) hA12
    linarith [hB12, hC]
  have key : (400:ℚ) ^ 12 * wzDiffPoly x y z u
      = 400 ^ 12 * wzDet x y u ^ 6
        + 400 ^ 11 * ((400 * z) ^ 1 * wzDet x y u ^ 5 * wzR1 x y u)
        + 400 ^ 10 * ((400 * z) ^ 2 * wzDet x y u ^ 4 * wzR2 x y u)
        + 400 ^ 9 * ((400 * z) ^ 3 * wzDet x y u ^ 3 * wzR3 x y u)
        + 400 ^ 8 * ((400 * z) ^ 4 * wzDet x y u ^ 2 * wzR4 x y u)
        + 400 ^ 7 * ((400 * z) ^ 5 * wzDet x y u ^ 1 * wzR5 x y u)
        + 400 ^ 6 * ((400 * z) ^ 6 * wzDet x y u ^ 0 * wzR6 x y u)
        + 400 ^ 5 * ((400 * z) ^ 7 * wzR7 x y u)
        + 400 ^ 4 * ((400 * z) ^ 8 * wzR8 x y u)
        + 400 ^ 3 * ((400 * z) ^ 9 * wzR9 x y u)
        + 400 ^ 2 * ((400 * z) ^ 10 * wzR10 x y u)
        + 400 ^ 1 * ((400 * z) ^ 11 * wzR11 x y u)
        + 400 ^ 0 * ((400 * z) ^ 12 * wzR12 x y u)
      := by simp only [wzDiffPoly]; ring
  have hfin : (0:ℚ) < 400 ^ 12 * wzDiffPoly x y z u := by
    rw [key]; linarith [hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hT9, hT10, hT11, hT12, hW6]
  linarith

