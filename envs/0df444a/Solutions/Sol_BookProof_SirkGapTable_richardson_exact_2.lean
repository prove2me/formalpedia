-- Prove2me | solution 2 for BookProof.SirkGapTable.richardson_exact
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T20:28:24.248984+00:00
-- url     : https://prove2.me/submissions/ba932bb5-19a7-43ce-a842-7e06e4eec4b4

-- Generated from ChapterSirkGapTable.lean — solution of BookProof.SirkGapTable.richardson_exact
import Mathlib
import Definitions.Def_ChapterSirkGapTable
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkGapTable










noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]














open Real

set_option maxHeartbeats 1000000 in
theorem solution {D C l1 l2 p : ℝ} (hl1 : 0 < l1) (hl : l1 < l2) (hp : 0 < p) :
    richardson (D + C * l1 ^ (-p)) (D + C * l2 ^ (-p)) l1 l2 p = D := by

  have hl2 : 0 < l2 := lt_trans hl1 hl
  set A := l1 ^ p with hA
  set B := l2 ^ p with hB
  have hApos : 0 < A := rpow_pos_of_pos hl1 p
  have hBpos : 0 < B := rpow_pos_of_pos hl2 p
  have hAB : A < B := by
    simpa [hA, hB] using rpow_lt_rpow hl1.le hl hp
  have h1 : l1 ^ (-p) = A⁻¹ := by rw [hA, rpow_neg hl1.le]
  have h2 : l2 ^ (-p) = B⁻¹ := by rw [hB, rpow_neg hl2.le]
  have hratio : (l2 / l1) ^ p = B / A := by
    rw [div_rpow hl2.le hl1.le, hA, hB]
  rw [richardson, h1, h2, hratio]
  have hne : B - A ≠ 0 := by linarith
  field_simp
  ring
