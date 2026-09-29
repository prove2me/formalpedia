-- Prove2me | solution 1 for BookProof.SirkGapTable.richardson_exact
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:15:59.964605+00:00
-- url     : https://prove2.me/submissions/3284aeb1-729e-4b62-bf93-306533e3f4d5

import Definitions.Def_ChapterSirkGapTable
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkGapTable.lean
open BookProof.SirkGapTable Real
set_option autoImplicit false
private theorem ritzX_one_lt_ratio {l1 l2 p : ℝ} (hl1 : 0 < l1) (hl : l1 < l2) (hp : 0 < p) :
    1 < (l2 / l1) ^ p := by
  have h1 : 1 < l2 / l1 := (one_lt_div hl1).2 hl
  exact (one_lt_rpow_iff (by linarith)).2 (Or.inl ⟨h1, hp⟩)

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

#print axioms solution
