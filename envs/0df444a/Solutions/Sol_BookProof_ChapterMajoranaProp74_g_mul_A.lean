-- Prove2me | solution 1 for BookProof.ChapterMajoranaProp74.g_mul_A
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:20:04.1434+00:00
-- url     : https://prove2.me/submissions/357a766e-e98b-4233-9813-7beaba3fdf11

import Mathlib
open Matrix

theorem solution {g ns : Matrix (Fin 4) (Fin 4) ℂ} (hg2 : g * g = 1)
    (hgns : g * ns = -(ns * g)) : g * (ns * g) = -ns := by
  calc
    g * (ns * g) = (g * ns) * g := by rw [mul_assoc]
    _ = (-(ns * g)) * g := by rw [hgns]
    _ = -(ns * g * g) := by rw [neg_mul]
    _ = -(ns * (g * g)) := by rw [mul_assoc]
    _ = -(ns * 1) := by rw [hg2]
    _ = -ns := by simp
