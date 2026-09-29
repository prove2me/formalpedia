-- Prove2me | solution 1 for BrinSquier.isPLFSlopeOne_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T17:52:10.982876+00:00
-- url     : https://prove2.me/submissions/5e059720-9e4b-43cf-8239-546dd3e8a41a

import Theorems.Thm_BrinSquier_isPLF_mul
import Definitions.Def_BrinSquier
import Mathlib

namespace BS_sc
open BrinSquier
theorem slopeAtBot_one_mul {f g : ℝ ≃o ℝ} (hf : SlopeAtBot f 1) (hg : SlopeAtBot g 1) :
    SlopeAtBot (f * g) 1 := by
  obtain ⟨b1, M1, h1⟩ := hf
  obtain ⟨b2, M2, h2⟩ := hg
  refine ⟨b1 + b2, min M2 (M1 - b2), fun y hy => ?_⟩
  have hy2 : y < M2 := lt_of_lt_of_le hy (min_le_left _ _)
  have hy1 : y + b2 < M1 := by have := lt_of_lt_of_le hy (min_le_right _ _); linarith
  show f (g y) = 1 * y + (b1 + b2)
  rw [h2 y hy2]
  have : (1:ℝ) * y + b2 = y + b2 := by ring
  rw [this, h1 (y + b2) hy1]; ring

theorem slopeAtTop_one_mul {f g : ℝ ≃o ℝ} (hf : SlopeAtTop f 1) (hg : SlopeAtTop g 1) :
    SlopeAtTop (f * g) 1 := by
  obtain ⟨b1, M1, h1⟩ := hf
  obtain ⟨b2, M2, h2⟩ := hg
  refine ⟨b1 + b2, max M2 (M1 - b2), fun y hy => ?_⟩
  have hy2 : y > M2 := lt_of_le_of_lt (le_max_left _ _) hy
  have hy1 : y + b2 > M1 := by have := lt_of_le_of_lt (le_max_right _ _) hy; linarith
  show f (g y) = 1 * y + (b1 + b2)
  rw [h2 y hy2]
  have : (1:ℝ) * y + b2 = y + b2 := by ring
  rw [this, h1 (y + b2) hy1]; ring
end BS_sc

open BS_sc BrinSquier in
theorem solution {f g : ℝ ≃o ℝ} (hf : IsPLFSlopeOne f) (hg : IsPLFSlopeOne g) :
    IsPLFSlopeOne (f * g) :=
  ⟨isPLF_mul hf.1 hg.1, slopeAtBot_one_mul hf.2.1 hg.2.1, slopeAtTop_one_mul hf.2.2 hg.2.2⟩
