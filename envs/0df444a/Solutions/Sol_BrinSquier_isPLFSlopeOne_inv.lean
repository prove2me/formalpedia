-- Prove2me | solution 1 for BrinSquier.isPLFSlopeOne_inv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-13T07:04:32.468036+00:00
-- url     : https://prove2.me/submissions/50b5c22c-0030-4608-8023-247bf274fc55

import Theorems.Thm_BrinSquier_isPLF_inv
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

theorem slopeAtBot_one_inv {f : ℝ ≃o ℝ} (hf : SlopeAtBot f 1) : SlopeAtBot f⁻¹ 1 := by
  obtain ⟨b, M, h⟩ := hf
  refine ⟨-b, M + b, fun w hw => ?_⟩
  have hy : w - b < M := by linarith
  have hfy : f (w - b) = w := by rw [h (w - b) hy]; ring
  show f⁻¹ w = 1 * w + -b
  have : f (f⁻¹ w) = f (w - b) := by rw [RelIso.apply_inv_self, hfy]
  have := f.injective this
  rw [this]; ring

theorem slopeAtTop_one_inv {f : ℝ ≃o ℝ} (hf : SlopeAtTop f 1) : SlopeAtTop f⁻¹ 1 := by
  obtain ⟨b, M, h⟩ := hf
  refine ⟨-b, M + b, fun w hw => ?_⟩
  have hy : w - b > M := by linarith
  have hfy : f (w - b) = w := by rw [h (w - b) hy]; ring
  show f⁻¹ w = 1 * w + -b
  have : f (f⁻¹ w) = f (w - b) := by rw [RelIso.apply_inv_self, hfy]
  have := f.injective this
  rw [this]; ring
end BS_sc

open BS_sc BrinSquier in
theorem solution {f : ℝ ≃o ℝ} (hf : IsPLFSlopeOne f) : IsPLFSlopeOne f⁻¹ :=
  ⟨isPLF_inv hf.1, slopeAtBot_one_inv hf.2.1, slopeAtTop_one_inv hf.2.2⟩
