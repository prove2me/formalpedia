-- Prove2me | solution 1 for Eden.derivativeFactors_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:18:05.401993+00:00
-- url     : https://prove2.me/submissions/95ec8953-6ae4-403e-a7a6-fafc3e0288bb

import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_DerivativeDecomposition
import Theorems.Thm_Eden_planarAmplitude_pos
import Theorems.Thm_Eden_radialAmplitude_pos


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) (i : Fin 5) :
    0 < derivativeFactors c t p i := by
  have h₁ : 0 ≤ radiusSq₁ p := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have h₂ : 0 ≤ radiusSq₂ p := add_nonneg (sq_nonneg _) (sq_nonneg _)
  fin_cases i
  · exact radialAmplitude_pos ht h₁
  · exact planarAmplitude_pos ht h₁
  · exact radialAmplitude_pos ht h₂
  · exact planarAmplitude_pos ht h₂
  · exact Real.exp_pos _
end Eden
