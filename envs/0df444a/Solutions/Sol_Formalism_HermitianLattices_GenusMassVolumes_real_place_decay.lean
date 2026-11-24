-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.real_place_decay
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:47.909783+00:00
-- url     : https://prove2.me/submissions/4a3462db-4d99-4740-83a8-ac7cc60454cb

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CardUnitsZmodPrimeSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : SW_real_decay := by
  intro M b
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  have hmax : (0 : ℝ) < max 1 |b| := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hz : 2 * max 1 |b| ≤ ‖2 * Complex.I + 2 * (b : ℂ)‖ := by
    have h1 := Complex.abs_im_le_norm (2 * Complex.I + 2 * (b : ℂ))
    have h2 := Complex.abs_re_le_norm (2 * Complex.I + 2 * (b : ℂ))
    simp at h1 h2
    rcases max_cases 1 |b| with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  rw [norm_div]
  have h2 : ‖(2 * Complex.I : ℂ)‖ = 2 := by simp
  rw [h2, div_le_iff₀ (lt_of_lt_of_le (by positivity) hz)]
  calc (2 : ℝ) = (max 1 |b|)⁻¹ * (2 * max 1 |b|) := by field_simp
    _ ≤ (max 1 |b|)⁻¹ * ‖2 * Complex.I + 2 * (b : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hmax.le)
end Formalism.HermitianLattices.GenusMassVolumes
