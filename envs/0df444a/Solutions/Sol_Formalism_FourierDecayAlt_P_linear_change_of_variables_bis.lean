-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.linear_change_of_variables_bis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:44:05.990057+00:00
-- url     : https://prove2.me/submissions/e01cd297-5442-4996-80ad-f40541c9fc42

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x5 C2x6 C2x7
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.LinCOV := by
  intro a φ ha
  have hpos : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha
  set f : ℂ →ₗ[ℝ] ℂ := (LinearMap.mulLeft ℂ a).restrictScalars ℝ with hf
  have hdet : LinearMap.det f = Complex.normSq a := by
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_mulLeft, Algebra.norm_complex_apply]
  have hne : LinearMap.det f ≠ 0 := by rw [hdet]; exact hpos.ne'
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure ℂ)) hne
  have hcoe : (⇑f : ℂ → ℂ) = ⇑(MeasurableEquiv.mulLeft₀ a ha) := by ext c; rfl
  calc ∫⁻ c : ℂ, φ (a * c) = ∫⁻ c : ℂ, φ (MeasurableEquiv.mulLeft₀ a ha c) := rfl
    _ = ∫⁻ D, φ D ∂(Measure.map (MeasurableEquiv.mulLeft₀ a ha) volume) := (lintegral_map_equiv φ _).symm
    _ = ∫⁻ D, φ D ∂(Measure.map f volume) := by rw [hcoe]
    _ = ENNReal.ofReal ((‖a‖ ^ 2)⁻¹) * ∫⁻ D : ℂ, φ D := by
        rw [hmap, lintegral_smul_measure, hdet, abs_of_pos (inv_pos.mpr hpos), Complex.normSq_eq_norm_sq]
        rfl
end Formalism.FourierDecayAlt.P
