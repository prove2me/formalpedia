-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.map_mul_volume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:36:24.304107+00:00
-- url     : https://prove2.me/submissions/41885c4b-9505-4d7e-b9e1-ed12f0dbe531

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (ρ : ℂ) (hρ : ρ ≠ 0) :
    Measure.map (fun z : ℂ => ρ * z) volume = ENNReal.ofReal ((‖ρ‖ ^ 2)⁻¹) • (volume : Measure ℂ) := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ ρ) = ‖ρ‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl
  have hne : LinearMap.det (LinearMap.mulLeft ℝ ρ) ≠ 0 := by
    rw [hdet]
    positivity
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ) hne
  rw [hdet, abs_of_nonneg (by positivity)] at h
  exact h
end Formalism.FourierDecayAlt.P.PBK
