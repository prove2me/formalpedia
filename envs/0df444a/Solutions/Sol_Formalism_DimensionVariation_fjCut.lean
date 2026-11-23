-- Prove2me | solution 1 for Formalism.DimensionVariation.fjCut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:14.320864+00:00
-- url     : https://prove2.me/submissions/8225fc6b-8859-4aae-805f-48a7895b1e7b

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet
import Theorems.Thm_Formalism_DimensionVariation_measurable_productCutoff
import Theorems.Thm_Formalism_DimensionVariation_norm_productCutoff_le_one
import Theorems.Thm_Formalism_DimensionVariation_productCutoff_eventually_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
open scoped ComplexConjugate Real Nat
noncomputable section
open Formalism Formalism.DimensionVariation
namespace Formalism.DimensionVariation
theorem _root_.solution {κ : Type} [Fintype κ] (G : (κ → ℂ) → ℂ) (hG : Integrable G) :
    Tendsto (fun N : ℕ => ∫ u, fjChiP N u * G u) atTop (𝓝 (∫ u, G u)) := by
  refine tendsto_integral_of_dominated_convergence (fun u => ‖G u‖)
    (fun N => (measurable_productCutoff N).aestronglyMeasurable.mul hG.aestronglyMeasurable)
    hG.norm (fun N => Filter.Eventually.of_forall fun u => ?_)
    (Filter.Eventually.of_forall fun u => ?_)
  · show ‖fjChiP N u * G u‖ ≤ ‖G u‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_productCutoff_le_one N u)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [productCutoff_eventually_eq_one u] with N hN
    rw [hN, one_mul]
end Formalism.DimensionVariation
