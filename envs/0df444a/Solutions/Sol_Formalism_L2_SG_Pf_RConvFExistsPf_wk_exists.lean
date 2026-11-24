-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RConvFExistsPf.wk_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:18:33.703793+00:00
-- url     : https://prove2.me/submissions/cc8b0ebc-f440-4ebe-b91f-f8376d1651c5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RConvFExistsPfAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RConvFExistsPf
open MeasureTheory
open scoped InnerProductSpace
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
namespace Formalism.L2.SG.Pf.RConvFExistsPf
theorem _root_.solution {U : α → (E →L[ℂ] E)} (hU : ∀ g z, ‖U g z‖ ≤ ‖z‖)
    (hm : ∀ x y : E, AEStronglyMeasurable (fun g => ⟪x, U g y⟫_ℂ) μ) {f : α → ℂ} (hf : Integrable f μ) :
    ∃ T : E →L[ℂ] E, ∀ x y : E, ⟪x, T y⟫_ℂ = ∫ g, f g * ⟪x, U g y⟫_ℂ ∂μ := by
  refine ⟨ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin (wkForm hU hm hf)),
    fun x y => ?_⟩
  rw [ContinuousLinearMap.adjoint_inner_right, InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl
end Formalism.L2.SG.Pf.RConvFExistsPf
