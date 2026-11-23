-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.holo_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:56.338212+00:00
-- url     : https://prove2.me/submissions/728756d0-0845-4958-860c-855b8cd21594

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_C_differentiableOn_fderiv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Metric
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : DifferentiableOn ℂ f U) (n : ℕ) : ContDiffOn ℂ n f U := by
  induction n generalizing f with
  | zero => exact contDiffOn_zero.2 hf.continuousOn
  | succ n ih =>
    have h := (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℂ) (n := (n : WithTop ℕ∞)) (f := f) hU).2
      ⟨hf, fun h => absurd h (by simp), contDiffOn_clm_apply.2 fun v =>
        ih (C_differentiableOn_fderiv_apply hU hf v)⟩
    exact_mod_cast h
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
