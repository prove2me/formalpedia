-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_cut_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:40.025774+00:00
-- url     : https://prove2.me/submissions/4a3635ad-b12a-4e3f-9516-fcf969bfdd2d

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_cut_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_cut_compact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
noncomputable section
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (d N : ℕ) {ρ : ℝ} (h : 0 < ρ) : ∃ M : ℝ, ∀ x, ∀ i ≤ N,
    ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ M := by
  have h1 : ∀ i : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ C := fun i =>
    ((D_cut_compact d h).iteratedFDeriv i).exists_bound_of_continuous
      ((D_cut_contDiff d h i).continuous_iteratedFDeriv le_rfl)
  choose c hc using h1
  have hc0 : ∀ i, 0 ≤ c i := fun i => (norm_nonneg _).trans (hc i 0)
  exact ⟨∑ i ∈ Finset.range (N + 1), c i, fun x i hi => (hc i x).trans
    (Finset.single_le_sum (f := c) (fun j _ => hc0 j) (Finset.mem_range.2 (by omega)))⟩
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
