-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.bump_cutoff_deriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:18.061425+00:00
-- url     : https://prove2.me/submissions/b328ba96-1fa0-4eef-8ad0-2d589d92f314

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_bump_cutoff_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (d : ℕ) (ρ : ℝ) (h : 0 < ρ) (n : ℕ) : ∃ S : ℝ, ∀ j ≤ n, ∀ x : Fin d → ℂ,
    ‖iteratedFDeriv ℝ j (fun x : Fin d → ℂ => ((cutB d ρ x : ℝ) : ℂ)) x‖ ≤ S := by
  obtain ⟨hc, hcs, -, -⟩ := bump_cutoff_spec d ρ h n
  have key : ∀ j ≤ n, ∃ S : ℝ, ∀ x : Fin d → ℂ,
      ‖iteratedFDeriv ℝ j (fun x : Fin d → ℂ => ((cutB d ρ x : ℝ) : ℂ)) x‖ ≤ S := by
    intro j hj
    exact (hcs.iteratedFDeriv j).exists_bound_of_continuous
      (hc.continuous_iteratedFDeriv (by exact_mod_cast hj))
  choose! S hS using key
  refine ⟨∑ j ∈ Finset.range (n + 1), |S j|, fun j hj x => ?_⟩
  refine ((hS j hj x).trans (le_abs_self _)).trans ?_
  exact Finset.single_le_sum (f := fun j => |S j|) (fun i _ => abs_nonneg _) (Finset.mem_range.2 (by omega))
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
