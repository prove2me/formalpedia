-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_u_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:39.584905+00:00
-- url     : https://prove2.me/submissions/7c62653e-6c6e-42e4-b582-06900aa9cc9f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_cut_tsupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {d : ℕ} {β : ℂ} {r Γ c₁ ρ τ Cχ S : ℝ} {φ : (Fin d → ℂ) → ℝ}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (hρ0 : 0 < ρ) (hρr : ρ ≤ r) {a : (Fin d → ℂ) → V}
    (hsupp : Function.support a ⊆ Metric.closedBall 0 r) :
    Function.support (E_u d ρ a) ⊆ Metric.closedBall 0 r := by
  intro x hx
  by_contra hxr
  apply hx
  have h1 : a x = 0 := by
    by_contra h
    exact hxr (hsupp h)
  have h2 : cutB d ρ x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    rw [E_cut_tsupport hρ0]
    exact fun h => hxr (Metric.closedBall_subset_closedBall hρr h)
  simp [E_u, modelAmplitude, h1, h2]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
