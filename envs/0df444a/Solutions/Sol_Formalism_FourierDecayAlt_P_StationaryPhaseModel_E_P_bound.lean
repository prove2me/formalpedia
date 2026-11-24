-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_P_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:29.192813+00:00
-- url     : https://prove2.me/submissions/7c919676-f67c-42bf-8aac-ba1b64df4dfe

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_quad_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_quad_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_hess_le

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {φ : E → ℝ} {n : ℕ} (h2n : 2 ≤ n) (hφ : ContDiff ℝ n φ) {r Γ : ℝ} (hr : 0 < r)
    (hb : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ) :
    ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ n →
      ‖iteratedFDeriv ℝ i (E_P φ) x‖ ≤ Γ + Γ * (r + 1) ^ 2 := by
  intro x hx i hi
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by exact_mod_cast h2n)
  have h0 : ‖φ 0‖ ≤ Γ := by
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact hb 0 (Metric.mem_closedBall_self hr.le) 0 (Nat.zero_le _)
  have hin : ((i : ℕ) : WithTop ℕ∞) ≤ n := by exact_mod_cast hi
  have he : E_P φ = φ - quad φ := rfl
  rw [he, iteratedFDeriv_sub_apply (hφ.of_le hin).contDiffAt (E_quad_contDiff φ i).contDiffAt]
  exact (norm_sub_le _ _).trans (add_le_add (hb x hx i hi) (E_quad_bound hφ2 hr h0 (E_hess_le h2n hr hb) i hx))
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
