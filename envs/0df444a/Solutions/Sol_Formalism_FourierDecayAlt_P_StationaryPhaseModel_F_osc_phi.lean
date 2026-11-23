-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_osc_phi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:45.873689+00:00
-- url     : https://prove2.me/submissions/fa8f1489-6814-4027-a0e4-976434402270

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_bump_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_psi_eq

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
variable {d : ℕ} {r Λ : ℝ} {g : (Fin d → ℂ) → ℂ} {dg : (Fin d → ℂ) → Fin d → ℂ} {H : Matrix (Fin d) (Fin d) ℂ}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (hr : 0 < r) (β : ℂ) {t : ℂ} (ht : t ≠ 0) {x : Fin d → ℂ}
    (hx : x ∈ Metric.closedBall (0 : Fin d → ℂ) r) :
    osc (F_phi d r (F_c β t) g) ‖t‖ x = psi β (g x / t) := by
  rw [F_psi_eq β ht]
  unfold osc F_phi
  rw [F_bump_one hr (Metric.closedBall_subset_closedBall (by linarith) hx), one_mul]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
