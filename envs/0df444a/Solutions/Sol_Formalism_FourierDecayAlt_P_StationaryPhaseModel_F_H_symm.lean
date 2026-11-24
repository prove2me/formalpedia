-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_H_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:33.650139+00:00
-- url     : https://prove2.me/submissions/4d99f28f-e8c5-44cb-9ab2-3c3168cca17b

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_H_eq

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
variable {d : ℕ} {r : ℝ} {g : (Fin d → ℂ) → ℂ}
variable {dg : (Fin d → ℂ) → Fin d → ℂ} {H : Matrix (Fin d) (Fin d) ℂ}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r)))
    (hdg : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
      HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k))
    (hH : ∀ i j, HasDerivAt (fun ξ => dg (Function.update 0 j ξ) i) (H i j) 0) : H.IsSymm := by
  ext i j
  rw [Matrix.transpose_apply, ← F_H_eq hr hg hdg hH, ← F_H_eq hr hg hdg hH, F_symm hr hg]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
