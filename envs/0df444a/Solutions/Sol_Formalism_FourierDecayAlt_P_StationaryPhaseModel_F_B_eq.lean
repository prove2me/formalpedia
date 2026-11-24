-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_B_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:31.415802+00:00
-- url     : https://prove2.me/submissions/5099cddb-ca3a-4ab6-a890-3ed483622e34

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_clm_sum
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
    (hH : ∀ i j, HasDerivAt (fun ξ => dg (Function.update 0 j ξ) i) (H i j) 0) (u v : Fin d → ℂ) :
    fderiv ℂ (fderiv ℂ g) 0 u v = v ⬝ᵥ (H *ᵥ u) := by
  rw [F_clm_sum (fderiv ℂ (fderiv ℂ g) 0 u) v]
  simp only [dotProduct, mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [F_symm hr hg, F_clm_sum (fderiv ℂ (fderiv ℂ g) 0 (Pi.single i 1)) u]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [F_symm hr hg, F_H_eq hr hg hdg hH, mul_comm]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
