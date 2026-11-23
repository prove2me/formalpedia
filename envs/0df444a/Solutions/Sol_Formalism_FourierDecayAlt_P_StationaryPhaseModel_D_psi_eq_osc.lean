-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_psi_eq_osc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:24.606151+00:00
-- url     : https://prove2.me/submissions/5e45dbcc-9cd9-42ad-bf4c-a33f0568f52b

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel

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
theorem _root_.solution (d : ℕ) (β t : ℂ) (ht : t ≠ 0) (H : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) :
    psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) = osc (D_phi d (β * (‖t‖ : ℂ) / t) H) ‖t‖ x := by
  have hn : ‖t‖ ≠ 0 := norm_ne_zero_iff.2 ht
  unfold psi osc D_phi
  congr 3
  rw [eq_div_iff hn, mul_comm, ← Complex.re_ofReal_mul]
  congr 1
  field_simp
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
