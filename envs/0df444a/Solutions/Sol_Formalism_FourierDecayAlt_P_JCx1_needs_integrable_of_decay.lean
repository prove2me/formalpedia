-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.needs.integrable_of_decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:49:50.881505+00:00
-- url     : https://prove2.me/submissions/40974228-9b9c-415e-b5d1-4e1551fdf1f3

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt Filter Topology MeasureTheory NumberField
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.needs
noncomputable section
namespace Formalism.FourierDecayAlt.P.JCx1.needs
theorem _root_.solution {φ : ℂ → ℂ} (hc : Continuous φ) {Cφ : ℝ}
    (hb : ∀ c, ‖φ c‖ ≤ Cφ * ((1 + ‖c‖) ^ 3)⁻¹) : Integrable φ := by
  have hg : Integrable (fun c : ℂ => (1 + ‖c‖) ^ (-(3 : ℝ))) := by
    apply integrable_one_add_norm
    rw [Complex.finrank_real_complex]
    norm_num
  refine (hg.const_mul Cφ).mono' hc.aestronglyMeasurable (ae_of_all _ fun c => ?_)
  have h1 : (0 : ℝ) ≤ 1 + ‖c‖ := by positivity
  rw [Real.rpow_neg h1, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact hb c
end Formalism.FourierDecayAlt.P.JCx1.needs
