-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.theta_conj_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:31:05.425743+00:00
-- url     : https://prove2.me/submissions/ea398718-d64d-4413-8269-8fdcd361851b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RadialAdjointOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaConjOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_thr_big
import Theorems.Thm_Formalism_FourierDecayAlt_P_bessel_words_of_domain
import Theorems.Thm_Formalism_FourierDecayAlt_P_rewrite_rho_action
import Theorems.Thm_Formalism_FourierDecayAlt_P_theta_bessel_commute_of_parts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.P.JFxG.JThetaCOfParts := by
  intro hD hc hA k r Wp Wq _ _ _ _ _ _ D Θ F hS hC hF hFc g hg
  have hT : JTheta := Formalism.FourierDecayAlt.P.theta_bessel_commute_of_parts (Formalism.FourierDecayAlt.P.bessel_words_of_domain hD) Formalism.FourierDecayAlt.P.rewrite_rho_action
  obtain ⟨C, hCc, hCO, hCF⟩ := hFc
  refine ⟨?_, hA k r Wp Wq D Θ F hS hC hF ⟨C, hCc, hCO, hCF⟩ g hg⟩
  have hIn := hc k r (Wq →L[ℂ] Wp) F C hF hCc hCF
    (9 * ((r : ℝ) + 1) * ((((2 * r + k + 1 : ℕ) : ℝ)) ^ 2 + 1) + 6 * (r : ℝ) * (opOrder Θ : ℝ)) (opOrder Θ)
  exact (hT k r Wp Wq D _ (opOrder Θ) F Θ le_rfl (JFxG.thr_big k r _) hIn hC g hg).symm
end Formalism.FourierDecayAlt.P
