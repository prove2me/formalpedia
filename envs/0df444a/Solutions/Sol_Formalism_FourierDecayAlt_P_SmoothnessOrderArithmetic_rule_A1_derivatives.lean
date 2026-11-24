-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.rule_A1_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:54:39.148875+00:00
-- url     : https://prove2.me/submissions/50ec50e0-cffb-4304-994f-13937c7d4a4f

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_rpow_mono_G
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_loss_bound_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_ckOn_top_of_all

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
theorem _root_.solution : C2.FiniteOrderIntersectionInSmooth := by
  intro k r E _ _ A F hF
  refine ⟨ckOn_top_of_all fun m => (hF m).choose_spec.1, ?_⟩
  intro u v hu hv
  obtain ⟨c, hc⟩ := hF (u.length + v.length)
  refine ⟨c, fun g hg => le_trans ?_ (hc.2 u v hu hv le_rfl g hg)⟩
  refine mul_le_mul_of_nonneg_right (rpow_mono_G hg ?_) (norm_nonneg _)
  have : 0 ≤ C2.B0 r * ((u.length : ℝ) + v.length) := mul_nonneg (loss_bound_nonneg r) (by positivity)
  linarith
end Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
