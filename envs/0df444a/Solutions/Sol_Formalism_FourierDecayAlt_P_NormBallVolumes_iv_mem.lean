-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NormBallVolumes.iv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:13:23.656322+00:00
-- url     : https://prove2.me/submissions/3a006678-3360-4a37-a388-4fbf2e1e888f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftingTheory
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormBallVolumes
import Theorems.Thm_Formalism_FourierDecayAlt_P_NormBallVolumes_iv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology Metric
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NormBallVolumes
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.NormBallVolumes
theorem _root_.solution {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : iv g ∈ GV k r := by
  rw [← Matrix.inv_eq_left_inv (iv_mul hg)]
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg
end Formalism.FourierDecayAlt.P.NormBallVolumes
