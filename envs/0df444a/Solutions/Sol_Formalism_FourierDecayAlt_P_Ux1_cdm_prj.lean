-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.cdm_prj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:11:55.778641+00:00
-- url     : https://prove2.me/submissions/cba8068b-52c6-4b07-afeb-f9046df7b116

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cdm_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cdm_conjT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X}
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution {F : X → Mat k r} (hF : ContDiffOn ℝ n F s) : ContDiffOn ℝ n (fun x => prj (F x)) s := by
  unfold prj
  exact (hF.sub (cdm_mul (cdm_mul contDiffOn_const (cdm_conjT hF)) contDiffOn_const)).const_smul _
end Formalism.FourierDecayAlt.P.Ux1
