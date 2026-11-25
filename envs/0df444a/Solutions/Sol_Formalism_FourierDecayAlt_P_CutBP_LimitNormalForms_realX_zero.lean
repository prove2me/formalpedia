-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.realX_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:03:09.238042+00:00
-- url     : https://prove2.me/submissions/b8bd8303-078b-4f16-ac93-2daa3ecf4096

import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_HatProd
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_realF_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_realF_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_actA_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
set_option linter.unusedSectionVars false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
open Formalism.FourierDecayAlt.P.CutMP
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
variable {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)} {L : R.LevelData (MA.A P (MA.DQ P)) P.r} {o κ : ℕ}
namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
theorem _root_.solution : RealX P Bs e L o κ 0 :=
  realF_congr (fun _ _ => Gauge.actA_zero _ _) realF_zero
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
