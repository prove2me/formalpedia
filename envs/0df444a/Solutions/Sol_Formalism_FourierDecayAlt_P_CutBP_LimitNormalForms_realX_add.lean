-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.realX_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:37:43.446342+00:00
-- url     : https://prove2.me/submissions/c3fdc62e-e95a-4afb-b97e-1d3e8053d2d6

import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_HatProd
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_realF_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_realF_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_actA_add


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
theorem _root_.solution {X Y : MA.A P (MA.DQ P)} (hX : RealX P Bs e L o κ X) (hY : RealX P Bs e L o κ Y) :
    RealX P Bs e L o κ (X + Y) :=
  realF_congr (fun _ _ => Gauge.actA_add _ _ _ _) (realF_add hX hY)
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
