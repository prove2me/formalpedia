-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.dom_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:44:59.16628+00:00
-- url     : https://prove2.me/submissions/7932ae79-97ee-4992-bb25-ba73f0234d85

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cd_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cd_prjMv

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
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution : IsOpen (Dom k r) := by
  have hc : Continuous (fun Y : J k r → ℝ => (1 - prj (Mv Y)).det) := by
    rw [← continuousOn_univ]
    exact (cd_det (contDiffOn_const.sub cd_prjMv)).continuousOn
  have : Dom k r = {Y : J k r → ℝ | (1 - prj (Mv Y)).det ≠ (fun _ => (0 : ℂ)) Y} := by
    ext Y; simp [Dom, isUnit_iff_ne_zero]
  rw [this]
  exact isOpen_ne_fun hc continuous_const
end Formalism.FourierDecayAlt.P.Ux1
