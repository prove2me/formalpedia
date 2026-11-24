-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.mt_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:15:40.164794+00:00
-- url     : https://prove2.me/submissions/5d92c417-fa26-4d6a-ac9b-0796661b4280

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GNMulRpow
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InnerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_cornerA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_cornerB
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_ell
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_fromCols
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_fromRows
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_lowW
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_strictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_subS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_supS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_continuous_psi_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_cornerA
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_cornerB
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_ell
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_fromCols
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_fromRows
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_lowW
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_strictUpper
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_subS
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_supS
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_upper
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.continuous_psi_comp



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := by
  first
    | exact continuous_id
    | fun_prop
    | continuity
end Formalism.FourierDecayAlt.P.S3dx4
