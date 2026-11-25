-- Prove2me | solution 1 for Formalism.L2.Col.GFam.Mat.opOf_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:07:00.615063+00:00
-- url     : https://prove2.me/submissions/8f49064e-212f-42c5-842e-cd1dd8575c02

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_ClsKer_opOf_indep
import Theorems.Thm_Formalism_L2_Col_GFam_Mat_opOf_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.GFam
variable (F : GFam K)
namespace Formalism.L2.Col.GFam
namespace Mat
theorem _root_.solution {F F' : GFam K} (M : Mat F F') (h : F.Ok) (s s' : ∀ b, (F.mem b).Sec) :
    M.opOf h s = M.opOf h s' := by
  refine LinearMap.ext fun φ => funext fun b' => ?_
  rw [M.opOf_apply h s, M.opOf_apply h s']
  exact Finset.sum_congr rfl fun b _ => by rw [(M b b').opOf_indep (h b) (s b) (s' b)]
end Mat
end Formalism.L2.Col.GFam
