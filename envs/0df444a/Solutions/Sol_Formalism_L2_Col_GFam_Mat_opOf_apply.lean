-- Prove2me | solution 1 for Formalism.L2.Col.GFam.Mat.opOf_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:07.355107+00:00
-- url     : https://prove2.me/submissions/9810869e-528d-4775-96ed-be22f33e3b76

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas

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
theorem _root_.solution {F F' : GFam K} (M : Mat F F') (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ : F.Forms)
    (b' : F'.β) : M.opOf h s φ b' = ∑ b, (M b b').opOf (h b) (s b) (φ b) := by
  simp only [Mat.opOf, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
end Mat
end Formalism.L2.Col.GFam
