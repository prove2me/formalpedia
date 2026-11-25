-- Prove2me | solution 1 for Formalism.L2.Col.LocOp.op_mem_intOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:12:17.200805+00:00
-- url     : https://prove2.me/submissions/aa87854c-4531-45d0-b164-f51d0e1e1014

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
namespace Formalism.L2.Col
namespace LocOp
theorem _root_.solution {S S' : GSD K} (A : LocOp S S') (N : S.D → Submodule (𝓞 K) S.V)
    (N' : S'.D → Submodule (𝓞 K) S'.V) (hk : ∀ d' d, ∀ x ∈ N d, A.ker d' d x ∈ N' d') (φ : S.EqFun)
    (hφ : φ ∈ S.intOf N) : A.op φ ∈ S'.intOf N' := by
  intro d'
  show ∑ d ∈ (A.ker d').support, (A.ker d' d) ((φ : S.D → S.V) d) ∈ N' d'
  exact sum_mem fun d _ => hk d' d _ (hφ d)
end LocOp
end Formalism.L2.Col
