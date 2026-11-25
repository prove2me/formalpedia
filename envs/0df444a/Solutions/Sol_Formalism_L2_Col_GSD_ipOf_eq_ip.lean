-- Prove2me | solution 1 for Formalism.L2.Col.GSD.ipOf_eq_ip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:11:36.414651+00:00
-- url     : https://prove2.me/submissions/68e07969-2343-4370-936e-6a5f6b9c642c

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_ipOf_indep

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
open Formalism.L2.Col.GSD
variable (S : GSD K)
namespace Formalism.L2.Col.GSD
theorem _root_.solution (h : S.Ok) (s : S.Sec) (φ ψ : S.EqFun) : S.ipOf h s φ ψ = S.ip h φ ψ := by
  exact (S.ipOf_indep h s S.outSec φ ψ).trans rfl
end Formalism.L2.Col.GSD
