-- Prove2me | solution 1 for Formalism.L2.Col.GFam.dim_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:07:20.980559+00:00
-- url     : https://prove2.me/submissions/cf6c56f0-c24e-4fe1-8c3f-fee27309e938

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_finiteDimensional_EqFun

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
theorem _root_.solution (h : F.Ok) (s : ∀ b, (F.mem b).Sec) :
    (F.toCSDOf h s).dim = ∑ b, finrank K (F.mem b).EqFun := by
  unfold CSD.dim
  haveI : ∀ b, Module.Finite K (F.mem b).EqFun := fun b => (F.mem b).finiteDimensional_EqFun (h b)
  rw [← (F.resOf h s).finrank_eq, Module.finrank_pi_fintype]
end Formalism.L2.Col.GFam
