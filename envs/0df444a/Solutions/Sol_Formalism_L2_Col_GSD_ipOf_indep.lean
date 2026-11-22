-- Prove2me | solution 1 for Formalism.L2.Col.GSD.ipOf_indep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:54:34.32388+00:00
-- url     : https://prove2.me/submissions/c61f14d3-d870-4ad4-9e88-0e3fad5eddf2

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_card_stab_smul
import Theorems.Thm_Formalism_L2_Col_GSD_ipOf_eq_sum
import Theorems.Thm_Formalism_L2_Col_GSD_Sec_exists_smul

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
theorem _root_.solution (h : S.Ok) (s s' : S.Sec) (φ ψ : S.EqFun) : S.ipOf h s φ ψ = S.ipOf h s' φ ψ := by
  rw [S.ipOf_eq_sum h s, S.ipOf_eq_sum h s']
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, hg⟩ := Sec.exists_smul s s' c
  rw [← hg, φ.2, ψ.2, h.inv, card_stab_smul]
end Formalism.L2.Col.GSD
