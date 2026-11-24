-- Prove2me | solution 1 for Formalism.L2.Col.ClsKer.appOf_indep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:49.047871+00:00
-- url     : https://prove2.me/submissions/9d71a3e9-2cad-4e70-bd52-2870aee11db7

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_wt_eq
import Theorems.Thm_Formalism_L2_Col_GSD_card_stab_smul
import Theorems.Thm_Formalism_L2_Col_GSD_Sec_exists_smul
import Theorems.Thm_Formalism_L2_Col_ClsKer_term_smul

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
open Formalism.L2.Col.ClsKer
variable {S S' : GSD K} (A : ClsKer S S')
namespace Formalism.L2.Col.ClsKer
theorem _root_.solution (h : S.Ok) (s s' : S.Sec) (φ : S.EqFun) : A.appOf h s φ = A.appOf h s' φ := by
  funext d'
  unfold appOf
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, hg⟩ := GSD.Sec.exists_smul s s' c
  rw [S.wt_eq h s c, S.wt_eq h s' c, ← hg, S.card_stab_smul, A.term_smul]
end Formalism.L2.Col.ClsKer
