-- Prove2me | solution 1 for Formalism.L2.Col.BiPair.sumOf_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:06:34.463623+00:00
-- url     : https://prove2.me/submissions/932ada36-061f-40fc-9e23-08c61be19bdc

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_ClsKer_term_smul
import Theorems.Thm_Formalism_L2_Col_GSD_csOf_indep
import Theorems.Thm_Formalism_L2_Col_BiPair_term_smul

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
open Formalism.L2.Col.BiPair
variable {S S' : GSD K} (P : BiPair S S')
namespace Formalism.L2.Col.BiPair
theorem _root_.solution (h' : S'.Ok) (s s' : S'.Sec) (φ : S.EqFun) (ψ : S'.EqFun) :
    P.sumOf h' s φ ψ = P.sumOf h' s' φ ψ := by
  unfold sumOf
  exact S'.csOf_indep h' s s' _ (fun g d' => P.term_smul φ ψ g d')
end Formalism.L2.Col.BiPair
