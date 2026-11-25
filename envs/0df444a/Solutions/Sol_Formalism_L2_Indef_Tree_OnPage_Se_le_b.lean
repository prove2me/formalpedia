-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.OnPage.Se_le_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:10:30.178289+00:00
-- url     : https://prove2.me/submissions/0275c8e8-051c-442b-a1d7-4b880e337994

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONPage
import Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_one_le_b
import Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_one_le_Xp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.L2.Indef.Tree.OnPage
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}
namespace Formalism.L2.Indef.Tree.OnPage
theorem _root_.solution (O : OnObj S P c) (hx : 0 ≤ O.x) (h14 : SupportGapBounds O) : O.Se ≤ O.b := by
  have h1 := one_le_Xp O hx
  have hb := one_le_b O hx
  have h2 := h14.2
  show O.Sc + O.eta ≤ O.b
  by_cases h : 0 ≤ O.Sc + O.eta
  · have : 1 * (O.Sc + O.eta) ≤ Xp O * (O.Sc + O.eta) := mul_le_mul_of_nonneg_right h1 h
    linarith
  · linarith
end Formalism.L2.Indef.Tree.OnPage
