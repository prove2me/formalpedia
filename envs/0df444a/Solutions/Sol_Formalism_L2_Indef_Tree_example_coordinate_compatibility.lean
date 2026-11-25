-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.example_coordinate_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:22:53.736259+00:00
-- url     : https://prove2.me/submissions/6393f75e-b4e1-475e-a983-41d45fd05e00

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsWeightedConditional
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditions
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ErrSum
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_UnipotentNumeric
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditionsOfExact
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Theorems.Thm_P2M_Formalism_L2_Indef_Tree_map_id__e509ab30fe6d
import Theorems.Thm_P2M_Formalism_L2_Indef_Tree_cut_top__4ae350ae3262
import Theorems.Thm_Formalism_L2_Indef_Tree_example_Zg_eq_top
import Theorems.Thm_Formalism_L2_Indef_Tree_example_T_identity

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
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (K)
variable {K} (v0 : InfinitePlace K) (Tw0 : Finset (HeightOneSpectrum (𝓞 K)))
namespace Formalism.L2.Indef.Tree
theorem _root_.solution : TieCoord (exampleObject K v0 Tw0) := by
  refine ⟨fun j => ⟨fun _ _ h => h, ?_, ?_⟩, fun w _ j => ⟨example_T_identity v0 Tw0 _ _ j, example_T_identity v0 Tw0 _ _ j⟩⟩
  · rw [example_Zg_eq_top]
    exact LinearMap.range_id
  · rw [example_Zg_eq_top, cut_top']
    exact map_id' K _
end Formalism.L2.Indef.Tree
