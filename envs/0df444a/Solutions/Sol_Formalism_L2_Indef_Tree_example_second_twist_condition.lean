-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.example_second_twist_condition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:37:29.719249+00:00
-- url     : https://prove2.me/submissions/baa6c0b8-4f62-44e1-b1c7-749a7d532bfb

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
import Theorems.Thm_Formalism_L2_Indef_Tree_stdLat_isLatIn
import Theorems.Thm_P2M_Formalism_L2_Indef_Tree_map_id__e509ab30fe6d
import Theorems.Thm_Formalism_L2_Indef_Tree_example_Zg_eq_top
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key


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
theorem _root_.solution : LeafTW2 (exampleObject K v0 Tw0) := by
  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Unit), IsLatIn ((exampleObject K v0 Tw0).Zg j) ((exampleObject K v0 Tw0).X₃ v j) ∧
      IsLatIn ((exampleObject K v0 Tw0).Zg j) ((exampleObject K v0 Tw0).Im v j) ∧
      Formalism.HermitianLatticesTheory.localization₂ v.asIdeal ((exampleObject K v0 Tw0).X₃ v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal ((exampleObject K v0 Tw0).Im v j) := by
    intro v j
    have hIm : (exampleObject K v0 Tw0).Im v j = stdLat K 1 := by
      unfold OnObj.Im
      rw [show ((exampleObject K v0 Tw0).Mt v j).map (((exampleObject K v0 Tw0).θ' v j).restrictScalars (𝓞 K)) = stdLat K 1
        from map_id' K _]
      exact map_id' K _
    rw [example_Zg_eq_top, hIm]
    exact ⟨stdLat_isLatIn K 1, stdLat_isLatIn K 1, le_rfl⟩
  intro w _
  exact ⟨key w, key (conjPl w)⟩
end Formalism.L2.Indef.Tree
