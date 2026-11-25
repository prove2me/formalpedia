-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.example_stable_lattice_condition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:03:47.758882+00:00
-- url     : https://prove2.me/submissions/363bdb62-f39a-4c2f-be31-9018fabb6047

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
import Theorems.Thm_P2M_Formalism_L2_Indef_Tree_sc_one__93479485a0cc
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
theorem _root_.solution : LeafLemmaS (exampleObject K v0 Tw0) := by
  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Unit), (exampleObject K v0 Tw0).Th v j ≤ (exampleObject K v0 Tw0).Ms j ∧
      (∀ g : Unit, ((exampleObject K v0 Tw0).Th v j).map (((exampleObject K v0 Tw0).ρ j g).restrictScalars (𝓞 K)) ≤
        (exampleObject K v0 Tw0).Th v j) ∧
      (exampleObject K v0 Tw0).σ v j ≠ 0 ∧ (exampleObject K v0 Tw0).Th v j ≤ sc ((exampleObject K v0 Tw0).σ v j) ((exampleObject K v0 Tw0).ThK v j) :=
    fun v j => ⟨le_rfl, fun g => le_of_eq (map_id' K _), one_ne_zero, le_of_eq (sc_one' K _).symm⟩
  intro w _
  exact ⟨key w, key (conjPl w)⟩
end Formalism.L2.Indef.Tree
