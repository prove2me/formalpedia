-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.example_first_twist_condition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:43:43.513854+00:00
-- url     : https://prove2.me/submissions/0ac3b2d5-0858-4ed1-b848-19dfaa906849

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
theorem _root_.solution : LeafTW1 (exampleObject K v0 Tw0) := by
  have hz : ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Unit),
      (lix v (cut ((exampleObject K v0 Tw0).Zg j) ((exampleObject K v0 Tw0).Ms j)) ((exampleObject K v0 Tw0).X₃ v j) : ℝ) ≤
        (lix v (cut ((exampleObject K v0 Tw0).Zg j) ((exampleObject K v0 Tw0).Ms j)) ((exampleObject K v0 Tw0).eJ v j) : ℝ) +
          (ramw v : ℝ) * (exampleObject K v0 Tw0).ε0 v j := by
    intro v j
    rw [show (exampleObject K v0 Tw0).eJ v j = stdLat K 1 from map_id' K _]
    show _ ≤ _ + (ramw v : ℝ) * 0
    rw [mul_zero, add_zero]
  refine ⟨fun w _ => ⟨fun j => ⟨le_rfl, hz w j⟩, fun j => ⟨le_rfl, hz (conjPl w) j⟩⟩, fun w _ => ?_⟩
  show ∑ j : Unit, ((0 : ℝ) + 0) ≤ 2 / ((plc w : ℕ) : ℝ) ^ 2
  simp only [add_zero, Finset.sum_const_zero]
  positivity
end Formalism.L2.Indef.Tree
