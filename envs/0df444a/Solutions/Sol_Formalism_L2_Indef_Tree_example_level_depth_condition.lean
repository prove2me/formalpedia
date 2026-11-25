-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.example_level_depth_condition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:07:43.951396+00:00
-- url     : https://prove2.me/submissions/46bb112f-4e6c-45ab-96a9-b1c1c70c8a24

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
import Theorems.Thm_Formalism_L2_Indef_Tree_toy_vw_one
import Theorems.Thm_Formalism_L2_Indef_Tree_example_ramification_zero

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
variable (h3 : ∀ w ∈ Tw0, plc w = 3)
include h3
omit h3
variable (h5 : ∀ w ∈ Tw0, plc w = 5)
include h5
namespace Formalism.L2.Indef.Tree
theorem _root_.solution (F E : ℝ) : LeafDepthLevel (exampleConstants K v0 F E) (exampleObject K v0 Tw0) := by
  intro w hw _ j
  have hnn : ∀ v, (exampleObject K v0 Tw0).nn v j = 0 := by
    intro v
    show ((vw v (1 : K) : ℤ) : ℝ) / (ramw v : ℝ) = 0
    rw [toy_vw_one]
    simp
  have hF0 : (exampleConstants K v0 F E).F0 w j = 0 := by
    show (if plc w = 3 then F else 0) = 0
    rw [if_neg (by rw [h5 w hw]; norm_num)]
  rw [example_ramification_zero, example_ramification_zero, hnn, hnn, hF0]
  show (0 : ℝ) ≤ 2 * 0 - 0 ∧ (0 : ℝ) ≤ 2 * 0 - 0 ∧ (0 : ℝ) + 0 = -(2 * 0)
  norm_num
end Formalism.L2.Indef.Tree
