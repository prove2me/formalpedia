-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.example_depth_condition_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:56:16.892877+00:00
-- url     : https://prove2.me/submissions/2a9c1bbe-6dc3-4b89-9593-f03d6442bd0a

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
import Theorems.Thm_Formalism_L2_Indef_Tree_example_b_ge
import Theorems.Thm_Formalism_L2_Indef_Tree_example_ramification_zero
import Theorems.Thm_Formalism_L2_Indef_Tree_example_aE_at_three_eq_zero

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
namespace Formalism.L2.Indef.Tree
theorem _root_.solution (F E : ℝ) (hF : -1 ≤ F) : LeafDepthGood (exampleConstants K v0 F E) (exampleObject K v0 Tw0) := by
  have hY : (exampleObject K v0 Tw0).Y = 3 := by
    show (1 : ℝ) * 3 = 3
    norm_num
  refine ⟨fun _ => ⟨le_rfl, le_rfl⟩, fun Q _ => ?_, fun Q _ => ?_, ?_⟩
  · show ∑ p ∈ Q, (0 : ℝ) * Real.log (p : ℝ) ≤ 1 / 1
    simp
  · show (0 : ℝ) * ∑ p ∈ Q, (0 : ℝ) * Real.log (p : ℝ) ≤ 1 * (1 * (exampleObject K v0 Tw0).b)
    rw [zero_mul]
    linarith [example_b_ge v0 Tw0]
  · intro w hw _ j
    cases j
    have hp := h3 w hw
    have hF0 : (exampleConstants K v0 F E).F0 w () = F := by
      show (if plc w = 3 then F else 0) = F
      rw [if_pos hp]
    refine ⟨fun _ => ?_, fun hlt => ?_⟩
    · rw [example_ramification_zero, example_ramification_zero, hF0, hp, example_aE_at_three_eq_zero]
      constructor <;> linarith
    · exfalso
      rw [hY, hp] at hlt
      norm_num at hlt
end Formalism.L2.Indef.Tree
