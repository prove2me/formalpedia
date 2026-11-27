-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.example_bad_primes_condition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:46:08.86791+00:00
-- url     : https://prove2.me/submissions/95170e7e-a316-4fe9-b02d-5c9191d17763

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
import Theorems.Thm_Formalism_L2_Indef_Tree_example_L_eq
import Theorems.Thm_Formalism_L2_Indef_Tree_example_b_ge

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
namespace Formalism.L2.Indef.Tree
theorem _root_.solution : LeafBad (exampleObject K v0 Tw0) := by
  have hb := example_b_ge v0 Tw0
  refine ⟨?_, ?_, fun j => ⟨?_, ?_, ?_⟩⟩
  · show (0 : ℝ) ≤ 2 * Real.log 143
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 143)
    linarith
  · show (0 : ℝ) ≤ 1
    norm_num
  · show (2 * ((0 : ℝ) + 8 * (0 + 0) + 0 + 1) + 4 * (8 * 1 * 0)) * Real.log ((11 * 13 : ℕ) : ℝ) ≤
      2 * Real.log 143 * (8 * 1 * (exampleObject K v0 Tw0).b)
    have h143 : ((11 * 13 : ℕ) : ℝ) = 143 := by norm_num
    rw [h143]
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 143)
    nlinarith
  · show (∑ p ∈ ({2} : Finset ℕ), Real.log (p : ℝ)) * (2 * (1 * 1 * (2 + 0) * (0 + 8 * (0 + 0))) + 2 * 0 + 2) ≤
      1 * (8 * 1 * (exampleObject K v0 Tw0).b * (exampleObject K v0 Tw0).L)
    rw [Finset.sum_singleton, example_L_eq]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    push_cast
    nlinarith
  · show (4 * (0 : ℝ) + 4 * 8 * 1 ^ 2) * Real.log ((5 * 7 : ℕ) : ℝ) ≤ 4 * (exampleObject K v0 Tw0).b
    have h35 : ((5 * 7 : ℕ) : ℝ) = 35 := by norm_num
    rw [h35]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 35)
    nlinarith
end Formalism.L2.Indef.Tree
