-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.example_error_at_five
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:13:33.064799+00:00
-- url     : https://prove2.me/submissions/1bb713bc-e0b7-4a80-a184-bf165e64ed10

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
import Theorems.Thm_Formalism_L2_Indef_Tree_example_r_eq_zero

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (hw : plc w = 5) (j : Unit) : (exampleObject K v0 Tw0).errOn w j = 32 := by
  cases j
  have he : (exampleObject K v0 Tw0).errP () 5 = 32 := by
    unfold OnObj.errP
    rw [if_pos (show (5 : ℕ) = (exampleObject K v0 Tw0).g1 ∨ (5 : ℕ) = (exampleObject K v0 Tw0).g2 from Or.inl rfl)]
    show 4 * (0 : ℝ) + 4 * 8 * 1 ^ 2 = 32
    norm_num
  unfold OnObj.errOn OnObj.errl
  rw [hw, example_r_eq_zero, example_r_eq_zero, he]
  simp
end Formalism.L2.Indef.Tree
