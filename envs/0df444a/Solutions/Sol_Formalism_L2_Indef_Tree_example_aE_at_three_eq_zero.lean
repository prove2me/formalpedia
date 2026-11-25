-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.example_aE_at_three_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:46:42.614998+00:00
-- url     : https://prove2.me/submissions/a716e98f-2d9c-4a17-a476-28da447331e4

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
theorem _root_.solution : (exampleObject K v0 Tw0).aE () 3 = 0 := by
  show (1 : ℝ) * (Real.log 1 * 1 * 0 + 8 * 1 * (0 + 0)) / ((3 : ℕ) : ℝ) + 1 * 1 * 0 * 0 + 0 * 0 +
    (if (1 : ℝ) < ((3 : ℕ) : ℝ) then 1 * 1 * 0 / ((3 : ℕ) : ℝ) ^ 2 else 0) = 0
  simp
end Formalism.L2.Indef.Tree
