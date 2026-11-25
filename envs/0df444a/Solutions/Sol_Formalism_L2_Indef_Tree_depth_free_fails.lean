-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.depth_free_fails
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:03:05.466368+00:00
-- url     : https://prove2.me/submissions/4279b71c-d35d-4d70-95d6-5681d1245a2c

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
omit h3
namespace Formalism.L2.Indef.Tree
theorem _root_.solution (w0 : HeightOneSpectrum (𝓞 K)) (h3w : plc w0 = 3) (E : ℝ) :
    ¬ LeafDepthGood (exampleConstants K v0 (-10) E) (exampleObject K v0 {w0}) := by
  intro h
  have hn : ¬ (plc w0 ∈ (exampleObject K v0 {w0}).sm ∨ plc w0 = (exampleObject K v0 {w0}).q1 ∨ plc w0 = (exampleObject K v0 {w0}).dd ∨
      plc w0 = (exampleObject K v0 {w0}).g1 ∨ plc w0 = (exampleObject K v0 {w0}).g2) := by
    rw [h3w]
    exact (by decide : ¬ ((3 : ℕ) ∈ ({2} : Finset ℕ) ∨ (3 : ℕ) = 11 ∨ (3 : ℕ) = 13 ∨ (3 : ℕ) = 5 ∨ (3 : ℕ) = 7))
  have hY : ((plc w0 : ℕ) : ℝ) ≤ (exampleObject K v0 {w0}).Y := by
    rw [h3w]
    show ((3 : ℕ) : ℝ) ≤ 1 * 3
    norm_num
  have h1 := ((h.2.2.2 w0 (Finset.mem_singleton_self w0) hn ()).1 hY).1
  rw [example_ramification_zero, h3w, example_aE_at_three_eq_zero] at h1
  have hF : (exampleConstants K v0 (-10) E).F0 w0 () = -10 := by
    show (if plc w0 = 3 then (-10 : ℝ) else 0) = -10
    rw [if_pos h3w]
  rw [hF] at h1
  linarith
end Formalism.L2.Indef.Tree
