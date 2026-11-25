-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.theorem_zero_condition_not_automatic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:11:14.034848+00:00
-- url     : https://prove2.me/submissions/200b1255-3ef9-4350-aa65-f76b608ac832

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
import Theorems.Thm_Formalism_L2_Indef_Tree_lw_pos
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_lw_pos


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
theorem _root_.solution (w0 : HeightOneSpectrum (𝓞 K)) :
    ¬ LatticeIndexBoundAtPairs ({ exampleObject K v0 {w0} with r1 := fun _ _ => (8 * Real.exp 300 + 1) / lw w0 } : OnObj (exampleIndefiniteData K v0 {w0} 0) Unit exampleC) := by
  intro h
  have h1 := (h.2.2.2.2 () {w0}).1
  rw [Finset.sum_singleton] at h1
  have hl := lw_pos w0
  change lw w0 * ((8 * Real.exp 300 + 1) / lw w0) ≤ ((1 : ℕ) : ℝ) * (8 * 1 * Real.exp ((300 : ℝ) ^ (1 : ℝ)) * 1) at h1
  have e : lw w0 * ((8 * Real.exp 300 + 1) / lw w0) = 8 * Real.exp 300 + 1 := by
    field_simp
  rw [e, Real.rpow_one] at h1
  push_cast at h1
  linarith
end Formalism.L2.Indef.Tree
