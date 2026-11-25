-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.OnPage.cube_le_two_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:54:40.317745+00:00
-- url     : https://prove2.me/submissions/d038368c-967c-47d8-afa3-6daf674863e2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONPage

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
open Formalism.L2.Indef.Tree.OnPage
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}
namespace Formalism.L2.Indef.Tree.OnPage
theorem _root_.solution (y : ℝ) (hy : 0 ≤ y) : y ^ 3 ≤ 2 * Real.exp y := by
  have h := Real.sum_le_exp_of_nonneg hy 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  nlinarith [sq_nonneg (y ^ 2 - 6 * y), sq_nonneg (y - 4), mul_nonneg hy (sq_nonneg (y - 4)), sq_nonneg y]
end Formalism.L2.Indef.Tree.OnPage
