-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.OnPage.two_cube_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:07:39.005739+00:00
-- url     : https://prove2.me/submissions/da2b1c04-cb4b-423f-a5f0-9266a15f921b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONPage
import Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_cube_le_two_exp

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
theorem _root_.solution (y n : ℝ) (hy : 0 ≤ y) (hn : 4 ≤ n) : 2 * y ^ 3 ≤ Real.exp y * n := by
  have h := cube_le_two_exp y hy
  have he : 0 < Real.exp y := Real.exp_pos y
  have : Real.exp y * 4 ≤ Real.exp y * n := mul_le_mul_of_nonneg_left hn he.le
  linarith
end Formalism.L2.Indef.Tree.OnPage
