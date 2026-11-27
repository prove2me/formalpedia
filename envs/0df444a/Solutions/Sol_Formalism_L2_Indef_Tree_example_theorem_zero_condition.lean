-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.example_theorem_zero_condition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:01:11.897421+00:00
-- url     : https://prove2.me/submissions/8a6a377c-6fc7-40a8-bdd9-34d7dd6bd42a

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
import Theorems.Thm_Formalism_L2_Indef_Tree_stdLat_isLatIn
import Theorems.Thm_Formalism_L2_Indef_Tree_toy_vw_one
import Theorems.Thm_Formalism_L2_Indef_Tree_example_b_ge
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
namespace Formalism.L2.Indef.Tree
theorem _root_.solution : LatticeIndexBoundAtPairs (exampleObject K v0 Tw0) := by
  have h : ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Unit),
      IsLatIn ⊤ ((exampleObject K v0 Tw0).Th1 v j) ∧ (exampleObject K v0 Tw0).Th1 v j ≤ (exampleObject K v0 Tw0).Th v j ∧
      (exampleObject K v0 Tw0).a v j ≠ 0 ∧ vw v ((exampleObject K v0 Tw0).a v j) = ((exampleObject K v0 Tw0).E v j : ℤ) ∧
      ∀ W : Submodule K (Fin ((exampleObject K v0 Tw0).nZ j) → K),
        (lix v (cut W ((exampleObject K v0 Tw0).Ms j)) (cut W ((exampleObject K v0 Tw0).Th1 v j)) : ℝ) ≤
          ((exampleObject K v0 Tw0).E v j : ℝ) * (finrank K W : ℝ) + (exampleObject K v0 Tw0).r v j := by
    intro v j
    refine ⟨stdLat_isLatIn K 1, le_rfl, one_ne_zero, toy_vw_one v, fun W => ?_⟩
    rw [example_r_eq_zero]
    show (lix v (cut W (stdLat K 1)) (cut W (stdLat K 1)) : ℝ) ≤ ((0 : ℕ) : ℝ) * (finrank K W : ℝ) + 0
    simp [lix, Formalism.HermitianLatticesTheory.lidx]
  have hb := example_b_ge v0 Tw0
  refine ⟨fun w _ => ⟨h w, h (conjPl w)⟩, by norm_num, le_rfl, fun _ _ => ⟨le_rfl, le_rfl⟩, fun _ S' => ?_⟩
  show ∑ v ∈ S', lw v * (0 : ℝ) ≤ ((1 : ℕ) : ℝ) * (8 * 1 * (exampleObject K v0 Tw0).b * 1) ∧
    ∑ v ∈ S', lw v * (0 : ℝ) ≤ ((1 : ℕ) : ℝ) * (8 * 1 * (exampleObject K v0 Tw0).b * 1)
  simp only [mul_zero, Finset.sum_const_zero, Nat.cast_one]
  constructor <;> linarith
end Formalism.L2.Indef.Tree
