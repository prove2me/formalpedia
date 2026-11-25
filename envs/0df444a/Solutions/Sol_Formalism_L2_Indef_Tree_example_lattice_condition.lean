-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.example_lattice_condition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:07:37.576852+00:00
-- url     : https://prove2.me/submissions/f4e913ee-1997-4c7f-8c1a-1b58b362cc02

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
import Theorems.Thm_P2M_Formalism_L2_Indef_Tree_cut_top__4ae350ae3262
import Theorems.Thm_P2M_Formalism_L2_Indef_Tree_sc_one__93479485a0cc
import Theorems.Thm_Formalism_L2_Indef_Tree_toy_card
import Theorems.Thm_Formalism_L2_Indef_Tree_example_eigenspace_eq_top
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key


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
theorem _root_.solution : LeafData (exampleObject K v0 Tw0) := by
  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Unit), ((exampleObject K v0 Tw0).Th0 v j).FG ∧
      (exampleObject K v0 Tw0).Th0 v j ≤
        (eig ((exampleObject K v0 Tw0).ρ j) (exampleObject K v0 Tw0).U (exampleObject K v0 Tw0).ψ).restrictScalars (𝓞 K) ∧
      sc ((Nat.card (exampleObject K v0 Tw0).U : ℕ) : K) (cut (eig ((exampleObject K v0 Tw0).ρ j) (exampleObject K v0 Tw0).U (exampleObject K v0 Tw0).ψ)
        ((exampleObject K v0 Tw0).ThK v j)) ≤ (exampleObject K v0 Tw0).Th0 v j := by
    intro v j
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_, le_of_eq ?_⟩
    · rw [example_eigenspace_eq_top, Submodule.restrictScalars_top]
      exact le_top
    · rw [example_eigenspace_eq_top, cut_top', show (exampleObject K v0 Tw0).U = ⊤ from rfl, toy_card, Nat.cast_one, sc_one']
  intro w _
  exact ⟨key w, key (conjPl w)⟩
end Formalism.L2.Indef.Tree
