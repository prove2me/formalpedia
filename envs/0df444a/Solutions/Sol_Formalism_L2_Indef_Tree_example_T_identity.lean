-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.example_T_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:20.11426+00:00
-- url     : https://prove2.me/submissions/3036b5a0-9e7c-4455-a275-db794bbe4dbf

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
import Theorems.Thm_P2M_Formalism_L2_Indef_Tree_map_id__e509ab30fe6d

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (t : Bool) (j : Unit) : (exampleObject K v0 Tw0).TjId j w t := by
  unfold OnObj.TjId OnObj.ImageLattice
  have h1 : ∀ A : Submodule (𝓞 K) (Fin 1 → K),
      A.map ((LinearMap.id : (Fin 1 → K) →ₗ[K] (Fin 1 → K)).restrictScalars (𝓞 K)) = A := fun A => map_id' K A
  show (matLat (1 : Matrix (Fin 1) (Fin 1) K) (stdLat K 1)).map
      ((LinearMap.id : (Fin 1 → K) →ₗ[K] (Fin 1 → K)).restrictScalars (𝓞 K)) =
    (((stdLat K 1).map ((LinearMap.id : (Fin 1 → K) →ₗ[K] (Fin 1 → K)).restrictScalars (𝓞 K))).map
      ((LinearMap.id : (Fin 1 → K) →ₗ[K] (Fin 1 → K)).restrictScalars (𝓞 K))).map
      ((LinearMap.id : (Fin 1 → K) →ₗ[K] (Fin 1 → K)).restrictScalars (𝓞 K))
  simp only [matLat_one', h1]
end Formalism.L2.Indef.Tree
