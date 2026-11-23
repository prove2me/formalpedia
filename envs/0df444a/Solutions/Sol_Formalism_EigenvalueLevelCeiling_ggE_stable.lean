-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ggE_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:35.805203+00:00
-- url     : https://prove2.me/submissions/ad5c0dd7-6226-455b-ae20-3feb9c9253c5

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ggE_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution {P : Type} [Group P] (ρ : Representation K P Z) (U : Subgroup P) [Fintype U]
    (ψ : P → 𝓞 K) (L : Submodule (𝓞 K) Z)
    (hst : ∀ g : P, L.map ((ρ g).restrictScalars (𝓞 K)) ≤ L) (x : Z) (hx : x ∈ L) :
    ggE ρ U ψ x ∈ L := by
  rw [ggE_apply]
  refine Submodule.sum_mem _ (fun u _ => ?_)
  rw [algebraMap_smul]
  exact L.smul_mem _ (hst _ ⟨x, hx, rfl⟩)
end Formalism.EigenvalueLevelCeiling
