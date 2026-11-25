-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.matrix_adjoint_action_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:05:12.995222+00:00
-- url     : https://prove2.me/submissions/22fd3825-542b-4038-a3a6-3be19b55ebe2

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_matrix_action_evaluation_holds
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_unitary
import Theorems.Thm_Formalism_QuantumDeterminants_unitary_group_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate TensorProduct
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : RankTwoSkewConjugation := by
  intro n H hH g hg e v
  obtain ⟨hgu, hgi⟩ := (unitary_group_holds n H hH).2.2 g hg
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hgu
  have hu : ∀ x w : Fin n → ℂ, herm H (g *ᵥ x) w = herm H x (g⁻¹ *ᵥ w) := by
    intro x w
    rw [← ggHerm_unitary H g hg x (g⁻¹ *ᵥ w), Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp only [Matrix.toLin'_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, matrix_action_evaluation_holds, matrix_action_evaluation_holds, Matrix.mulVec_sub,
    Matrix.mulVec_smul, Matrix.mulVec_smul, hu, hu]
end Formalism.HermitianLatticeCounting.P
