-- Prove2me | solution 1 for Formalism.L2.Th1.H.SemicharacterExponentialLemmas.semi_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:26:12.432098+00:00
-- url     : https://prove2.me/submissions/0a67a910-6b49-4ad2-b4a7-1dbb205800e7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_GaussDegenerate
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GapStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.L2.Th1.H.SemicharacterExponentialLemmas
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.L2.Th1.H.SemicharacterExponentialLemmas
theorem _root_.solution {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ} (hα : IsSemiChar H Λ α) {x : V}
    (hx : x ∈ Λ) : ‖α x‖ = 1 := by
  rcases hα.1 x hx with h | h <;> rw [h] <;> simp
end Formalism.L2.Th1.H.SemicharacterExponentialLemmas
