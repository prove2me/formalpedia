-- Prove2me | solution 1 for Formalism.L2.Th1.H.quad_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:27:32.35635+00:00
-- url     : https://prove2.me/submissions/0e396cd3-0be2-411d-a4f6-7d07a4b713d3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionInterSubspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.L2.Th1.H
theorem _root_.solution (a b t : ℝ) (ha : 0 < a) : b * t ≤ a * t ^ 2 + b ^ 2 / (4 * a) := by
  rw [← sub_nonneg]
  have e : a * t ^ 2 + b ^ 2 / (4 * a) - b * t = (2 * a * t - b) ^ 2 / (4 * a) := by
    field_simp
    ring
  rw [e]
  positivity
end Formalism.L2.Th1.H
