-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biLe_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:23.133503+00:00
-- url     : https://prove2.me/submissions/1e7c4274-e194-4d77-bbae-379418c28e92

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MinorProdBlockDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
variable {K ι κ : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (n0 : ι →₀ ℕ) : BiLe n0 (0 : MvPolynomial κ (MvPolynomial ι K)) := by
  intro β n hn
  simp at hn
end Formalism.InvariantFactorPaths.G7
