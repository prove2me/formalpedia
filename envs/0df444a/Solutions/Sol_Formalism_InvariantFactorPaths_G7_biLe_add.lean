-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biLe_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:23.390393+00:00
-- url     : https://prove2.me/submissions/ae5cc571-5866-40e8-8591-bba4770e7501

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
theorem _root_.solution {n0 : ι →₀ ℕ} {W W' : MvPolynomial κ (MvPolynomial ι K)} (h : BiLe n0 W)
    (h' : BiLe n0 W') : BiLe n0 (W + W') := by
  classical
  intro β n hn
  rw [MvPolynomial.coeff_add] at hn
  rcases Finset.mem_union.mp (MvPolynomial.support_add hn) with hn1 | hn1
  · exact h β n hn1
  · exact h' β n hn1
end Formalism.InvariantFactorPaths.G7
