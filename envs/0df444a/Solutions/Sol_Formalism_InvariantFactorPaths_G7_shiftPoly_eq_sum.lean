-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.shiftPoly_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:42.502236+00:00
-- url     : https://prove2.me/submissions/71eb153b-bb56-4186-b964-9ad703d4b945

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
theorem _root_.solution [Fintype κ] (b : κ → ι → K) (Q : MvPolynomial ι K) :
    shiftPoly b Q = ∑ n0 ∈ Q.support, MvPolynomial.C (MvPolynomial.C (MvPolynomial.coeff n0 Q)) *
      ∏ x ∈ n0.support, (MvPolynomial.C (MvPolynomial.X x) +
        ∑ k, MvPolynomial.C (MvPolynomial.C (b k x)) * MvPolynomial.X k :
          MvPolynomial κ (MvPolynomial ι K)) ^ n0 x := by
  rw [shiftPoly, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl (fun n0 _ => ?_)
  rw [MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
end Formalism.InvariantFactorPaths.G7
