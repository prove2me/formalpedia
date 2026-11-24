-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.isWH_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:11:11.318912+00:00
-- url     : https://prove2.me/submissions/a16e7d2e-202a-40be-9875-40340287373d

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearHypothesisTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
variable {R : Type*} [CommRing R]
namespace Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
theorem _root_.solution (n : ℕ) :
    (detPoly R n).IsWeightedHomogeneous (blockWt n n) (fun _ => 1) := by
  classical
  rw [detPoly, Matrix.det_apply, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule]
  have hsum : (∑ i, blockWt n n (σ i, i)) = fun _ => 1 := by
    funext j
    simp only [blockWt, Finset.sum_apply]
    rw [Equiv.sum_comp σ (fun i' => (Pi.single i' 1 : Fin n → ℕ) j)]
    simp [Pi.single_apply]
  rw [← hsum]
  exact IsWeightedHomogeneous.prod _ _ _ (fun i _ => isWeightedHomogeneous_X R _ _)
end Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
