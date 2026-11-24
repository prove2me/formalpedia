-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.WeightCompositions.sum_coordWt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:49:42.085909+00:00
-- url     : https://prove2.me/submissions/b941fa49-62d4-4027-a138-1c250f0149cc

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_LtSuccOfMemWeightCompositions
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_weight


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
universe u
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.WeightCompositions
variable {N n : ℕ}
namespace Formalism.NormUnitaryCountingLemmas.WeightCompositions
theorem _root_.solution (d : (Fin N × Fin n) →₀ ℕ) :
    ∑ k, Finsupp.weight (coordWt N n) d k = ∑ p, d p := by
  simp only [Finsupp.weight_eq_sum, Finset.sum_apply, coordWt, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Pi.single_apply]
end Formalism.NormUnitaryCountingLemmas.WeightCompositions
