-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.WeightCompositions.weight_coordKWt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:46:32.510549+00:00
-- url     : https://prove2.me/submissions/63aea707-145c-40c7-bbdc-8efb7c2c5425

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
theorem _root_.solution (k : Fin n) (d : (Fin N × Fin n) →₀ ℕ) :
    Finsupp.weight (coordKWt N n k) d = Finsupp.weight (coordWt N n) d k := by
  simp only [Finsupp.weight_eq_sum, Finset.sum_apply, coordWt, coordKWt, Pi.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Pi.single_apply, eq_comm]
end Formalism.NormUnitaryCountingLemmas.WeightCompositions
