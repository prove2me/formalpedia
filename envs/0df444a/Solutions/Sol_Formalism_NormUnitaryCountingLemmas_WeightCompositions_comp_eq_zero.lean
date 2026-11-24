-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.WeightCompositions.comp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:06:51.335485+00:00
-- url     : https://prove2.me/submissions/7c5c4b0a-0f5d-490a-8ade-d7c6ed243814

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_LtSuccOfMemWeightCompositions
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_sum_coordWt
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_mem_S0_of_sum_eq
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
variable {K : Type u} [Field K] (ν : Fin N → ℕ)
namespace Formalism.NormUnitaryCountingLemmas.WeightCompositions
theorem _root_.solution {F : MvPolynomial (Fin N × Fin n) K} (hF : F ∈ H K ν) (w : Fin n → ℕ)
    (hw : w ∉ S0 n (∑ j, ν j)) : weightedHomogeneousComponent (coordWt N n) w F = 0 := by
  apply weightedHomogeneousComponent_eq_zero'
  intro d hd hdw
  apply hw
  have hb : Finsupp.weight (blockWt N n) d = ν := mem_block ν hF (mem_support_iff.mp hd)
  apply mem_S0_of_sum_eq
  rw [← hdw, sum_coordWt, ← sum_blockWt, hb]
end Formalism.NormUnitaryCountingLemmas.WeightCompositions
