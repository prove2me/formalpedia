-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.WeightCompositions.coordWt_to_coordKWt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:03:15.796671+00:00
-- url     : https://prove2.me/submissions/cd3d7ca6-9a3b-4dfd-bf85-15a7bda85b37

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_LtSuccOfMemWeightCompositions
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_weight_coordKWt

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
theorem _root_.solution (k : Fin n) {w : Fin n → ℕ} {G : MvPolynomial (Fin N × Fin n) K}
    (hG : G ∈ weightedHomogeneousSubmodule K (coordWt N n) w) :
    G ∈ weightedHomogeneousSubmodule K (coordKWt N n k) (w k) := by
  rw [mem_weightedHomogeneousSubmodule] at hG ⊢
  intro d hd
  rw [weight_coordKWt, hG hd]
end Formalism.NormUnitaryCountingLemmas.WeightCompositions
