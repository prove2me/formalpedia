-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.WeightCompositions.T_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:45:19.668817+00:00
-- url     : https://prove2.me/submissions/54a98127-74bd-452f-b24f-4d7e8d5efcba

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_LtSuccOfMemWeightCompositions

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
theorem _root_.solution (h3w : NormUnitaryWeight.{u}) (k : Fin n) (i : ℕ) :
    ∀ F ∈ H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i, ∀ w,
      weightedHomogeneousComponent (coordWt N n) w F ∈
        H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i := by
  classical
  intro F hF w
  rw [Submodule.mem_inf] at hF ⊢
  refine ⟨h3w K N n ν F hF.1 w, ?_⟩
  have hi := hF.2
  rw [mem_weightedHomogeneousSubmodule] at hi ⊢
  intro d hd
  apply hi
  intro h0
  apply hd
  rw [coeff_weightedHomogeneousComponent, h0]
  simp
end Formalism.NormUnitaryCountingLemmas.WeightCompositions
