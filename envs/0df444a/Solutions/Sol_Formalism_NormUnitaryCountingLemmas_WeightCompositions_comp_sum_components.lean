-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.WeightCompositions.comp_sum_components
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:45:20.679337+00:00
-- url     : https://prove2.me/submissions/4a69e774-8d6d-4755-9bd3-8858fcd02532

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
namespace Formalism.NormUnitaryCountingLemmas.WeightCompositions
theorem _root_.solution {σ M K : Type*} [Field K] [AddCommMonoid M] [DecidableEq M]
    (φ : σ → M) (S : Finset M) (g : S → MvPolynomial σ K)
    (hg : ∀ m : S, g m ∈ weightedHomogeneousSubmodule K φ (m : M)) (m : S) :
    weightedHomogeneousComponent φ (m : M) (∑ m', g m') = g m := by
  rw [map_sum]
  rw [Finset.sum_congr rfl fun m' _ => weightedHomogeneousComponent_of_mem (m := (m : M)) (hg m')]
  rw [Finset.sum_eq_single m]
  · simp
  · intro b _ hb
    rw [if_neg]
    exact fun h => hb (Subtype.ext h.symm)
  · simp
end Formalism.NormUnitaryCountingLemmas.WeightCompositions
