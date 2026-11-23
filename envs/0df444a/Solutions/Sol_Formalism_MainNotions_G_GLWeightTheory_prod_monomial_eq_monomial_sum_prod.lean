-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.prod_monomial_eq_monomial_sum_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:48.479041+00:00
-- url     : https://prove2.me/submissions/c5a9b8bb-83ea-4866-8e2b-9559defb40f7

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionX
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.G
namespace Formalism.MainNotions.G.GLWeightTheory
theorem _root_.solution {B σ α : Type*} [CommRing B] (s : Finset α) (f : α → σ →₀ ℕ) (c : α → B) :
    ∏ i ∈ s, monomial (f i) (c i) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, c i) := by
  first
  | exact (monomial_sum_index s f c).symm
  | classical
    refine Finset.induction_on s (by simp) ?_
    intro i s hi ih
    rw [prod_insert hi, prod_insert hi, sum_insert hi, ih, monomial_mul]
end Formalism.MainNotions.G.GLWeightTheory
