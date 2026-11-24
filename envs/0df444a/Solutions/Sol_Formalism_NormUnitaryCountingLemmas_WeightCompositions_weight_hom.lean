-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.WeightCompositions.weight_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:47:07.545192+00:00
-- url     : https://prove2.me/submissions/aa593473-0ab8-40aa-92eb-a4c21a2be666

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
namespace Formalism.NormUnitaryCountingLemmas.WeightCompositions
theorem _root_.solution {σ M M' : Type*} [AddCommMonoid M] [AddCommMonoid M'] (g : M →+ M')
    (w : σ → M) (d : σ →₀ ℕ) :
    Finsupp.weight (fun i => g (w i)) d = g (Finsupp.weight w d) := by
  simp only [Finsupp.weight_apply, Finsupp.sum, map_sum, map_nsmul]
end Formalism.NormUnitaryCountingLemmas.WeightCompositions
