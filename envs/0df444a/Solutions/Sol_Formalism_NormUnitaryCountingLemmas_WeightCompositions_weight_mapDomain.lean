-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.WeightCompositions.weight_mapDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:47:08.628651+00:00
-- url     : https://prove2.me/submissions/ac27ce49-4d50-4b53-90ec-56fd51fda3b0

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
theorem _root_.solution {σ τ M : Type*} [AddCommMonoid M] (f : σ → τ) (w : τ → M)
    (d : σ →₀ ℕ) :
    Finsupp.weight w (Finsupp.mapDomain f d) = Finsupp.weight (fun i => w (f i)) d := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index]
  · intro; simp
  · intros; exact add_smul _ _ _
end Formalism.NormUnitaryCountingLemmas.WeightCompositions
