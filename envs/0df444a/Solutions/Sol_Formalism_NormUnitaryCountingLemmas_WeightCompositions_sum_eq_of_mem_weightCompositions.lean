-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.WeightCompositions.sum_eq_of_mem_weightCompositions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:49:43.0227+00:00
-- url     : https://prove2.me/submissions/b4814cdc-c549-4969-befe-d020c73e0500

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
theorem _root_.solution {s : ℕ} {w : Fin n → ℕ} (h : w ∈ S0 n s) : ∑ k, w k = s :=
  (Finset.mem_filter.mp h).2
end Formalism.NormUnitaryCountingLemmas.WeightCompositions
