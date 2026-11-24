-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.ShearCoefficients.isWeightedHomogeneous_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:11:24.064336+00:00
-- url     : https://prove2.me/submissions/1fc07544-0a6b-4e84-85ed-94fc7b15397b

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_weight_mapDomain

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
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.ShearCoefficients
variable {R : Type*} [CommRing R]
namespace Formalism.NormUnitaryCountingLemmas.ShearCoefficients
theorem _root_.solution {σ τ M : Type*} [AddCommMonoid M] {w : τ → M} {f : σ → τ}
    {m : M} {F : MvPolynomial σ R} (hF : F.IsWeightedHomogeneous (w ∘ f) m) :
    (rename f F).IsWeightedHomogeneous w m := by
  refine IsWeightedHomogeneous.induction_on
    (motive := fun p _ => (rename f p).IsWeightedHomogeneous w m) ?_ ?_ ?_ hF
  · simpa using isWeightedHomogeneous_zero R w m
  · intro p q _ _ hp hq
    rw [map_add]; exact hp.add hq
  · intro d r hr
    rw [rename_monomial]
    exact isWeightedHomogeneous_monomial _ _ _ (by rw [weight_mapDomain, hr])
end Formalism.NormUnitaryCountingLemmas.ShearCoefficients
