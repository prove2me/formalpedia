-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.ShearCoefficients.weight_mapDomain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:08.741104+00:00
-- url     : https://prove2.me/submissions/15e1051c-de62-4c74-adcb-450419b284da

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients

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
theorem _root_.solution {σ τ M : Type*} [AddCommMonoid M] (w : τ → M) (f : σ → τ)
    (d : σ →₀ ℕ) :
    Finsupp.weight w (Finsupp.mapDomain f d) = Finsupp.weight (w ∘ f) d := by
  classical
  simp only [Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index] <;> simp [add_smul]
end Formalism.NormUnitaryCountingLemmas.ShearCoefficients
