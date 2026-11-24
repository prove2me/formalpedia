-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.WeightCompositions.finrank_Hw_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:21:27.240292+00:00
-- url     : https://prove2.me/submissions/be09a1c7-ade6-4c18-9cfa-746e2d116084

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_LtSuccOfMemWeightCompositions
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_finrank_Hw_le

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
theorem _root_.solution (h3p : NormUnitaryPermutationInvariance.{u}) (σ : Equiv.Perm (Fin n)) (w : Fin n → ℕ) :
    Module.finrank K ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) (w ∘ σ)) =
      Module.finrank K ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) w) := by
  apply le_antisymm
  · have h := finrank_Hw_le (K := K) ν h3p σ (w ∘ σ)
    have e : (w ∘ σ) ∘ σ.symm = w := by funext k; simp
    rwa [e] at h
  · have h := finrank_Hw_le (K := K) ν h3p σ.symm w
    rwa [Equiv.symm_symm] at h
end Formalism.NormUnitaryCountingLemmas.WeightCompositions
