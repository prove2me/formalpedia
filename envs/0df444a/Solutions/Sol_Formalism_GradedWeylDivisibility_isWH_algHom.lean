-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.isWH_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:05.856949+00:00
-- url     : https://prove2.me/submissions/d643ebc0-2a32-4bba-99c7-dd7af2247c07

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowstLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_isWH_algHom_monomial

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
open Formalism Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {σ τ M : Type*} [AddCommMonoid M]
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (w : σ → M) (w' : τ → M)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (w v)) {f : MvPolynomial σ R} {d : M}
    (hf : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous w' (φ f) d := by
  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun s hs => ?_
  have h := isWH_algHom_monomial φ w w' hφ s (coeff s f)
  rwa [hf (mem_support_iff.mp hs)] at h
end Formalism.GradedWeylDivisibility
