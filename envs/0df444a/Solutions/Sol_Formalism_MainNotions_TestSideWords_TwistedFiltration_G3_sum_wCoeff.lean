-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.sum_wCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:41:48.077278+00:00
-- url     : https://prove2.me/submissions/710a96d2-d087-4d17-96bd-59d0d7084179

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TwistSubXMemSupported

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
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
open Classical
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
theorem _root_.solution (w : Set ι) (F : MvPolynomial (ι × Fin n) R) :
    F = ∑ M ∈ F.support.image (fun μ => μ.filter (fun v => v.1 ∈ w)), monomial M 1 * wCoeff w M F := by
  calc F = ∑ μ ∈ F.support, monomial μ (coeff μ F) := F.as_sum
    _ = ∑ M ∈ F.support.image (fun μ => μ.filter (fun v => v.1 ∈ w)),
          ∑ μ ∈ F.support with μ.filter (fun v => v.1 ∈ w) = M, monomial μ (coeff μ F) :=
        (Finset.sum_fiberwise_of_maps_to (fun μ hμ => Finset.mem_image_of_mem _ hμ) _).symm
    _ = _ := by
        refine Finset.sum_congr rfl fun M _ => ?_
        unfold wCoeff
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun μ hμ => ?_
        rw [monomial_mul, one_mul]
        congr 1
        rw [← (Finset.mem_filter.1 hμ).2, Finsupp.filter_pos_add_filter_neg]
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
