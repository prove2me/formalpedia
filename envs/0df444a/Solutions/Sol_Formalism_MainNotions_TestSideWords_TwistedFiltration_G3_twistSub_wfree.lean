-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.twistSub_wfree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:30:12.183484+00:00
-- url     : https://prove2.me/submissions/4dd5a7e7-b62b-498e-9565-169c53cbf40e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TwistSubXMemSupported
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_wfree_iff_supported
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_twistSub_X_mem_supported

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
theorem _root_.solution (w : Set ι) (j : Fin n) (P : MvPolynomial (ι × Fin n) R) (hP : WFree w P) :
    WFree w (twistSub LL S j P) := by
  rw [wfree_iff_supported]
  rw [P.as_sum, map_sum]
  refine Subalgebra.sum_mem _ fun ν hν => ?_
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod]
  refine Subalgebra.mul_mem _ ?_ (Subalgebra.prod_mem _ fun v hv => ?_)
  · rw [twistSub, eval₂Hom_C]
    exact Subalgebra.algebraMap_mem _ _
  · rw [map_pow]
    refine Subalgebra.pow_mem _ ?_ _
    apply twistSub_X_mem_supported
    intro hw
    have h1 := hP ν hν
    have : (ν.filter (fun v => v.1 ∈ w)) v = 0 := by rw [h1]; rfl
    rw [Finsupp.filter_apply, if_pos hw] at this
    exact (Finsupp.mem_support_iff.1 hv) this
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
