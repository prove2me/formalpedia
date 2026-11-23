-- Prove2me | solution 1 for Formalism.REAL.fischerInner_pderiv_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:06.035376+00:00
-- url     : https://prove2.me/submissions/c9d35b8f-3109-4048-b2fc-85ff2ee90e13

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Theorems.Thm_Formalism_REAL_fischerInner_monomial_left
import Theorems.Thm_Formalism_REAL_prod_factorial_support_sub_single

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
open Formalism Formalism.REAL
variable {σ : Type*}
namespace Formalism.REAL
theorem _root_.solution [DecidableEq σ] (v : σ) (f g : MvPolynomial σ ℂ) :
    fockF (pderiv v f) g = fockF f (X v * g) := by
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [pderiv_monomial, fischerInner_monomial_left, fischerInner_monomial_left, coeff_X_mul']
    by_cases hv : u v = 0
    · have : v ∉ u.support := Finsupp.notMem_support_iff.mpr hv
      simp [hv, this]
    · have : v ∈ u.support := Finsupp.mem_support_iff.mpr hv
      rw [if_pos this, prod_factorial_support_sub_single u v hv]
      push_cast; ring
  | add p q hp hq => rw [map_add, fischerInner_add_left, fischerInner_add_left, hp, hq]
end Formalism.REAL
