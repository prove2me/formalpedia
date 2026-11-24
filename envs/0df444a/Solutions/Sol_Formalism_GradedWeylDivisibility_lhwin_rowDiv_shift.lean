-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwin_rowDiv_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:53.901852+00:00
-- url     : https://prove2.me/submissions/e875fcb4-cf0f-4419-ad5f-b59e9aee1ad5

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwinShift_rowGen_monomial

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
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (R : Type*) [CommRing R] {r n : ℕ} (H : ℤ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (lhwinHt r n) f H) :
    IsWeightedHomogeneous (lhwinHt r n) (rowDiv R a b k f) (H + k * ((a.val : ℤ) - b.val)) := by
  unfold rowDiv
  conv => enter [2, 1, 2]; rw [f.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have := lhwinShift_rowGen_monomial R a b d (coeff d f) k
  rwa [hf (mem_support_iff.mp hd)] at this
end Formalism.GradedWeylDivisibility
