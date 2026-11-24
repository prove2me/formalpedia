-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lccomp_colAddGen_homog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:13.009741+00:00
-- url     : https://prove2.me/submissions/0e32d44c-7945-4302-b3df-2848ebc865cc

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCcompLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lccomp_colAddGen_monomial_homog

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
theorem _root_.solution {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n)
    (ω : Fin r × Fin n →₀ ℕ) (f : MvPolynomial (Fin r × Fin n) B)
    (hf : IsWeightedHomogeneous (pairW l j) f ω) :
    IsWeightedHomogeneous (lccompW l j) (colAddGen B l j f) ω := by
  classical
  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have h := lccomp_colAddGen_monomial_homog (B := B) l j d (coeff d f)
  rwa [hf (mem_support_iff.mp hd)] at h
end Formalism.GradedWeylDivisibility
