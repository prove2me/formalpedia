-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lehw_rowDiv_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:20.325797+00:00
-- url     : https://prove2.me/submissions/e672556a-a7d5-4315-96d8-592f4e1c29a2

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehwShift_rowGen_monomial

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
theorem _root_.solution (R : Type*) [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (δ : ℤ)
    (a b : Fin r) (hstep : ∀ s : Fin n, w (a, s) = w (b, s) + δ) (H : ℤ) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous w f H) :
    IsWeightedHomogeneous w (rowDiv R a b k f) (H + k * δ) := by
  unfold rowDiv
  rw [f.as_sum, map_sum, Polynomial.finset_sum_coeff]
  refine (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sum_mem _ fun d hd => ?_)
  refine (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_
  have h := lehwShift_rowGen_monomial R w δ a b hstep d (coeff d f) k
  rw [hf (mem_support_iff.mp hd)] at h
  exact h
end Formalism.GradedWeylDivisibility
