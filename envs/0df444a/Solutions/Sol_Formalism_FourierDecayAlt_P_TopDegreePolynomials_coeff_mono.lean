-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TopDegreePolynomials.coeff_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:32.241889+00:00
-- url     : https://prove2.me/submissions/fc1da1bc-777f-409c-93e4-3216d1f66dcf

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_TopDegreePolynomials_natDegree_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TopDegreePolynomials
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.TopDegreePolynomials
theorem _root_.solution (h : ℂ) (a b i j : ℕ) (hi : i ≤ a) (hj : j ≤ b) :
    ((X : ℂ[X]) ^ i * (X + C h) ^ j).coeff (a + b) = if i = a ∧ j = b then 1 else 0 := by
  have hm : ((X : ℂ[X]) ^ i * (X + C h) ^ j).Monic := (monic_X_pow i).mul ((monic_X_add_C h).pow j)
  split_ifs with hij
  · obtain ⟨rfl, rfl⟩ := hij
    have := hm.coeff_natDegree
    rwa [natDegree_mono] at this
  · apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_mono]
    omega
end Formalism.FourierDecayAlt.P.TopDegreePolynomials
