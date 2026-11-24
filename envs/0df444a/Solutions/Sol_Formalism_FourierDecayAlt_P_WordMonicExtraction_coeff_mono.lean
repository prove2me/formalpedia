-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordMonicExtraction.coeff_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:26.453135+00:00
-- url     : https://prove2.me/submissions/bdf3be40-9cf7-4229-9b60-40fb97ab1727

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_natDegree_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.WordMonicExtraction
theorem _root_.solution (h : ℂ) (a b i j : ℕ) (hi : i ≤ a) (hj : j ≤ b) :
    ((X : ℂ[X]) ^ i * (X + C h) ^ j).coeff (a + b) = if i = a ∧ j = b then 1 else 0 := by
  by_cases hij : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := hij
    rw [if_pos ⟨rfl, rfl⟩]
    have hm := ((Polynomial.monic_X_pow i).mul ((Polynomial.monic_X_add_C h).pow j)).coeff_natDegree
    rw [natDegree_mono] at hm
    exact hm
  · rw [if_neg hij]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [natDegree_mono]
    omega
end Formalism.FourierDecayAlt.P.WordMonicExtraction
