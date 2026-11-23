-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TopDegreePolynomials.isTop_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:12.730771+00:00
-- url     : https://prove2.me/submissions/c083c82a-4c9a-4394-a1c2-9016f704f472

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials

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
theorem _root_.solution {W : ℝ → ℂ} {d : ℕ} {c : ℂ} (k : ℂ) (h : IsTopCoeff W d c) :
    IsTopCoeff (fun Y => k * W Y) d (k * c) := by
  obtain ⟨P, hd, hc, hP⟩ := h
  exact ⟨C k * P, (natDegree_C_mul_le _ _).trans hd, by rw [coeff_C_mul, hc],
    fun Y => by simp only [eval_mul, eval_C, hP]⟩
end Formalism.FourierDecayAlt.P.TopDegreePolynomials
