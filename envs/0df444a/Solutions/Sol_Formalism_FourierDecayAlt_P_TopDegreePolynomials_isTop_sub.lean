-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TopDegreePolynomials.isTop_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:16:09.998947+00:00
-- url     : https://prove2.me/submissions/ac91c7ab-a469-4675-b540-46f7fc017b94

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
theorem _root_.solution {W W' : ℝ → ℂ} {d : ℕ} {c c' : ℂ} (h : IsTopCoeff W d c)
    (h' : IsTopCoeff W' d c') : IsTopCoeff (fun Y => W Y - W' Y) d (c - c') := by
  obtain ⟨P, hd, hc, hP⟩ := h
  obtain ⟨P', hd', hc', hP'⟩ := h'
  exact ⟨P - P', (natDegree_sub_le_of_le hd hd').trans (by simp), by rw [coeff_sub, hc, hc'],
    fun Y => by simp only [eval_sub, hP, hP']⟩
end Formalism.FourierDecayAlt.P.TopDegreePolynomials
