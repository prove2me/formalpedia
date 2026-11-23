-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordMonicExtraction.isTop_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:24.271005+00:00
-- url     : https://prove2.me/submissions/f284215e-2ccb-4eea-8b66-3336e26cfb91

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction

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
theorem _root_.solution {W W' : ℝ → ℂ} {d : ℕ} {c c' : ℂ} (h : IsTopCoeff W d c)
    (h' : IsTopCoeff W' d c') : IsTopCoeff (fun Y => W Y - W' Y) d (c - c') := by
  unfold IsTopCoeff at h h' ⊢
  obtain ⟨P, hP, hPc, hW⟩ := h
  obtain ⟨P', hP', hPc', hW'⟩ := h'
  exact ⟨P - P', (Polynomial.natDegree_sub_le _ _).trans (max_le hP hP'),
    by rw [Polynomial.coeff_sub, hPc, hPc'], fun Y => by simp only [Polynomial.eval_sub, hW, hW']⟩
end Formalism.FourierDecayAlt.P.WordMonicExtraction
