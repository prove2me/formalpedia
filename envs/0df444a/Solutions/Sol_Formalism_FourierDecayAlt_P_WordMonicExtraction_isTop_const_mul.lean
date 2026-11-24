-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordMonicExtraction.isTop_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:26.634801+00:00
-- url     : https://prove2.me/submissions/46e47b3f-6db7-4a23-8a18-421a0cd1dd82

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
theorem _root_.solution {W : ℝ → ℂ} {d : ℕ} {c : ℂ} (k : ℂ) (h : IsTopCoeff W d c) :
    IsTopCoeff (fun Y => k * W Y) d (k * c) := by
  unfold IsTopCoeff at h ⊢
  obtain ⟨P, hP, hPc, hW⟩ := h
  exact ⟨Polynomial.C k * P, (Polynomial.natDegree_C_mul_le _ _).trans hP,
    by rw [Polynomial.coeff_C_mul, hPc], fun Y => by simp only [Polynomial.eval_C_mul, hW]⟩
end Formalism.FourierDecayAlt.P.WordMonicExtraction
