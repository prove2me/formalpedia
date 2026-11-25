-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral.vN_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:59:33.521495+00:00
-- url     : https://prove2.me/submissions/e639b0e9-816c-44b5-81d3-aae0a417b34a

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoeffOfValues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
theorem _root_.solution (d : ℕ) : IsUnit (vN d).det := by
  rw [isUnit_iff_ne_zero, vN, Matrix.det_vandermonde_ne_zero_iff]
  intro a b h
  have h' : ((a : ℕ) : ℂ) = ((b : ℕ) : ℂ) := h
  exact Fin.ext (by exact_mod_cast h')
end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
