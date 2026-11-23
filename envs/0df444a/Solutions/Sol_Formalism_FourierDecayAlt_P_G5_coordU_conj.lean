-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.coordU_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:42.777536+00:00
-- url     : https://prove2.me/submissions/7426d13e-0ace-406d-b66e-6897208a8653

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_wMat_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mul_wMat_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G5
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    coordU (wMat n * A * wMat n)ᵀ = coordU A ∘ revEquiv n := by
  funext p
  simp only [coordU, Matrix.transpose_apply, mul_wMat_apply, wMat_mul_apply, Function.comp, revEquiv,
    Equiv.coe_fn_mk]
end Formalism.FourierDecayAlt.P.G5
