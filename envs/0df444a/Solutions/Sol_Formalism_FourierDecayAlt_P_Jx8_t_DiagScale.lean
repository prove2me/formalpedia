-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.t_DiagScale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:22.495968+00:00
-- url     : https://prove2.me/submissions/aa73e8e4-38f8-45df-bfc1-eb81603e64ba

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution : DiagScale := by
  intro α F k a h
  classical
  unfold TB.PSDOn at h ⊢
  have := h.conjTranspose_mul_mul_same (Matrix.diagonal (fun x : F => ((a x : ℝ) : ℂ)))
  convert this using 1
  ext x y
  simp [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring
end Formalism.FourierDecayAlt.P.Jx8
