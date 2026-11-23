-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.norm_det_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:47.56237+00:00
-- url     : https://prove2.me/submissions/ed0849e5-b7c1-42fa-ada2-bfe2bbb455a2

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G9
namespace Formalism.FourierDecayAlt.P.G9
theorem _root_.solution {d : ℕ} {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) : ‖W.det‖ = 1 := by
  have h := (Unitary.mem_iff.1 (Matrix.det_of_mem_unitary hW)).1
  have h2 : ‖W.det‖ ^ 2 = 1 := by
    have := congrArg norm h
    rw [norm_mul, norm_star, norm_one] at this
    nlinarith [this]
  nlinarith [norm_nonneg W.det, h2]
end Formalism.FourierDecayAlt.P.G9
