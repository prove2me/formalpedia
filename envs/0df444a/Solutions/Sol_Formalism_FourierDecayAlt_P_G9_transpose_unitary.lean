-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.transpose_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:28.507891+00:00
-- url     : https://prove2.me/submissions/42354f93-5682-4b29-bff1-92bfa7ce5d1a

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
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) : Wᵀ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h : star W * W = 1 := Matrix.mem_unitaryGroup_iff'.1 hW
  have h2 := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_one] at h2
  rw [← h2]
  rfl
end Formalism.FourierDecayAlt.P.G9
