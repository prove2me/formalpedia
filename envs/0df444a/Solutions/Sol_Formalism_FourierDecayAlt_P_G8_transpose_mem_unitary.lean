-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G8.transpose_mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:08.968831+00:00
-- url     : https://prove2.me/submissions/0e7c4a9b-7ebb-4ad4-b801-074bb204af87

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G8
namespace Formalism.FourierDecayAlt.P.G8
theorem _root_.solution (d : ℕ) (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) : Wᵀ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h := Matrix.mem_unitaryGroup_iff'.1 hW
  have e : star Wᵀ = (star W)ᵀ := by
    ext i j; simp [Matrix.star_apply]
  rw [e, ← Matrix.transpose_mul, h, Matrix.transpose_one]
end Formalism.FourierDecayAlt.P.G8
