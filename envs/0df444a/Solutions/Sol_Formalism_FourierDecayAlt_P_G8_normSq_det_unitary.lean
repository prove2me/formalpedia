-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G8.normSq_det_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:38.122179+00:00
-- url     : https://prove2.me/submissions/fb90ba3a-e491-4a7e-9b6d-c9d8a6f0625f

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
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) : Complex.normSq W.det = 1 := by
  have h1 := (Unitary.mem_iff.1 (Matrix.det_of_mem_unitary hW)).1
  have h2 : ((Complex.normSq W.det : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]; exact h1
  exact_mod_cast h2
end Formalism.FourierDecayAlt.P.G8
