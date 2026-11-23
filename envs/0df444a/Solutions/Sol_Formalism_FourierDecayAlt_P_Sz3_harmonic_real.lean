-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz3.harmonic_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:38.840024+00:00
-- url     : https://prove2.me/submissions/2f13cf4e-cac9-44c1-b635-77fe5d2300de

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz3
theorem _root_.solution (n : ℕ) : ((harmonic n : ℚ) : ℝ) = ∑ d ∈ Icc 1 n, 1 / (d : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp
end Formalism.FourierDecayAlt.P.Sz3
