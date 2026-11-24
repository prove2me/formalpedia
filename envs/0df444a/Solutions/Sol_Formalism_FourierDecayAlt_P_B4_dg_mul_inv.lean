-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.dg_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:28:53.61789+00:00
-- url     : https://prove2.me/submissions/7c689f64-a467-4458-a20c-261442060663

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution (k r : ℕ) (t : ℝ) (ht : t ≠ 0) (i : Fin (2 * r + k + 1)) :
    dg k r t i * dg k r t⁻¹ i = 1 := by
  unfold dg
  split_ifs with h1 h2
  · rw [← Complex.ofReal_mul, ← mul_pow, mul_inv_cancel₀ ht, one_pow, Complex.ofReal_one]
  · rw [one_mul]
  · rw [← Complex.ofReal_mul, inv_pow, inv_inv, inv_mul_cancel₀ (pow_ne_zero _ ht), Complex.ofReal_one]
end Formalism.FourierDecayAlt.P.B4
