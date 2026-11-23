-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x6.orbZ_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:41.248786+00:00
-- url     : https://prove2.me/submissions/929ddcd7-f6c6-4037-b586-40013e406f56

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x6
namespace Formalism.FourierDecayAlt.P.A5x6
theorem _root_.solution {K : Type} [CommRing K] (w : Point K)
    (p : lowW K w.1 w.2 × upUniG K w.1.sum) : (orbZ w p).det = (pt w.1 w.2).det := by
  unfold orbZ
  rw [Matrix.det_mul, Matrix.det_mul, isLowUni_det K p.1.2.1, isUpUni_det K p.2.2, one_mul,
    mul_one]
end Formalism.FourierDecayAlt.P.A5x6
