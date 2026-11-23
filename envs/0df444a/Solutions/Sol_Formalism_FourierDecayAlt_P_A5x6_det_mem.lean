-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x6.det_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:19.655506+00:00
-- url     : https://prove2.me/submissions/fb5bc05e-638e-4583-8e98-a3d345bd8165

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
theorem _root_.solution {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hM : IsInt R M) : M.det ∈ R := by
  rw [Matrix.det_apply]
  refine R.sum_mem fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  exact R.mul_mem (intCast_mem R _) (R.prod_mem fun i _ => hM _ _)
end Formalism.FourierDecayAlt.P.A5x6
