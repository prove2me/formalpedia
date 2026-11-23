-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.inTTeq_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:23.278396+00:00
-- url     : https://prove2.me/submissions/20d7a9e2-610c-4f85-a68d-17bcbe0b78fc

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
variable {R}
namespace Formalism.FourierDecayAlt.P.A5x2
theorem _root_.solution {k : ℕ} {Z Z' : Matrix (Fin n) (Fin n) K} {φ : coker R Z ≃ₗ[R] coker R Z'}
    (h : InTTeq R k Z Z' φ) : InTTeq R k Z' Z φ.symm := by
  intro j hk hj v' v hv
  exact (h j hk hj v v' (by rw [← hv, φ.apply_symm_apply])).symm
end Formalism.FourierDecayAlt.P.A5x2
