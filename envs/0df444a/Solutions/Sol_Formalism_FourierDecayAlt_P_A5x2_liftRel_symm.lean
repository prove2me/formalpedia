-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.liftRel_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:23.545147+00:00
-- url     : https://prove2.me/submissions/5f67c923-3f25-45a4-8525-c314f342327f

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
    {v v' : Fin n → R} (h : LiftRel R k Z Z' φ v v') : LiftRel R k Z' Z φ.symm v' v :=
  ⟨by rw [← h.1, φ.symm_apply_apply], fun j hj => (h.2 j hj).symm⟩
end Formalism.FourierDecayAlt.P.A5x2
