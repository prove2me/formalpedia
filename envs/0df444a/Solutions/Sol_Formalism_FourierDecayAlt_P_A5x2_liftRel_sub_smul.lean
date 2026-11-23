-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.liftRel_sub_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:32.46746+00:00
-- url     : https://prove2.me/submissions/58914533-47b9-4089-8d50-4bf3dd368a64

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
    {v v' m m' : Fin n → R} (hv : LiftRel R k Z Z' φ v v') (hm : LiftRel R k Z Z' φ m m') (r : R) :
    LiftRel R k Z Z' φ (v - r • m) (v' - r • m') :=
  ⟨by rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, map_sub, map_smul, hv.1, hm.1,
      Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul],
    fun j hj => by rw [map_sub, map_smul, map_sub, map_smul, hv.2 j hj, hm.2 j hj]⟩
end Formalism.FourierDecayAlt.P.A5x2
