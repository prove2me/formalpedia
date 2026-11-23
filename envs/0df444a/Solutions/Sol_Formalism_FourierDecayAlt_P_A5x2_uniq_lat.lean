-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.uniq_lat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:36.096718+00:00
-- url     : https://prove2.me/submissions/b363d278-1b5b-4dd6-a631-a129c414b2d0

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_liftRel_sub_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lift_lat

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
variable (R)
namespace Formalism.FourierDecayAlt.P.A5x2
theorem _root_.solution (Z Z' : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z.det) (hd' : IsUnit Z'.det)
    (φ : coker R Z ≃ₗ[R] coker R Z') (c : Fin n) (m m' v v' v'' : Fin n → R)
    (hm : LiftRel R c.val Z Z' φ m m') (h1 : LiftRel R c.val Z Z' φ v v')
    (h2 : LiftRel R c.val Z Z' φ v v'') :
    v' - v'' ∈ latZ R (Z' + vecMulVec (coeLin R m') (Pi.single c 1)) := by
  have h := liftRel_sub_smul h1 h2 1
  rw [one_smul, one_smul, sub_self] at h
  exact lift_lat R Z Z' hd hd' φ c m m' 0 _ hm h (Submodule.zero_mem _)
end Formalism.FourierDecayAlt.P.A5x2
