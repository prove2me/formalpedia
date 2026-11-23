-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.grp_sUp_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:15.831992+00:00
-- url     : https://prove2.me/submissions/8e93aee9-679f-455f-bf62-0b6e0939be81

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_DoubleCosetMeasures_Final_simpleAdd
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_simpleAdd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
noncomputable section
variable {K : Type} [CommRing K] (R : Subring K) (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution {N : ℕ} (a b : upUniG K N) :
    sUp (((a * b : upUniG K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      sUp ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) +
        sUp ((b : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
  rw [Subgroup.coe_mul, Units.val_mul]
  exact (Formalism.DoubleCosetMeasures.P.simpleAdd K N _ _).2 a.2 b.2
end Formalism.FourierDecayAlt.P.A5x9
