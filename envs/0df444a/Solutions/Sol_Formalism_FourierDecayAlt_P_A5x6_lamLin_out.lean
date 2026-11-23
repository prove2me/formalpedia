-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x6.lamLin_out
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:06:40.829356+00:00
-- url     : https://prove2.me/submissions/f34fab50-1be9-4cc3-bb3f-3f945838e8cd

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_muZ_mk

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
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x6
theorem _root_.solution {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) (hZ : IsUnit Z.det) (β : coker R Z) :
    lamLin R Z (Quotient.out β) = muZ R Z hZ β := by
  rw [← muZ_mk R Z hZ (Quotient.out β)]
  congr 1
  exact Quotient.out_eq β
end Formalism.FourierDecayAlt.P.A5x6
