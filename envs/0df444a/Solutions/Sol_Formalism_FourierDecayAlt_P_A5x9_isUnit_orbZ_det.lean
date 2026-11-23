-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.isUnit_orbZ_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:16.121038+00:00
-- url     : https://prove2.me/submissions/26a7d735-fb1f-4e66-8be3-ed19ecc807b1

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_pt_mul_ptI


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
noncomputable section
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (w : Point K) (p : lowW K w.1 w.2 × upUniG K w.1.sum) :
    IsUnit (orbZ w p).det := by
  unfold orbZ
  rw [Matrix.det_mul, Matrix.det_mul, isLowUni_det K p.1.2.1, isUpUni_det K p.2.2, one_mul,
    mul_one]
  exact Matrix.isUnit_det_of_right_inverse (Formalism.DoubleCosetMeasures.P.Phase.pt_mul_ptI w.1 w.2)
end Formalism.FourierDecayAlt.P.A5x9
