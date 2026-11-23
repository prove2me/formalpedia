-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.grp_sUp_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:15.256595+00:00
-- url     : https://prove2.me/submissions/520750b5-c66a-4623-b381-c2a375703871

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_grp_sUp_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_grp_sUp_one

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
    sUp (((a * b * a⁻¹ : upUniG K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      sUp ((b : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
  have h1 := grp_sUp_mul a a⁻¹
  rw [mul_inv_cancel, grp_sUp_one] at h1
  rw [grp_sUp_mul, grp_sUp_mul]
  linear_combination -h1
end Formalism.FourierDecayAlt.P.A5x9
