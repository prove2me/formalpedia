-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.isD_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:31:11.695997+00:00
-- url     : https://prove2.me/submissions/8ee1fb98-b3bb-420a-9659-1ef2d0a9f0c1

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity

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
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution : IsD R k (1 : Matrix (Fin n) (Fin n) K) := by
  refine ⟨isUpUni_one K, fun a b => ?_, fun _ _ _ => rfl⟩
  rw [Matrix.one_apply]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem
end Formalism.FourierDecayAlt.P.A5x9
