-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.liftMatrix_mul_transpose_of_central
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:07:01.211804+00:00
-- url     : https://prove2.me/submissions/642cda8d-fd72-4278-b270-cbb36d90042e

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_cen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution {N : M2 A} (hN : Cen N) (M : M2 (SlopeTestRemainingChoices S A)) :
    (lift0 N * M)ᵀ = Mᵀ * lift0 Nᵀ := by
  ext1 i j
  rw [Matrix.transpose_apply, Matrix.mul_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => (io_cen (hN j k) (M k i)).eq
end Formalism.FourierDecayAlt.P.Wd11
