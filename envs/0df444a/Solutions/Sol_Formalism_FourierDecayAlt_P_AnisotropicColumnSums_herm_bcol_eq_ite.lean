-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AnisotropicColumnSums.herm_bcol_eq_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:38:50.667271+00:00
-- url     : https://prove2.me/submissions/dd55ff57-9d2b-4732-9d59-5de29a6c5aed

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.AnisotropicColumnSums
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.AnisotropicColumnSums
theorem _root_.solution {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [x] Bs) (j : Fin (mdim k r (Fin.last r))) :
    herm (Hpk k r) (bcol k r x Bs j) x = if j.val < k then 0 else herm (Hpk k r) x x := by
  unfold bcol
  by_cases h : j.val < k
  · rw [dif_pos h, if_pos h]
    exact hB.2.2 _ x (List.mem_singleton_self x)
  · rw [dif_neg h, if_neg h]
end Formalism.FourierDecayAlt.P.AnisotropicColumnSums
