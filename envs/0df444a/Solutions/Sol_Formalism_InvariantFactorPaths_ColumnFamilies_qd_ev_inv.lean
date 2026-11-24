-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:22:52.409066+00:00
-- url     : https://prove2.me/submissions/bb778fc3-6f2f-4821-b46a-d0b90b902db9

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_point
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (M : GLMod n) (la nu : Fin n → ℤ) (x : M.ι → ℚ) (hx : IsHighest M ℚ la x)
    {R' : Type} [CommRing R'] [Algebra ℚ R'] (g u : GL (Fin n) R') (hu1 : ∀ a, u.val a a = 1)
    (hu2 : ∀ a b, b < a → u.val a b = 0) (i : M.ι) :
    evGLR (R := ℚ) (g * u) (qb_ev M ℚ nu x i) = evGLR (R := ℚ) g (qb_ev M ℚ nu x i) := by
  rw [qd_ev_point, qd_ev_point, M.mul, ← Matrix.mulVec_mulVec, hx.2 R' u hu1 hu2]
end Formalism.InvariantFactorPaths.ColumnFamilies
