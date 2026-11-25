-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormSums.sum_mdim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:02:18.729131+00:00
-- url     : https://prove2.me/submissions/f659cb96-e871-4563-a6ea-808b387e84b3

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameCompletion
import Theorems.Thm_Formalism_FourierDecayAlt_P_AnisotropicColumnSums_mdim_last


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.HermitianFormSums
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HermitianFormSums
theorem _root_.solution {X : Type*} [AddCommMonoid X] (F : ℕ → X) :
    ∑ j : Fin (mdim k r (Fin.last r)), F j.val = ∑ a : Fin k, F a.val + F k := by
  rw [Fin.sum_univ_eq_sum_range, AnisotropicColumnSums.mdim_last, Finset.sum_range_succ, Fin.sum_univ_eq_sum_range]
end Formalism.FourierDecayAlt.P.HermitianFormSums
