-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.decay.minFac_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:52:21.075063+00:00
-- url     : https://prove2.me/submissions/9e4bbd82-dbda-4ee5-89e2-3d283db9ac77

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_decay


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Finset Formalism.FourierDecayAlt
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.decay
open Formalism.FourierDecayAlt.TB
open scoped ComplexOrder
attribute [local instance] Classical.propDecidable
variable {E W : Type} [Field E] (D : Data E W)
namespace Formalism.FourierDecayAlt.P.JCx1.decay
theorem _root_.solution (x a : ℝ) (K : ℕ) (hx : 0 ≤ x) (ha : 0 < a) : PairingProductCorollary.minFac x a K = min 1 ((x / a) ^ K) := by
  unfold PairingProductCorollary.minFac
  split_ifs with h
  · rw [min_eq_right]
    exact pow_le_one₀ (div_nonneg hx ha.le) ((div_le_one ha).2 h.le)
  · rw [min_eq_left]
    exact one_le_pow₀ ((one_le_div ha).2 (not_lt.1 h))
end Formalism.FourierDecayAlt.P.JCx1.decay
