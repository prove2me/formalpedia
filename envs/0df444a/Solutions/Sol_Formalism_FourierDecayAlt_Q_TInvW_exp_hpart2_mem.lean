-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.exp_hpart2_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:59:52.348576+00:00
-- url     : https://prove2.me/submissions/dbd92cc2-b7fc-4292-b3c6-a24c43971af5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceCongruence
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_hpart2_skew
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_exp_mem_glev
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_hpart_cols

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1))
      ∈ Glev k r i := exp_mem_glev i _ (hpart2_skew _) (hpart_cols i p q).2 t
end Formalism.FourierDecayAlt.Q.TInvW
