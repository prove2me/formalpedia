-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.hpart1_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:11:20.519489+00:00
-- url     : https://prove2.me/submissions/9d774968-b17d-42a0-85d4-044170c24536

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceCongruence
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_conj_part

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
theorem _root_.solution {s : Mx k r} (hs : s ∈ UH (Hpk k r)) (Z : Mx k r) :
    hpart1 (Hpk k r) (s⁻¹ * Z * s) = s⁻¹ * hpart1 (Hpk k r) Z * s := by
  unfold hpart1
  rw [conj_part hs Z]
  simp only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_assoc]
end Formalism.FourierDecayAlt.Q.TInvW
