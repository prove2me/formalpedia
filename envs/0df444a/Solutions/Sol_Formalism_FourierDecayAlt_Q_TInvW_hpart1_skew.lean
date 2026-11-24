-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.hpart1_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:56:36.197564+00:00
-- url     : https://prove2.me/submissions/626a8449-d43e-496a-b963-8475a2ec4f2c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceCongruence
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_hpk_inv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_hpk_hh
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq


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
theorem _root_.solution (Z : Mx k r) :
    (hpart1 (Hpk k r) Z)ᴴ = -(Hpk k r * hpart1 (Hpk k r) Z * Hpk k r) := by
  unfold hpart1
  rw [hpk_inv]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm, hs,
    mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_assoc, hpk_hh, Hpk_sq, mul_one]
  rw [← smul_neg, neg_sub]
end Formalism.FourierDecayAlt.Q.TInvW
