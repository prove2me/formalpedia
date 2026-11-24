-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.skew_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:59:52.865644+00:00
-- url     : https://prove2.me/submissions/d11a6fef-4a2c-46ec-8144-9a46b7c25fdb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hsq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.EabGlW
theorem _root_.solution {X : Mx k r} (h : Skew X) : Xᴴ = Hpk k r * (-X) * Hpk k r := by
  have h' : Xᴴ * Hpk k r + Hpk k r * X = 0 := h
  have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left h'
  calc Xᴴ = Xᴴ * Hpk k r * Hpk k r := by rw [Matrix.mul_assoc, hsq, Matrix.mul_one]
    _ = -(Hpk k r * X) * Hpk k r := by rw [h1]
    _ = Hpk k r * (-X) * Hpk k r := by rw [Matrix.mul_neg, Matrix.neg_mul]
end Formalism.FourierDecayAlt.Q.EabGlW
