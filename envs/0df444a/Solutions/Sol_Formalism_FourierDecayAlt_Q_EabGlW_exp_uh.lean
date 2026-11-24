-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.exp_uh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:48:00.626209+00:00
-- url     : https://prove2.me/submissions/f7016c82-fc23-4c95-8a4d-8c65f89e9357

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hsq
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hinv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_skew_conj

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
theorem _root_.solution {X : Mx k r} (h : Skew X) : NormedSpace.exp X ∈ UH (Hpk k r) := by
  have hU : IsUnit (Hpk k r) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse hsq)
  have hc := Matrix.exp_conj (Hpk k r) (-X) hU
  rw [hinv] at hc
  show (NormedSpace.exp X)ᴴ * Hpk k r * NormedSpace.exp X = Hpk k r
  rw [← Matrix.exp_conjTranspose, skew_conj h, hc,
    Matrix.mul_assoc (Hpk k r * NormedSpace.exp (-X)) (Hpk k r) (Hpk k r), hsq, Matrix.mul_one,
    Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)),
    neg_add_cancel, NormedSpace.exp_zero, Matrix.mul_one]
end Formalism.FourierDecayAlt.Q.EabGlW
