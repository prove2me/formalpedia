-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.exp_uh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:49:31.790861+00:00
-- url     : https://prove2.me/submissions/c2bcc35f-b941-4563-aae2-a55bebc72c77

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_ReflectionColumnDualIsotropic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_HasDerivAtPhase
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_hinv
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
theorem _root_.solution {Y : Mx k r} (hY : Hpk k r * Yᴴ * Hpk k r = -Y) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Y) ∈ UH (Hpk k r) := by
  have hH := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hU : IsUnit (Hpk k r) := ⟨⟨Hpk k r, Hpk k r, hH, hH⟩, rfl⟩
  have hY' : Yᴴ = Hpk k r * -Y * Hpk k r := by
    rw [← hY]
    simp only [← mul_assoc, hH, one_mul]
    rw [mul_assoc, hH, mul_one]
  have hYH : ((t : ℂ) • Y)ᴴ = Hpk k r * -((t : ℂ) • Y) * (Hpk k r)⁻¹ := by
    rw [hinv, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hY']
    simp only [smul_neg, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc]
  show (NormedSpace.exp ((t : ℂ) • Y))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • Y) = Hpk k r
  rw [← Matrix.exp_conjTranspose, hYH, Matrix.exp_conj _ _ hU, hinv]
  simp only [mul_assoc]
  rw [← mul_assoc (Hpk k r) (Hpk k r), hH, one_mul,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl ((t : ℂ) • Y))), neg_add_cancel,
    NormedSpace.exp_zero, mul_one]
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
