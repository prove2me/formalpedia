-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.hpart_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:47:49.884638+00:00
-- url     : https://prove2.me/submissions/597374a2-1649-4768-830a-61c29f4a60d3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hsq
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_EabGlW_hsq__e5d4b9ac7468
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
theorem _root_.solution {P Q : Mx k r} (hP : Skew P) (hQ : Skew Q) :
    hpart1 (Hpk k r) (P + Complex.I • Q) = P ∧ hpart2 (Hpk k r) (P + Complex.I • Q) = Q := by
  have hWP : Hpk k r * Pᴴ * Hpk k r = -P := by
    rw [skew_conj hP]
    simp only [Matrix.mul_assoc, hsq', hsq, Matrix.mul_one]
  have hWQ : Hpk k r * Qᴴ * Hpk k r = -Q := by
    rw [skew_conj hQ]
    simp only [Matrix.mul_assoc, hsq', hsq, Matrix.mul_one]
  have hW : Hpk k r * (P + Complex.I • Q)ᴴ * Hpk k r = -P + Complex.I • Q := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, hWP, hWQ, Complex.star_def, Complex.conj_I, neg_smul,
      smul_neg, neg_neg]
  have hI : (1 / (2 * Complex.I)) * (2 * Complex.I) = 1 := by
    have := Complex.I_ne_zero
    field_simp
  unfold hpart1 hpart2
  rw [hinv, hW]
  constructor
  · rw [show P + Complex.I • Q - (-P + Complex.I • Q) = (2 : ℂ) • P by module, smul_smul]
    norm_num
  · rw [show P + Complex.I • Q + (-P + Complex.I • Q) = (2 * Complex.I) • Q by module, smul_smul, hI,
      one_smul]
end Formalism.FourierDecayAlt.Q.EabGlW
