-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.skew_hpart1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:48:03.909877+00:00
-- url     : https://prove2.me/submissions/390d3a1b-b650-418c-bd66-6ff9cb4354cc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hsq
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_EabGlW_hsq__e5d4b9ac7468
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hinv
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts


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
theorem _root_.solution (Z : Mx k r) : Skew (hpart1 (Hpk k r) Z) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by
    first | simp | (rw [Complex.star_def]; simp)
  show (hpart1 (Hpk k r) Z)ᴴ * Hpk k r + Hpk k r * hpart1 (Hpk k r) Z = 0
  simp only [hpart1, hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH, hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_assoc, hsq', hsq, Matrix.mul_one]
  all_goals module
end Formalism.FourierDecayAlt.Q.EabGlW
