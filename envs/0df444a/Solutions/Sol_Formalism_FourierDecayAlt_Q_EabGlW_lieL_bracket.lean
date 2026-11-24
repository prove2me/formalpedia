-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.lieL_bracket
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:47:58.137571+00:00
-- url     : https://prove2.me/submissions/da2e5ba9-9273-403f-a629-1f73512fd3e9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hsq
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_EabGlW_hsq__e5d4b9ac7468
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
theorem _root_.solution {i : Fin (r + 1)} {X Y : Mx k r} (hX : X ∈ LieL k r i) (hY : Y ∈ LieL k r i) :
    X * Y - Y * X ∈ LieL k r i := by
  have cX := skew_conj hX.1
  have cY := skew_conj hY.1
  refine ⟨?_, fun a ha => ?_⟩
  · show (X * Y - Y * X)ᴴ * Hpk k r + Hpk k r * (X * Y - Y * X) = 0
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, cX, cY]
    simp only [Matrix.mul_assoc, hsq', hsq, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
      Matrix.sub_mul, Matrix.mul_sub]
    all_goals abel
  · obtain ⟨x1, x2⟩ := hX.2 a ha
    obtain ⟨y1, y2⟩ := hY.2 a ha
    exact ⟨by rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, y1, x1,
        Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero],
      by rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, y2, x2,
        Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero]⟩
end Formalism.FourierDecayAlt.Q.EabGlW
