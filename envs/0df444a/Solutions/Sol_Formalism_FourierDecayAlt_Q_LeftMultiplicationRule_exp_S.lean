-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.exp_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:15:38.864189+00:00
-- url     : https://prove2.me/submissions/0a5b8ad3-eac4-4ac3-ba91-aaf0e0dcc471

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_cube_S

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
theorem _root_.solution {l : Fin r} {Y : Mx k r} (hY : InS k r l Y) :
    NormedSpace.exp Y = 1 + Y + (1 / 2 : ℂ) • (Y * Y) := by
  have h3 : ∀ n, 3 ≤ n → Y ^ n = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add, pow_three', cube_S hY, zero_mul]
  have hz : ∀ n ∉ Finset.range 3, ((n.factorial : ℂ))⁻¹ • Y ^ n = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [h3 n hn, smul_zero]
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  dsimp only
  rw [tsum_eq_sum hz]
  simp [Finset.sum_range_succ, Nat.factorial, sq, one_div]
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
