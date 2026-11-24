-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_lo_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:52:12.43643+00:00
-- url     : https://prove2.me/submissions/ae15e864-7e1b-4bf4-aa10-d1e17d1446e0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution (Q : M.Par) (c : ℝ) (i : ℕ) (hu : ∃ n : ℤ, Q.u (i + 1) - c = n)
    (hu' : ∃ n : ℤ, Q.u' (i + 1) - c = n) : ∃ n : ℤ, Q.lo i - (c + 1 / 2) = n := by
  unfold M.Par.lo
  rcases max_choice (Q.u (i + 1)) (Q.u' (i + 1)) with h | h <;> rw [h]
  · obtain ⟨n, hn⟩ := hu
    exact ⟨n, by linarith⟩
  · obtain ⟨n, hn⟩ := hu'
    exact ⟨n, by linarith⟩
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
