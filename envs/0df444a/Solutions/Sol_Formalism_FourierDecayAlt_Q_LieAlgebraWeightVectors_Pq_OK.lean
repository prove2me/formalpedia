-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.Pq_OK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:51:09.979345+00:00
-- url     : https://prove2.me/submissions/430273b3-1e12-4e06-abe1-08fc34af8a22

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
theorem _root_.solution {P : M.Par} (hP : P.OK) : (Pq P).OK := by
  refine ⟨hP.k_pos, hP.T_pos, hP.T'_pos, ?_, ?_, ?_⟩
  · exact hP.int_u
  · exact hP.int_u
  · intro i hi
    have g := hP.gap i hi
    show max (P.u (i + 1)) (P.u (i + 1)) + 1 / 2 ≤ min (P.u i) (P.u i) - 1 / 2
    have e1 : P.lo i = max (P.u (i + 1)) (P.u' (i + 1)) + 1 / 2 := rfl
    have e2 : P.hi i = min (P.u i) (P.u' i) - 1 / 2 := rfl
    rw [max_self, min_self]
    have := le_max_left (P.u (i + 1)) (P.u' (i + 1))
    have := min_le_left (P.u i) (P.u' i)
    linarith
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
