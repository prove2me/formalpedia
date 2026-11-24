-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.comm_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:06:50.08386+00:00
-- url     : https://prove2.me/submissions/f0fc2d28-eabf-4c56-bd88-833eba93f747

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution {B : Type*} [Ring B] {x xi y : B} (h1 : x * xi = 1) (h2 : xi * x = 1) (h : Commute x y) :
    Commute xi y := by
  show xi * y = y * xi
  calc xi * y = xi * (y * x) * xi := by rw [mul_assoc, mul_assoc, h1, mul_one]
    _ = y * xi := by rw [← h.eq, ← mul_assoc, h2, one_mul]
end Formalism.FourierDecayAlt.P.Fr9
