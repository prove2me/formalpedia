-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.ee_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:08:29.338581+00:00
-- url     : https://prove2.me/submissions/20347285-95c1-4568-92f9-bdff87fd9bd2

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
variable {L : LevelData A r} {f : FrameData S A}
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution {B : Type*} [Ring B] {g gi k ki x xi L0 e D w : B} (hg : gi * g = 1) (hk : ki * k = 1)
    (hx : xi * x = 1) (xk : x * k = k * x) (eg : e * g = g * e) (kg : k * g = g * k) (xL : x * L0 = L0 * x)
    (gL : g * L0 - L0 * g = g * w) (wx : w * x = x * w)
    (hY : g * x * (L0 + k * e) - (L0 + k * e) * (g * x) = -(g * x * (-w + k * D))) :
    xi * e * x - D = e := by
  have T : g * k * (x * e - e * x + x * D) =
      (g * x * (L0 + k * e) - (L0 + k * e) * (g * x) + g * x * (-w + k * D)) - g * (x * k - k * x) * e
        - g * (x * k - k * x) * D + k * (e * g - g * e) * x + (k * g - g * k) * e * x
        - g * (x * L0 - L0 * x) - (g * L0 - L0 * g - g * w) * x - g * (w * x - x * w) := by
    noncomm_ring
  rw [hY, xk, eg, kg, xL, gL, wx] at T
  simp only [sub_self, mul_zero, zero_mul, add_zero, neg_add_cancel] at T
  have T2 : x * e - e * x + x * D = 0 := by
    calc x * e - e * x + x * D = ki * (gi * (g * k * (x * e - e * x + x * D))) := by
          rw [mul_assoc g, ← mul_assoc gi, hg, one_mul, ← mul_assoc ki, hk, one_mul]
      _ = 0 := by rw [T, mul_zero, mul_zero]
  have T3 := congrArg (fun z => xi * z) T2
  simp only [mul_add, mul_sub, mul_zero, ← mul_assoc, hx, one_mul] at T3
  rw [sub_eq_iff_eq_add, ← sub_eq_zero, ← neg_eq_zero, ← T3]
  abel
end Formalism.FourierDecayAlt.P.Fr9
