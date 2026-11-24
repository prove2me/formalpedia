-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.tau_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:08:36.597165+00:00
-- url     : https://prove2.me/submissions/ad3c156a-a359-46d5-814d-d0b513c9b559

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
theorem _root_.solution {B : Type*} [Ring B] [Algebra ℂ B] {τb τbi τ t12b t12 m : B} {d : ℂ} (h1 : τbi * τb = 1)
    (hc : Commute τb τ) (hm : t12b = τb * m)
    (hR : d • (t12b * τ - τ * t12b) = τb * t12 - τ * t12b) : d • (m * τ - τ * m) = t12 - τ * m := by
  have e := congrArg (fun z => τbi * z) hR
  simp only [hm, mul_smul_comm, mul_sub] at e
  have a1 : τbi * (τb * m * τ) = m * τ := by rw [mul_assoc, ← mul_assoc, h1, one_mul]
  have a2 : τbi * (τ * (τb * m)) = τ * m := by
    rw [← mul_assoc τ, ← hc.eq, mul_assoc, ← mul_assoc, h1, one_mul]
  have a3 : τbi * (τb * t12) = t12 := by rw [← mul_assoc, h1, one_mul]
  rwa [a1, a2, a3] at e
end Formalism.FourierDecayAlt.P.Fr9
