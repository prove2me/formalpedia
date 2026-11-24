-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr3.zetaConj2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:08:40.932542+00:00
-- url     : https://prove2.me/submissions/0b8e7f35-5a9b-4b33-b814-0b76f414c766

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr3
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)
namespace Formalism.FourierDecayAlt.P.Fr3
theorem _root_.solution : L.ζb * L.GGi - L.ζi = L.TT • (L.ζi * L.GGi) := by
  obtain ⟨p, pb, c, ci, cb, cbi, ζ, ζi, ζb, ζbi, GG, GGi, nab, nabs, TT, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11, h12⟩ := L
  dsimp only
  subst h12
  have e : ζi * (ζ * ζb - algebraMap ℂ A TT) = ζb - TT • ζi := by
    rw [mul_sub, ← mul_assoc, h7, one_mul, Algebra.smul_def, Algebra.commutes]
  calc ζb * GGi - ζi = ζb * GGi - ζi * ((ζ * ζb - algebraMap ℂ A TT) * GGi) := by
        rw [h10, mul_one]
    _ = ζb * GGi - (ζb - TT • ζi) * GGi := by rw [← mul_assoc, e]
    _ = TT • (ζi * GGi) := by
        rw [sub_mul, smul_mul_assoc]
        abel
end Formalism.FourierDecayAlt.P.Fr3
