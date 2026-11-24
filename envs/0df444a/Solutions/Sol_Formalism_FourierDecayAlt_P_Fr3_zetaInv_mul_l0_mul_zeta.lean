-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr3.zetaInv_mul_l0_mul_zeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:07:00.769997+00:00
-- url     : https://prove2.me/submissions/eccdb5c0-cfe4-42b1-9e1b-2c4e8ecbdd9d

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m__58fce9a2b273
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_l0_constant_part_commute

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
theorem _root_.solution (Y : ℂ) : L.ζi * L.l0 Y * L.ζ = L.l0 Y - L.ζi := by
  have c := l0_constant_part_commute L Y (mζ L)
  have h1 : L.ζi * (-L.nab) * L.ζ = -L.nab - L.ζi := by
    rw [mul_neg, neg_mul, mul_assoc, L.nab_ζ, mul_add, ← mul_assoc, L.ζi_ζ, one_mul, mul_one]; abel
  have h2 : L.ζi * (algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) * L.ζ =
      algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi) := by
    rw [mul_assoc, c.eq, ← mul_assoc, L.ζi_ζ, one_mul]
  unfold LevelData.l0
  rw [mul_sub, sub_mul, h1, h2]; abel
end Formalism.FourierDecayAlt.P.Fr3
