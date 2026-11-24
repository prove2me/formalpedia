-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.commutator_GG_l0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:25:22.231437+00:00
-- url     : https://prove2.me/submissions/53cf6db2-07fe-49a1-8671-0adf075e88eb

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_zc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_b_c2aaaddc0865
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_mGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_l0_eq_neg_nabla_sub

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
variable (L : LevelData A r)
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution (Y : ℂ) : L.GG * L.l0 Y - L.l0 Y * L.GG = L.ζb := by
  rw [l0_eq_neg_nabla_sub]
  have e : L.GG * (L.ζb * L.GGi) = L.ζb * L.GGi * L.GG := by
    rw [mul_assoc, L.GGi_GG, zc L (mζb L) (mGi L), ← mul_assoc, L.GG_GGi, one_mul, mul_one]
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, e, mul_neg, neg_mul, L.nab_GG]
  abel
end Formalism.FourierDecayAlt.P.Fr9
