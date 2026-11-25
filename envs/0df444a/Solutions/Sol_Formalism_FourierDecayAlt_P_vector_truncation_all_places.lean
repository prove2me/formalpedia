-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.vector_truncation_all_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:53:58.166622+00:00
-- url     : https://prove2.me/submissions/ca97993f-e632-4d8e-94ea-e244aeaeff6d

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_orbJ_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Gf_sgs
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Gf_of_Zhat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : TBB.VecCutAll := by
  intro Wp Wq _ _ _ _ _ _ P p χ F hχ ε hε γ hγ hG
  unfold KB.Pl.V D.vecV
  split_ifs with h h'
  · apply Formalism.FourierDecayAlt.P.TBBx2.orbJ_congr
    filter_upwards [Formalism.FourierDecayAlt.P.TBBx2.ae_inSS p.T.base] with q hq
    have hχ1 : χ (Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' (B.sgs q h'.choose) / ε) = 1 := by
      apply hχ.2.2
      rw [Formalism.FourierDecayAlt.P.TBBx2.Gf_sgs p.T.base q hq h'.choose,
        Formalism.FourierDecayAlt.P.TBBx2.Gf_of_Zhat _ _ _ γ h'.choose_spec.2.1, le_div_iff₀ hε, one_mul]
      exact hG
    simp only [D.orbIntegrand, B.rho, D.cutF, hχ1, Complex.ofReal_one, one_smul]
  all_goals rfl
end Formalism.FourierDecayAlt.P
