-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.exchange_relation_minus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:06.084473+00:00
-- url     : https://prove2.me/submissions/d435e0db-9873-4ee1-bae1-90470df4a6b3

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_rtt_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_minus_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.ExchMinus := by
  unfold Formalism.FourierDecayAlt.Wd.ExchMinus
  intro K A S _ _ _ _ _ _ _ _ Ω RR TT q b Y Yb hmod hfree hY hYb
  obtain ⟨_, _, hrtt, _, _⟩ := hmod
  have hr : RTTat TT Y Yb := hrtt Y hY Yb hYb
  have hc := Wd3.minus_core b (TT Y) (TT Yb) (Yb - Y) (hfree Y) (hfree Yb)
    (Wd3.rtt_entry (TT Yb) (TT Y) (Yb - Y) hr)
  simp only [Rht0, Matrix.mul_smul, Matrix.smul_mul, hc]
end Formalism.FourierDecayAlt.P
