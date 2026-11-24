-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.exchange_relation_plus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:06.540802+00:00
-- url     : https://prove2.me/submissions/c995a5de-ed98-40ec-8258-06075b1eec4b

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_rtt_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_plus_core

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
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.ExchPlus := by
  unfold Formalism.FourierDecayAlt.Wd.ExchPlus
  intro K A S _ _ _ _ _ _ _ _ Ω RR TT q a Y Ya hmod hfree hY hYa
  obtain ⟨_, _, hrtt, _, _⟩ := hmod
  have hr : RTTat TT Ya Y := hrtt Ya hYa Y hY
  have hc := Wd3.plus_core a (TT Y) (TT Ya) (Y - Ya) (hfree Y) (hfree Ya)
    (Wd3.rtt_entry (TT Y) (TT Ya) (Y - Ya) hr)
  rw [Rh0, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, hc]
end Formalism.FourierDecayAlt.P
