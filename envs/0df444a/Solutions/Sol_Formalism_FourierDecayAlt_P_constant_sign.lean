-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.constant_sign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:35:34.944821+00:00
-- url     : https://prove2.me/submissions/7dc98d93-e485-45a3-b829-3ec95a566fba

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivedCoefficientIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
private theorem le_constSign_proof : Formalism.FourierDecayAlt.LE.ConstSign := by
  intro n lam α β h
  classical
  by_cases hab : α ≤ β
  · refine ⟨∏ s, (if -lam s < α then (1:ℝ) else -1), ?_, ?_⟩
    · refine Finset.prod_induction _ (fun x : ℝ => x = 1 ∨ x = -1) ?_ ?_ ?_
      · rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
      · left; rfl
      · intro s _
        split_ifs <;> simp
    · intro Y hY
      rw [Finset.abs_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun s _ => ?_)
      have hs := h s
      split_ifs with hlt
      · rw [abs_of_pos (by linarith [hY.1])]
        ring
      · have hb : β < -lam s := by
          by_contra hc
          push_neg at hc
          exact hs ⟨not_lt.mp hlt, hc⟩
        rw [abs_of_neg (by linarith [hY.2])]
        ring
  · exact ⟨1, Or.inl rfl, fun Y hY => absurd (le_trans hY.1 hY.2) hab⟩
end Formalism.FourierDecayAlt.P.LEx2
end

set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.LE.ConstSign := Formalism.FourierDecayAlt.P.LEx2.le_constSign_proof
end Formalism.FourierDecayAlt.P
