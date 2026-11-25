-- Prove2me | solution 1 for Formalism.L2.Th1.A.two_curves_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:14.514409+00:00
-- url     : https://prove2.me/submissions/50ea629d-cab2-4769-a8a1-e487ebd6adc8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_NormLeOneOfMonicTwo
import Theorems.Thm_Formalism_L2_Th1_A_Q2_coeff_odd_eq_zero
import Theorems.Thm_Formalism_L2_Th1_A_Q2_nadd
import Theorems.Thm_Formalism_L2_Th1_A_Q2_nneg
import Theorems.Thm_Formalism_L2_Th1_A_Q2_nsub
import Theorems.Thm_Formalism_L2_Th1_A_Q2_nmul
import Theorems.Thm_Formalism_L2_Th1_A_Q2_npow
import Theorems.Thm_Formalism_L2_Th1_A_Q2_ntwo
import Theorems.Thm_Formalism_L2_Th1_A_Q2_nthree
import Theorems.Thm_Formalism_L2_Th1_A_Q2_norm_le_one_of_monic_two
import Theorems.Thm_Formalism_L2_Th1_A_twoTorsionZ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Q2
namespace Formalism.L2.Th1.A
theorem _root_.solution : BridgeTwoMore := by
  intro K _ _ _ W xT yT hE h2
  obtain ⟨hroot, -, hkap, -, -, -, heven, -⟩ := twoTorsionZ K W xT yT hE h2
  refine ⟨hroot, fun n hn => coeff_odd_eq_zero heven hn, ?_⟩
  rintro ⟨h1, h2', h3, h4, h6⟩ hx
  have hy : ‖yT‖ ≤ 1 := by
    rw [WeierstrassCurve.Affine.equation_iff] at hE
    refine norm_le_one_of_monic_two (b := W.a₁ * xT + W.a₃)
      (c := xT ^ 3 + W.a₂ * xT ^ 2 + W.a₄ * xT + W.a₆) (nadd (nmul h1 hx) h3)
      (nadd (nadd (nadd (npow hx 3) (nmul h2' (npow hx 2))) (nmul h4 hx)) h6) ?_
    linear_combination hE
  refine ⟨hy, ?_, ?_⟩
  · have : W.b₂ / 12 - (xT + W.b₂ / 12) = -xT := by ring
    rw [this]; exact nneg hx
  · rw [hkap]
    exact nsub (nadd (nadd (nmul nthree (npow hx 2)) (nmul (nmul ntwo h2') hx)) h4) (nmul h1 hy)
end Formalism.L2.Th1.A
