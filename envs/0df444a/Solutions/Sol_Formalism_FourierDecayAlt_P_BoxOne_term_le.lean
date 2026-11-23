-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxOne.term_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:14.868996+00:00
-- url     : https://prove2.me/submissions/129aeac3-c283-463e-a608-7fc67ba0d537

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BoxOne
import Theorems.Thm_Formalism_SA_P_min_one_inv_le
import Theorems.Thm_Formalism_SA_P_min_one_rpow
import Theorems.Thm_Formalism_SA_P_pow_rpow_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxOne
open NumberField Finset
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.FourierDecayAlt.P.BoxOne
theorem _root_.solution (x : InfinitePlace E → ℝ) (hx : ∀ w, 0 < x w) (Kx : ℝ) (hK : 0 ≤ Kx) (l : E)
    (hl0 : l ≠ 0) :
    ∏ w, min 1 ((x w / w l) ^ Kx) ≤ ∏ w, ((1 / 2 : ℝ) ^ Kx) ^ (Nat.log 2 ⌊w l / x w⌋₊) := by
  apply Finset.prod_le_prod (fun w _ => le_min zero_le_one
    (Real.rpow_nonneg (div_nonneg (hx w).le (by positivity)) _))
  intro w _
  have hpos : 0 < x w / w l := div_pos (hx w) (InfinitePlace.pos_iff.2 hl0)
  rw [Formalism.SA.P.min_one_rpow _ _ hpos hK, ← Formalism.SA.P.pow_rpow_comm (1 / 2 : ℝ) Kx (by norm_num)]
  apply Real.rpow_le_rpow (le_min zero_le_one hpos.le) _ hK
  have hu : 0 < w l / x w := div_pos (InfinitePlace.pos_iff.2 hl0) (hx w)
  have := Formalism.SA.P.min_one_inv_le (w l / x w) hu
  rwa [one_div_div] at this
end Formalism.FourierDecayAlt.P.BoxOne
