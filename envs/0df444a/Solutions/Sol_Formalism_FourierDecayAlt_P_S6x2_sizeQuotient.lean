-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.sizeQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:12.8965+00:00
-- url     : https://prove2.me/submissions/02a50394-a2a4-438b-b3ab-3a789616f7c8

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_rd_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x2
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x2
theorem _root_.solution (hL : LeastNorm) (hD : Formalism.FourierDecayAlt.DualSizeIdentity) (hdeg : DegreeFacts) :
    SizeQuotient := by
  intro E _ _ _ g r i c hg hc l hl hl0
  have h := hL E g (nuBlock r i 1) 1 hg l hl hl0
  have hrd : 0 < rd E := rd_pos E
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hid := hD (InfinitePlace E) c g (rd E) r i hgR hrd
  rw [(hdeg E).2.1] at hid
  rw [← hid]
  have e : nuBlock (r : ℤ) (i : ℤ) 1 + 1 = (2 * r : ℤ) + 3 - 2 * i := by unfold nuBlock; ring
  rw [e] at h
  have hpos : 0 < ((g : ℝ) * rd E ^ ((2 * r : ℤ) + 3 - 2 * i)) ^ (-(deg E : ℤ)) := by positivity
  apply div_le_div_of_nonneg_left _ hpos h
  exact Finset.prod_nonneg fun v _ => mul_nonneg (hc v) (by positivity)
end Formalism.FourierDecayAlt.P.S6x2
