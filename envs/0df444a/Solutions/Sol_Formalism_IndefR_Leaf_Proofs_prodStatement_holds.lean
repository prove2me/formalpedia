-- Prove2me | solution 1 for Formalism.IndefR.Leaf.Proofs.prodStatement_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:59.256194+00:00
-- url     : https://prove2.me/submissions/9d35f868-f67b-4243-ac8c-a6845a16e3a9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_Unimod
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_UnimodP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Leaf Formalism.IndefR.Leaf.Proofs
open Formalism.IndefR.Leaf MeasureTheory
namespace Formalism.IndefR.Leaf.Proofs
theorem _root_.solution : HaarRightInvProd := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ μ hμ
  have : (Measure.haar : Measure G₁).IsMulRightInvariant := h₁ _ inferInstance
  have : (Measure.haar : Measure G₂).IsMulRightInvariant := h₂ _ inferInstance
  rw [Measure.isMulLeftInvariant_eq_smul μ ((Measure.haar : Measure G₁).prod (Measure.haar : Measure G₂))]
  infer_instance
end Formalism.IndefR.Leaf.Proofs
