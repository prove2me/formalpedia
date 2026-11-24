-- Prove2me | solution 1 for Formalism.IndefR.Leaf.Proofs.piStatement_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:59.381616+00:00
-- url     : https://prove2.me/submissions/1b4c52a6-afd6-4991-9f19-a4bc6fdf1395

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
theorem _root_.solution : HaarRightInvPi := by
  intro ι _ G _ _ _ _ _ _ _ _ h μ hμ
  have : ∀ i, (Measure.haar : Measure (G i)).IsMulRightInvariant := fun i => h i _ inferInstance
  rw [Measure.isMulLeftInvariant_eq_smul μ (Measure.pi fun i => (Measure.haar : Measure (G i)))]
  infer_instance
end Formalism.IndefR.Leaf.Proofs
