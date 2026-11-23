-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.isOpen_cls_leftRel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:27.787168+00:00
-- url     : https://prove2.me/submissions/e0a1544d-44de-4874-840e-42fe38707d01

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_cls_leftRel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
variable {G : Type} [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution (K₀ : Subgroup G) (hK : IsOpen (K₀ : Set G)) (q : G ⧸ K₀) :
    IsOpen (cls (QuotientGroup.leftRel K₀) q) := by
  rw [cls_leftRel]; exact hK.preimage (continuous_const.mul continuous_id)
end Formalism.DoubleCosetMeasures.P
