-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.cls_double
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:27.034837+00:00
-- url     : https://prove2.me/submissions/9cc9ef0b-8e56-41af-8be0-4b571aa3c29d

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_mem_cls

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
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution {G : Type} [Group G] (K₀ : Subgroup G)
    (q : Quotient (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G))) :
    cls (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G)) q =
      DoubleCoset.doubleCoset (Quotient.out q) (K₀ : Set G) K₀ := by
  ext y
  rw [mem_cls]
  exact (DoubleCoset.mem_quotToDoubleCoset_iff (H := K₀) (K := K₀) q y).symm
end Formalism.DoubleCosetMeasures.P
