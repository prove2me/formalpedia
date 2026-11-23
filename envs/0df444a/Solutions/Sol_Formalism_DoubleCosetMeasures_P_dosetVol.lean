-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.dosetVol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:00.645379+00:00
-- url     : https://prove2.me/submissions/43fb67f9-df8d-4be0-8280-cfe9e61b79f5

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_doubleCoset_eq_preimage
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_card_range_dcMap
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_relIndex_conj_ne_zero
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_measure_preimage_mk

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
theorem _root_.solution : Formalism.DoubleCosetMeasures.DosetVol := by
  intro G _ _ _ _ _ μ _ K₀ hK hc g
  have hne := relIndex_conj_ne_zero K₀ hK hc g
  refine ⟨hne, ?_⟩
  have hfin : (Set.range (dcMap K₀ g)).Finite := by
    have : Finite (Set.range (dcMap K₀ g)) := Nat.finite_of_card_ne_zero (by
      rw [card_range_dcMap]; exact hne)
    exact Set.toFinite _
  rw [doubleCoset_eq_preimage, measure_preimage_mk μ K₀ hK _ hfin, card_range_dcMap]
end Formalism.DoubleCosetMeasures.P
