-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.simpleAdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:22.09994+00:00
-- url     : https://prove2.me/submissions/55b46754-7ef7-4df4-a815-b55cebea0647

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_low_simple_entry
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_up_simple_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution : Formalism.DoubleCosetMeasures.SimpleAdd := by
  intro K _ n x y
  constructor
  · intro hx hy
    unfold sLow
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j.val + 1 < n
    · simp only [dif_pos h]; exact low_simple_entry hx hy j h
    · simp [dif_neg h]
  · intro hx hy
    unfold sUp
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j.val + 1 < n
    · simp only [dif_pos h]; exact up_simple_entry hx hy j h
    · simp [dif_neg h]
end Formalism.DoubleCosetMeasures.P
